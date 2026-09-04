#!/usr/bin/env python3
"""Validate the KLS Lean Blueprint's offline dependency metadata.

The Blueprint sources remain ordinary LaTeX.  This checker covers the small
machine-readable boundary around them: labels and ``\\uses`` references, the
JSON subset stored in ``route-composition.yaml``, and the four declarations
that the Blueprint presents as Lean-certified.  It deliberately does not try
to parse mathematics or infer proof status from prose.
"""
from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
BLUEPRINT = ROOT / "formalization/blueprint"
ROUTES = BLUEPRINT / "route-composition.yaml"
LEDGER = ROOT / "research/a-series/ledger.yaml"

ALLOWED_ROUTE_TOP_LEVEL_FIELDS = {"version", "targets"}
ALLOWED_TARGET_FIELDS = {"target", "operator", "alternatives"}
ALLOWED_ALTERNATIVE_FIELDS = {"route", "operator", "nodes"}

EXPECTED_ROUTES: dict[str, tuple[str, ...]] = {
    "eldan-localization": (
        "ass:tight-prefix-carleson",
        "cor:tight-window-consumption",
    ),
    "moment-map-spectral": ("prop:spectral-sufficiency",),
    "moment-map-cmh": ("cor:cmh-recovery-sequence-suffices",),
    "conditional-fiber-frame": (
        "q:conditional-fiber-frame",
        "lem:conditional-fiber-form",
    ),
}

# Blueprint label -> (ledger node, public Lean certificate declaration).
CERTIFICATES: dict[str, tuple[str, str]] = {
    "cert:linear-test-lower": (
        "lem:linear-test-lower",
        "Solutions.LemLinearTestLower.certificate",
    ),
    "cert:binary-tensorization": (
        "lem:poincare-tensorization",
        "Solutions.LemPoincareTensorization.certificate",
    ),
    "cert:finite-tensorization": (
        "lem:poincare-finite-tensorization",
        "Solutions.LemPoincareFiniteTensorization.certificate",
    ),
    "cert:gaussian-one-dimensional": (
        "lem:poincare-gaussian-one-dimensional",
        "Solutions.LemPoincareGaussianOneDimensional.certificate",
    ),
}

LABEL = re.compile(r"\\label\s*\{([^{}]*)\}", re.DOTALL)
USES = re.compile(r"\\uses\s*\{([^{}]*)\}", re.DOTALL)
LEAN = re.compile(r"\\lean\s*\{([^{}]*)\}", re.DOTALL)
LEAN_OK = re.compile(r"\\leanok\b")
ENVIRONMENT = re.compile(
    r"\\begin\s*\{(?P<environment>[^{}\s]+)\}"
    r"(?P<body>.*?)"
    r"\\end\s*\{(?P=environment)\}",
    re.DOTALL,
)


@dataclass(frozen=True)
class SourceLocation:
    path: Path
    line: int


@dataclass(frozen=True)
class TeXBlock:
    path: Path
    environment: str
    body: str


@dataclass
class BlueprintIndex:
    labels: dict[str, SourceLocation]
    blocks: dict[str, TeXBlock]
    uses: list[tuple[str, SourceLocation]]
    file_count: int


def _strip_tex_comments(text: str) -> str:
    """Remove unescaped TeX comments while preserving line numbers."""
    lines: list[str] = []
    for line in text.splitlines(keepends=True):
        cut = len(line)
        for index, character in enumerate(line):
            if character != "%":
                continue
            backslashes = 0
            cursor = index - 1
            while cursor >= 0 and line[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            if backslashes % 2 == 0:
                cut = index
                break
        suffix = "\n" if line.endswith("\n") else ""
        lines.append(line[:cut].rstrip("\r\n") + suffix)
    return "".join(lines)


def _location(root: Path, path: Path, text: str, offset: int) -> SourceLocation:
    try:
        display_path = path.relative_to(root)
    except ValueError:
        display_path = path
    return SourceLocation(display_path, text.count("\n", 0, offset) + 1)


def _display(location: SourceLocation) -> str:
    return f"{location.path}:{location.line}"


def _split_command_list(
    value: str, *, command: str, location: SourceLocation, errors: list[str]
) -> list[str]:
    entries = [entry.strip() for entry in value.split(",")]
    if not entries or any(not entry for entry in entries):
        errors.append(f"{_display(location)}: \\{command} contains an empty entry")
        return [entry for entry in entries if entry]
    if len(entries) != len(set(entries)):
        errors.append(f"{_display(location)}: \\{command} contains duplicate entries")
    return entries


def _index_blueprint_tex(root: Path, chapters: Path, errors: list[str]) -> BlueprintIndex:
    if not chapters.is_dir():
        errors.append(f"Blueprint chapter directory does not exist: {chapters}")
        return BlueprintIndex({}, {}, [], 0)

    paths = sorted(chapters.rglob("*.tex"))
    if not paths:
        errors.append(f"Blueprint has no chapter TeX files under {chapters}")
        return BlueprintIndex({}, {}, [], 0)

    labels: dict[str, SourceLocation] = {}
    blocks: dict[str, TeXBlock] = {}
    uses: list[tuple[str, SourceLocation]] = []

    for path in paths:
        try:
            text = _strip_tex_comments(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError) as exc:
            errors.append(f"cannot read Blueprint TeX source {path}: {exc}")
            continue

        for match in LABEL.finditer(text):
            location = _location(root, path, text, match.start())
            label = match.group(1).strip()
            if not label:
                errors.append(f"{_display(location)}: \\label must not be empty")
                continue
            if label in labels:
                errors.append(
                    f"duplicate Blueprint label {label}: "
                    f"{_display(labels[label])} and {_display(location)}"
                )
            else:
                labels[label] = location

        for match in USES.finditer(text):
            location = _location(root, path, text, match.start())
            for dependency in _split_command_list(
                match.group(1), command="uses", location=location, errors=errors
            ):
                uses.append((dependency, location))

        for match in ENVIRONMENT.finditer(text):
            body = match.group("body")
            for label_match in LABEL.finditer(body):
                label = label_match.group(1).strip()
                if label and label not in blocks:
                    blocks[label] = TeXBlock(
                        path=path,
                        environment=match.group("environment"),
                        body=body,
                    )

    for dependency, location in uses:
        if dependency not in labels:
            errors.append(
                f"{_display(location)}: \\uses references unknown label {dependency}"
            )

    return BlueprintIndex(labels, blocks, uses, len(paths))


def _load_json_object(path: Path, description: str, errors: list[str]) -> dict[str, Any] | None:
    if not path.is_file():
        errors.append(f"{description} does not exist: {path}")
        return None
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        errors.append(f"cannot read {description} as JSON-compatible YAML: {exc}")
        return None
    if not isinstance(document, dict):
        errors.append(f"{description} top level must be an object")
        return None
    return document


def _unknown_fields(
    value: dict[str, Any], allowed: set[str], context: str, errors: list[str]
) -> None:
    for field in sorted(set(value) - allowed):
        errors.append(f"{context}: unknown field: {field}")


def _missing_fields(
    value: dict[str, Any], required: set[str], context: str, errors: list[str]
) -> None:
    for field in sorted(required - set(value)):
        errors.append(f"{context}: missing field: {field}")


def _validate_routes(
    path: Path, index: BlueprintIndex, errors: list[str]
) -> tuple[str | None, set[str], int]:
    document = _load_json_object(path, "Blueprint route composition", errors)
    if document is None:
        return None, set(), 0

    _unknown_fields(document, ALLOWED_ROUTE_TOP_LEVEL_FIELDS, "routes", errors)
    _missing_fields(document, ALLOWED_ROUTE_TOP_LEVEL_FIELDS, "routes", errors)
    if type(document.get("version")) is not int or document.get("version") != 1:
        errors.append("routes.version must be the integer 1")

    targets = document.get("targets")
    if not isinstance(targets, list) or len(targets) != 1:
        errors.append("routes.targets must be a single-element array")
        return None, set(), 0
    target = targets[0]
    if not isinstance(target, dict):
        errors.append("routes.targets[0] must be an object")
        return None, set(), 0

    context = "routes.targets[0]"
    _unknown_fields(target, ALLOWED_TARGET_FIELDS, context, errors)
    _missing_fields(target, ALLOWED_TARGET_FIELDS, context, errors)
    target_label = target.get("target")
    if target_label != "conj:kls":
        errors.append(f"{context}.target must be 'conj:kls'")
        target_label = None
    elif target_label not in index.labels:
        errors.append(f"{context}.target references unknown label {target_label}")
    if target.get("operator") != "any_of":
        errors.append(f"{context}.operator must be 'any_of'")

    alternatives = target.get("alternatives")
    if not isinstance(alternatives, list):
        errors.append(f"{context}.alternatives must be an array")
        return target_label, set(), 0

    seen_routes: set[str] = set()
    seen_nodes: set[str] = set()
    for index_number, alternative in enumerate(alternatives):
        alt_context = f"{context}.alternatives[{index_number}]"
        if not isinstance(alternative, dict):
            errors.append(f"{alt_context} must be an object")
            continue
        _unknown_fields(alternative, ALLOWED_ALTERNATIVE_FIELDS, alt_context, errors)
        _missing_fields(alternative, ALLOWED_ALTERNATIVE_FIELDS, alt_context, errors)

        route = alternative.get("route")
        if not isinstance(route, str) or not route:
            errors.append(f"{alt_context}.route must be a non-empty string")
            route = None
        elif route in seen_routes:
            errors.append(f"duplicate Blueprint route: {route}")
        else:
            seen_routes.add(route)
            if route not in EXPECTED_ROUTES:
                errors.append(f"{alt_context}.route is not an approved KLS route: {route}")
            route_label = f"route:{route}"
            if route_label not in index.labels:
                errors.append(f"{alt_context}.route references unknown label {route_label}")

        if alternative.get("operator") != "all_of":
            errors.append(f"{alt_context}.operator must be 'all_of'")

        nodes = alternative.get("nodes")
        if not isinstance(nodes, list) or not nodes:
            errors.append(f"{alt_context}.nodes must be a non-empty array")
            continue
        if not all(isinstance(node, str) and node for node in nodes):
            errors.append(f"{alt_context}.nodes must contain only non-empty labels")
            continue
        if len(nodes) != len(set(nodes)):
            errors.append(f"{alt_context}.nodes contains duplicate labels")
        for node in nodes:
            if node in seen_nodes:
                errors.append(f"route node appears in more than one alternative: {node}")
            seen_nodes.add(node)
            if node not in index.labels:
                errors.append(f"{alt_context}.nodes references unknown label {node}")

        if route in EXPECTED_ROUTES and set(nodes) != set(EXPECTED_ROUTES[route]):
            expected = ", ".join(EXPECTED_ROUTES[route])
            errors.append(f"{alt_context}.nodes must be exactly: {expected}")

    missing_routes = sorted(set(EXPECTED_ROUTES) - seen_routes)
    unexpected_routes = sorted(seen_routes - set(EXPECTED_ROUTES))
    if missing_routes:
        errors.append(f"routes: missing approved route(s): {', '.join(missing_routes)}")
    if unexpected_routes:
        errors.append(f"routes: unexpected route(s): {', '.join(unexpected_routes)}")
    return target_label, seen_nodes, len(seen_routes)


def _validate_or_target(
    target: str | None,
    route_nodes: set[str],
    index: BlueprintIndex,
    errors: list[str],
) -> None:
    if target is None:
        return
    block = index.blocks.get(target)
    if block is None:
        errors.append(f"Blueprint target {target} must occur inside a LaTeX environment")
        return
    target_uses: set[str] = set()
    for match in USES.finditer(block.body):
        target_uses.update(entry.strip() for entry in match.group(1).split(",") if entry.strip())
    if route_nodes and route_nodes.issubset(target_uses):
        errors.append(
            f"Blueprint target {target} must not encode every any_of route node as \\uses"
        )


def _ledger_nodes(path: Path, errors: list[str]) -> dict[str, dict[str, Any]]:
    document = _load_json_object(path, "certification ledger", errors)
    if document is None:
        return {}
    nodes = document.get("nodes")
    if not isinstance(nodes, list):
        errors.append("certification ledger nodes must be an array")
        return {}
    result: dict[str, dict[str, Any]] = {}
    for index, node in enumerate(nodes):
        if not isinstance(node, dict):
            errors.append(f"certification ledger node #{index + 1} must be an object")
            continue
        node_id = node.get("id")
        if not isinstance(node_id, str) or not node_id:
            errors.append(f"certification ledger node #{index + 1} has no valid id")
            continue
        if node_id in result:
            errors.append(f"certification ledger has duplicate node id: {node_id}")
        else:
            result[node_id] = node
    return result


def _validate_certificates(
    index: BlueprintIndex, ledger_path: Path, errors: list[str]
) -> None:
    ledger = _ledger_nodes(ledger_path, errors)
    certificate_declarations = {declaration for _node, declaration in CERTIFICATES.values()}
    for label, (node_id, declaration) in CERTIFICATES.items():
        if label not in index.labels:
            errors.append(f"Blueprint is missing certified result label: {label}")
            continue
        block = index.blocks.get(label)
        if block is None:
            errors.append(f"certified result {label} must occur inside a LaTeX environment")
            continue
        declarations: list[str] = []
        for match in LEAN.finditer(block.body):
            declarations.extend(entry.strip() for entry in match.group(1).split(",") if entry.strip())
        if declaration not in declarations:
            errors.append(f"{label}: \\lean must name {declaration}")
        conflicting = sorted((set(declarations) & certificate_declarations) - {declaration})
        if conflicting:
            errors.append(
                f"{label}: mapped to another certified declaration: {', '.join(conflicting)}"
            )
        if LEAN_OK.search(block.body) is None:
            errors.append(f"{label}: certified statement must contain \\leanok")

        node = ledger.get(node_id)
        if node is None:
            errors.append(f"{label}: certification ledger is missing {node_id}")
        elif node.get("status") != "proved" or node.get("checked_by") != "lean":
            errors.append(
                f"{label}: {node_id} must have status 'proved' and checked_by 'lean'"
            )


def check_blueprint(
    *,
    root: Path = ROOT,
    blueprint_path: Path | None = None,
    ledger_path: Path | None = None,
) -> tuple[list[str], dict[str, int]]:
    """Return offline structural errors and a small validation summary."""
    root = Path(root).resolve()
    blueprint = (
        Path(blueprint_path).resolve()
        if blueprint_path is not None
        else root / "formalization/blueprint"
    )
    ledger = (
        Path(ledger_path).resolve()
        if ledger_path is not None
        else root / "research/a-series/ledger.yaml"
    )
    errors: list[str] = []
    blueprint_index = _index_blueprint_tex(root, blueprint / "src/chapters", errors)
    target, route_nodes, route_count = _validate_routes(
        blueprint / "route-composition.yaml", blueprint_index, errors
    )
    _validate_or_target(target, route_nodes, blueprint_index, errors)
    _validate_certificates(blueprint_index, ledger, errors)
    return errors, {
        "files": blueprint_index.file_count,
        "labels": len(blueprint_index.labels),
        "routes": route_count,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT,
        help="repository root (defaults to the checker repository)",
    )
    args = parser.parse_args(argv)
    errors, summary = check_blueprint(root=args.root)
    for error in errors:
        print(f"FAIL: {error}")
    if errors:
        print(f"\n1 Blueprint, {len(errors)} error(s).")
        return 1
    print(
        f"1 Blueprint, {summary['files']} chapter file(s), "
        f"{summary['labels']} labels, {summary['routes']} routes. 0 error(s)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
