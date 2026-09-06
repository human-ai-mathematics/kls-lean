#!/usr/bin/env python3
"""Validate the statement lifecycle and Lean certification ledger.

The committed ``ledger.yaml`` uses the JSON subset of YAML 1.2, allowing this
checker to run with the Python standard library.  Exit 0 means that the ledger
is structurally valid and every node names a Lean artifact in the default
Lake build. Drafts and historical frozen snapshots may contain placeholders;
only proved nodes can claim ``checked_by: lean`` and must pass the escape-token
checks. This snapshot checker permits direct drafted-to-proved development;
it does not require a freeze or enforce public signature stability.

This structural check does not replace ``lake build`` or semantic review.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import tomllib
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "research/a-series/ledger.yaml"
ALLOWED_TOP_LEVEL_FIELDS = {"meta", "nodes"}
ALLOWED_META_FIELDS = {"program", "scope"}
ALLOWED_NODE_FIELDS = {
    "id",
    "kind",
    "status",
    "source",
    "statement",
    "lean_solution",
    "checked_by",
}
REQUIRED_NODE_FIELDS = {
    "id",
    "kind",
    "status",
    "statement",
    "lean_solution",
    "checked_by",
}
NODE_STATUSES = {"drafted", "frozen", "proved"}
FORBIDDEN_LEAN_TOKENS = re.compile(r"\b(?:sorry|admit|native_decide|axiom|unsafe)\b")
LEAN_IMPORTS = re.compile(
    r"^[ \t]*(?:public[ \t]+)?import[ \t]+([\w.]+(?:[ \t]+[\w.]+)*)", re.MULTILINE
)


def _check_proved_sources(root: Path, artifact: Path, context: str, errors: list[str]) -> None:
    """Apply the conservative token guard to the artifact and its local imports.

    Third-party libraries are outside this structural check; compilation and
    a proof-phase axiom audit remain separate obligations.
    """
    pending = [artifact]
    visited: set[Path] = set()
    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        try:
            text = source.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            errors.append(f"{context}: cannot read Lean source {source}: {exc}")
            continue
        forbidden = sorted(set(FORBIDDEN_LEAN_TOKENS.findall(text)))
        if forbidden:
            errors.append(
                f"{context}: forbidden Lean escape token(s) in "
                f"{source.relative_to(root)}: {', '.join(forbidden)}"
            )
        for module in (module for imports in LEAN_IMPORTS.findall(text) for module in imports.split()):
            relative = Path(*module.split(".")).with_suffix(".lean")
            for base in (root / "formalization", root):
                dependency = (base / relative).resolve()
                if dependency.is_relative_to(root) and dependency.is_file():
                    pending.append(dependency)
                    break


def _mentions_token(text: str, token: str) -> bool:
    token_characters = r"A-Za-z0-9_./:\-"
    return re.search(
        rf"(?<![{token_characters}]){re.escape(token)}(?![{token_characters}])",
        text,
    ) is not None


def _load_document(path: Path, errors: list[str]) -> dict[str, Any] | None:
    if not path.is_file():
        errors.append(f"ledger does not exist: {path}")
        return None
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        errors.append(f"cannot read JSON-compatible YAML ledger: {exc}")
        return None
    if not isinstance(document, dict):
        errors.append("ledger top level must be an object")
        return None
    return document


def _default_lake_modules(root: Path, errors: list[str]) -> set[str]:
    lakefile = root / "formalization/lakefile.toml"
    if not lakefile.is_file():
        errors.append("formalization/lakefile.toml does not exist")
        return set()
    try:
        config = tomllib.loads(lakefile.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        errors.append(f"cannot read formalization/lakefile.toml: {exc}")
        return set()

    default_targets = config.get("defaultTargets")
    if not isinstance(default_targets, list) or not all(
        isinstance(target, str) and target for target in default_targets
    ):
        errors.append("formalization/lakefile.toml: defaultTargets must be a string list")
        return set()

    modules: set[str] = set()
    libraries = config.get("lean_lib", [])
    if not isinstance(libraries, list):
        errors.append("formalization/lakefile.toml: lean_lib must be an array of tables")
        return set()
    for library in libraries:
        if not isinstance(library, dict) or library.get("name") not in default_targets:
            continue
        roots = library.get("roots", [])
        if isinstance(roots, list):
            modules.update(root for root in roots if isinstance(root, str) and root)
    return modules


def _validate_lean_certificate(
    root: Path,
    node_id: str,
    reference: Any,
    default_modules: set[str],
    errors: list[str],
    *,
    proved: bool,
) -> None:
    context = f"{node_id}.lean_solution"
    if not isinstance(reference, str) or not reference.strip():
        errors.append(f"{context}: must be a non-empty repository-relative path")
        return

    relative = Path(reference)
    if relative.is_absolute():
        errors.append(f"{context}: absolute paths are forbidden")
        return

    artifact = (root / relative).resolve()
    solutions = (root / "solutions").resolve()
    try:
        artifact.relative_to(solutions)
    except ValueError:
        errors.append(f"{context}: artifact must stay under solutions/")
        return

    if artifact.suffix != ".lean":
        errors.append(f"{context}: artifact must have the .lean suffix")
    if not artifact.is_file():
        errors.append(f"{context}: artifact does not exist: {reference}")
        return

    try:
        text = artifact.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        errors.append(f"{context}: cannot read artifact: {exc}")
        return

    if not _mentions_token(text[:2500], node_id):
        errors.append(f"{context}: certificate header does not name {node_id}")
    if proved:
        _check_proved_sources(root, artifact, context, errors)

    module = ".".join(relative.with_suffix("").parts)
    if module not in default_modules:
        errors.append(
            f"{context}: module {module} is not a root of a default Lake target"
        )


def check_ledger(
    *, root: Path = ROOT, ledger_path: Path | None = None
) -> tuple[list[str], dict[str, Any] | None]:
    """Return structural errors and the parsed ledger document."""
    root = Path(root).resolve()
    ledger_path = Path(ledger_path) if ledger_path is not None else root / "research/a-series/ledger.yaml"
    errors: list[str] = []
    document = _load_document(ledger_path, errors)
    if document is None:
        return errors, None

    for field in sorted(set(document) - ALLOWED_TOP_LEVEL_FIELDS):
        errors.append(f"unknown top-level field: {field}")

    meta = document.get("meta")
    if not isinstance(meta, dict):
        errors.append("meta must be an object")
    else:
        for field in sorted(set(meta) - ALLOWED_META_FIELDS):
            errors.append(f"meta: unknown field: {field}")
        if meta.get("program") != "a-series":
            errors.append("meta.program must be 'a-series'")
        scope = meta.get("scope")
        if not isinstance(scope, str) or not scope.strip():
            errors.append("meta.scope must be a non-empty string")

    nodes = document.get("nodes")
    if not isinstance(nodes, list):
        errors.append("nodes must be an array")
        return errors, document

    default_modules = _default_lake_modules(root, errors)
    seen: set[str] = set()
    for index, node in enumerate(nodes, start=1):
        context = f"node #{index}"
        if not isinstance(node, dict):
            errors.append(f"{context}: must be an object")
            continue
        for field in sorted(set(node) - ALLOWED_NODE_FIELDS):
            errors.append(f"{context}: unknown field: {field}")
        for field in sorted(REQUIRED_NODE_FIELDS - set(node)):
            errors.append(f"{context}: missing field: {field}")

        node_id = node.get("id")
        if not isinstance(node_id, str) or not node_id.strip():
            errors.append(f"{context}.id: must be a non-empty string")
            continue
        if node_id in seen:
            errors.append(f"duplicate node id: {node_id}")
        seen.add(node_id)

        if node.get("kind") != "lemma":
            errors.append(f"{node_id}.kind: Issue #2 node must be 'lemma'")
        statement = node.get("statement")
        if not isinstance(statement, str) or not statement.strip():
            errors.append(f"{node_id}.statement: must be a non-empty string")

        status = node.get("status")
        if not isinstance(status, str) or status not in NODE_STATUSES:
            errors.append(f"{node_id}.status: must be 'drafted', 'frozen', or 'proved'")
        checked_by = node.get("checked_by")
        if checked_by == "lean" and status != "proved":
            errors.append(f"{node_id}.status: checked_by lean requires 'proved'")
        if status == "proved" and checked_by != "lean":
            errors.append(f"{node_id}.checked_by: proved nodes require 'lean'")
        if status in ("drafted", "frozen") and checked_by is not None:
            errors.append(f"{node_id}.checked_by: drafted/frozen nodes require null")
        _validate_lean_certificate(
            root,
            node_id,
            node.get("lean_solution"),
            default_modules,
            errors,
            proved=status == "proved",
        )

    if "lem:linear-test-lower" not in seen:
        errors.append("required Issue #2 node is missing: lem:linear-test-lower")
    return errors, document


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs="?", choices=("check", "node"), default="check")
    parser.add_argument("node_id", nargs="?")
    args = parser.parse_args(argv)
    if args.command == "check" and args.node_id is not None:
        parser.error("check does not accept a node id")

    errors, document = check_ledger()
    for error in errors:
        print(f"FAIL: {error}")
    if errors:
        print(f"\n1 ledger(s). {len(errors)} error(s).")
        return 1

    assert document is not None
    nodes = document["nodes"]
    if args.command == "node":
        if not args.node_id:
            parser.error("node requires NODE_ID")
        for node in nodes:
            if node.get("id") == args.node_id:
                print(json.dumps(node, indent=2, ensure_ascii=False))
                return 0
        print(f"No ledger node matches '{args.node_id}'.", file=sys.stderr)
        return 1

    print(f"1 ledger(s), {len(nodes)} nodes. 0 error(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
