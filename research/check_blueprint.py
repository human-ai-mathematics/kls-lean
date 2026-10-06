#!/usr/bin/env python3
"""Validate the KLS Lean Blueprint's offline dependency metadata.

The Blueprint sources remain ordinary LaTeX.  This checker covers the small
machine-readable boundary around them: labels and ``\\uses`` references, the
JSON subset stored in ``route-composition.yaml``, and declarations presented
as Lean-certified.  It deliberately does not parse mathematics or infer proof
status from prose.  In particular, review evidence is never treated as Lean
certification.
"""
from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Literal


ROOT = Path(__file__).resolve().parents[1]
BLUEPRINT = ROOT / "formalization/blueprint"
ROUTES = BLUEPRINT / "route-composition.yaml"
LEDGER = ROOT / "research/a-series/ledger.yaml"

# Version 1 is intentionally frozen.  It remains accepted so an old, pinned
# Blueprint checkout can still be checked without silently acquiring v2
# semantics.
V1_TOP_LEVEL_FIELDS = {"version", "targets"}
V1_TARGET_FIELDS = {"target", "operator", "alternatives"}
V1_ALTERNATIVE_FIELDS = {"route", "operator", "nodes"}
V1_EXPECTED_ROUTES: dict[str, tuple[str, ...]] = {
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

# Kept as a public compatibility alias for downstream fixture code.
EXPECTED_ROUTES = V1_EXPECTED_ROUTES

V2_TOP_LEVEL_FIELDS = {"version", "sources", "claims", "branches", "targets"}
V2_SOURCE_BASE_FIELDS = {"id", "kind"}
V2_LOCAL_SOURCE_FIELDS = V2_SOURCE_BASE_FIELDS | {"root", "ledger"}
V2_GIT_SOURCE_FIELDS = V2_SOURCE_BASE_FIELDS | {
    "repository",
    "revision",
    "ledger",
}
V2_CLAIM_FIELDS = {"node", "state", "provenance", "evidence", "refuted_by"}
V2_CLAIM_PROVENANCE_FIELDS = {"source", "record", "path"}
V2_BRANCH_FIELDS = {
    "id",
    "route",
    "disposition",
    "provenance",
    "requires",
    "refuted_by",
    "superseded_by",
}
V2_BRANCH_PROVENANCE_FIELDS = {"source", "path"}
V2_TARGET_FIELDS = {"target", "adapters", "composition"}
V2_GROUP_FIELDS = {"operator", "items"}

CLAIM_STATES = {"open", "conditional", "proved", "imported", "defined", "refuted"}
BRANCH_DISPOSITIONS = {"active", "historical", "refuted"}
EVIDENCE_FIELDS = {
    "agent_review": {"kind", "source", "artifact"},
    "human_review": {"kind", "source", "artifact"},
    "published": {"kind", "source", "references"},
    "lean": {"kind", "source", "ledger_node", "declaration"},
}
MAX_EXPRESSION_DEPTH = 32
PINNED_EXPLORATION_REPOSITORY = (
    "https://github.com/numina-functional-inequalities/kls-conjecture-search.git"
)
PINNED_EXPLORATION_REVISION = "34b5fcd57fef17089e781616005fe6d3641bd11e"
REQUIRED_ACTIVE_ROUTES = {
    "eldan-localization",
    "moment-map-spectral",
    "moment-map-cmh",
    "conditional-fiber-frame",
}
REQUIRED_REPOSITORY_ADAPTERS = {
    "thm:selected-literature-constant-equivalence",
    "thm:affine-isotropic-reduction",
}

# Blueprint label -> (ledger node, public Lean certificate declaration).
CERTIFICATES: dict[str, tuple[str, str]] = {
    "cor:absolutely-continuous-relaxation-two-cheeger": (
        "cor:absolutely-continuous-relaxation-two-cheeger",
        "Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate",
    ),
    "thm:smooth-gradient-relaxation-two-cheeger": (
        "thm:smooth-gradient-relaxation-two-cheeger",
        "Solutions.ThmSmoothGradientRelaxationTwoCheeger.certificate",
    ),
    "thm:relaxed-minkowski-content-perimeter": (
        "thm:relaxed-minkowski-content-perimeter",
        "Solutions.ThmRelaxedMinkowskiContentPerimeter.certificate",
    ),
    "thm:bakry-emery-poincare": (
        "thm:bakry-emery-poincare",
        "Solutions.ThmBakryEmeryPoincare.certificate",
    ),
    "lem:relative-perimeter-cheeger-infimum": (
        "lem:relative-perimeter-cheeger-infimum",
        "Solutions.LemRelativePerimeterCheegerInfimum.certificate",
    ),
    "cor:conditional-fiber-twelve-bound": (
        "cor:conditional-fiber-twelve-bound",
        "Solutions.CorConditionalFiberTwelveBound.certificate",
    ),
    "lem:conditional-fiber-energy-comparison": (
        "lem:conditional-fiber-energy-comparison",
        "Solutions.LemConditionalFiberEnergyComparison.certificate",
    ),
    "lem:conditional-fiber-form": (
        "lem:conditional-fiber-form",
        "Solutions.LemConditionalFiberForm.certificate",
    ),
    "thm:smooth-gradient-raw-core-agreement-density": (
        "thm:smooth-gradient-raw-core-agreement-density",
        "Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate",
    ),
    "thm:one-dimensional-logconcave-poincare": (
        "thm:one-dimensional-logconcave-poincare",
        "Solutions.ThmOneDimensionalLogConcavePoincare.certificate",
    ),
    "thm:smooth-gradient-relaxation-dirichlet": (
        "thm:smooth-gradient-relaxation-dirichlet",
        "Solutions.ThmSmoothGradientRelaxationDirichlet.certificate",
    ),
    "thm:affine-isotropic-reduction": (
        "thm:affine-isotropic-reduction",
        "Solutions.ThmAffineIsotropicReduction.certificate",
    ),
    "lem:affine-poincare-translation-invariance": (
        "lem:affine-poincare-translation-invariance",
        "Solutions.LemAffinePoincareTranslationInvariance.certificate",
    ),
    "thm:affine-covariance-relaxation-closed": (
        "thm:affine-covariance-relaxation-closed",
        "Solutions.ThmAffineCovarianceRelaxationClosed.certificate",
    ),
    "lem:covariance-core-closure": (
        "lem:covariance-core-closure",
        "Solutions.LemCovarianceCoreClosure.certificate",
    ),
    "lem:ambient-intrinsic-covariance": (
        "lem:ambient-intrinsic-covariance",
        "Solutions.LemAmbientIntrinsicCovariance.certificate",
    ),
    "thm:borell-logconcave-density": (
        "thm:borell-logconcave-density",
        "Solutions.ThmBorellLogconcaveDensity.certificate",
    ),
    "lem:logconcave-intrinsic-absolute-continuity": (
        "lem:logconcave-intrinsic-absolute-continuity",
        "Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate",
    ),
    "thm:selected-literature-constant-equivalence": (
        "thm:selected-literature-constant-equivalence",
        "Solutions.ThmSelectedLiteratureConstantEquivalence.certificate",
    ),
    "thm:compact-borell-logconcavity-equivalence": (
        "thm:compact-borell-logconcavity-equivalence",
        "Solutions.ThmCompactBorellLogconcavityEquivalence.certificate",
    ),
    "thm:smooth-lipschitz-constant-equivalence": (
        "thm:smooth-lipschitz-constant-equivalence",
        "Solutions.ThmSmoothLipschitzConstantEquivalence.certificate",
    ),
    "lem:covariance-test-core-density": (
        "lem:covariance-test-core-density",
        "Solutions.LemCovarianceTestCoreDensity.certificate",
    ),
    "cert:ambient-intrinsic-comparison": (
        "lem:ambient-intrinsic-poincare-comparison",
        "Solutions.LemAmbientIntrinsicPoincareComparison.certificate",
    ),
    "cert:legacy-relaxed-comparison": (
        "lem:legacy-relaxed-poincare-comparison",
        "Solutions.LemLegacyRelaxedPoincareComparison.certificate",
    ),
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
FULL_GIT_REVISION = re.compile(r"[0-9a-f]{40}")


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


@dataclass(frozen=True)
class SourceRecord:
    source_id: str
    kind: Literal["local", "git"]
    root: Path | None
    ledger: Path | None


@dataclass
class ExpressionInfo:
    references: set[str] = field(default_factory=set)
    any_of_choices: list[list[set[str]]] = field(default_factory=list)


@dataclass
class ClaimRecord:
    node: str
    state: str
    evidence: list[dict[str, Any]]
    refuted_by: list[str]


@dataclass
class BranchRecord:
    branch_id: str
    route: str
    disposition: str
    requires: ExpressionInfo
    refuted_by: list[str]
    superseded_by: list[str]


@dataclass
class RouteValidation:
    schema_version: int
    route_count: int
    targets: list[tuple[str, list[list[set[str]]]]]
    claims: dict[str, ClaimRecord] = field(default_factory=dict)
    branches: dict[str, BranchRecord] = field(default_factory=dict)


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


def _load_json_object(
    path: Path, description: str, errors: list[str]
) -> dict[str, Any] | None:
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
    for field_name in sorted(set(value) - allowed):
        errors.append(f"{context}: unknown field: {field_name}")


def _missing_fields(
    value: dict[str, Any], required: set[str], context: str, errors: list[str]
) -> None:
    for field_name in sorted(required - set(value)):
        errors.append(f"{context}: missing field: {field_name}")


def _string(value: Any, context: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or not value.strip():
        errors.append(f"{context} must be a non-empty string")
        return None
    return value.strip()


def _string_list(value: Any, context: str, errors: list[str]) -> list[str]:
    if not isinstance(value, list) or not value:
        errors.append(f"{context} must be a non-empty array")
        return []
    if not all(isinstance(entry, str) and entry.strip() for entry in value):
        errors.append(f"{context} must contain only non-empty strings")
        return []
    result = [entry.strip() for entry in value]
    if len(result) != len(set(result)):
        errors.append(f"{context} contains duplicate entries")
    return result


def _safe_relative_path(
    value: Any,
    context: str,
    errors: list[str],
    *,
    allow_dot: bool = False,
) -> Path | None:
    path_string = _string(value, context, errors)
    if path_string is None:
        return None
    path = Path(path_string)
    if "\\" in path_string or path.is_absolute() or ".." in path.parts:
        errors.append(f"{context} must be a safe repository-relative path")
        return None
    if path_string == "." and not allow_dot:
        errors.append(f"{context} must name a repository-relative file")
        return None
    return path


def _within(base: Path, relative: Path, context: str, errors: list[str]) -> Path | None:
    resolved_base = base.resolve()
    resolved = (resolved_base / relative).resolve()
    try:
        resolved.relative_to(resolved_base)
    except ValueError:
        errors.append(f"{context} resolves outside its source root")
        return None
    return resolved


def _validate_v1_routes(
    document: dict[str, Any], index: BlueprintIndex, errors: list[str]
) -> RouteValidation:
    _unknown_fields(document, V1_TOP_LEVEL_FIELDS, "routes", errors)
    _missing_fields(document, V1_TOP_LEVEL_FIELDS, "routes", errors)

    targets = document.get("targets")
    if not isinstance(targets, list) or len(targets) != 1:
        errors.append("routes.targets must be a single-element array")
        return RouteValidation(1, 0, [])
    target = targets[0]
    if not isinstance(target, dict):
        errors.append("routes.targets[0] must be an object")
        return RouteValidation(1, 0, [])

    context = "routes.targets[0]"
    _unknown_fields(target, V1_TARGET_FIELDS, context, errors)
    _missing_fields(target, V1_TARGET_FIELDS, context, errors)
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
        return RouteValidation(1, 0, [])

    seen_routes: set[str] = set()
    seen_nodes: set[str] = set()
    choices: list[set[str]] = []
    for index_number, alternative in enumerate(alternatives):
        alt_context = f"{context}.alternatives[{index_number}]"
        if not isinstance(alternative, dict):
            errors.append(f"{alt_context} must be an object")
            continue
        _unknown_fields(alternative, V1_ALTERNATIVE_FIELDS, alt_context, errors)
        _missing_fields(alternative, V1_ALTERNATIVE_FIELDS, alt_context, errors)

        route = alternative.get("route")
        if not isinstance(route, str) or not route:
            errors.append(f"{alt_context}.route must be a non-empty string")
            route = None
        elif route in seen_routes:
            errors.append(f"duplicate Blueprint route: {route}")
        else:
            seen_routes.add(route)
            if route not in V1_EXPECTED_ROUTES:
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
        node_set = set(nodes)
        choices.append(node_set)
        if len(nodes) != len(node_set):
            errors.append(f"{alt_context}.nodes contains duplicate labels")
        for node in nodes:
            if node in seen_nodes:
                errors.append(f"route node appears in more than one alternative: {node}")
            seen_nodes.add(node)
            if node not in index.labels:
                errors.append(f"{alt_context}.nodes references unknown label {node}")

        if route in V1_EXPECTED_ROUTES and node_set != set(V1_EXPECTED_ROUTES[route]):
            expected = ", ".join(V1_EXPECTED_ROUTES[route])
            errors.append(f"{alt_context}.nodes must be exactly: {expected}")

    missing_routes = sorted(set(V1_EXPECTED_ROUTES) - seen_routes)
    unexpected_routes = sorted(seen_routes - set(V1_EXPECTED_ROUTES))
    if missing_routes:
        errors.append(f"routes: missing approved route(s): {', '.join(missing_routes)}")
    if unexpected_routes:
        errors.append(f"routes: unexpected route(s): {', '.join(unexpected_routes)}")
    target_groups = [(target_label, [choices])] if target_label else []
    return RouteValidation(1, len(seen_routes), target_groups)


def _validate_sources(
    value: Any, root: Path, errors: list[str]
) -> dict[str, SourceRecord]:
    if not isinstance(value, list) or not value:
        errors.append("routes.sources must be a non-empty array")
        return {}
    sources: dict[str, SourceRecord] = {}
    for source_index, source in enumerate(value):
        context = f"routes.sources[{source_index}]"
        if not isinstance(source, dict):
            errors.append(f"{context} must be an object")
            continue
        source_id = _string(source.get("id"), f"{context}.id", errors)
        kind = source.get("kind")
        if kind not in {"local", "git"}:
            errors.append(f"{context}.kind must be 'local' or 'git'")
            _unknown_fields(source, V2_SOURCE_BASE_FIELDS, context, errors)
            continue
        allowed = V2_LOCAL_SOURCE_FIELDS if kind == "local" else V2_GIT_SOURCE_FIELDS
        _unknown_fields(source, allowed, context, errors)
        _missing_fields(source, allowed, context, errors)
        if source_id is None:
            continue
        if source_id in sources:
            errors.append(f"duplicate route source id: {source_id}")
            continue

        ledger_relative = _safe_relative_path(
            source.get("ledger"), f"{context}.ledger", errors
        )
        if kind == "local":
            root_relative = _safe_relative_path(
                source.get("root"), f"{context}.root", errors, allow_dot=True
            )
            local_root = (
                _within(root, root_relative, f"{context}.root", errors)
                if root_relative
                else None
            )
            ledger_path = (
                _within(local_root, ledger_relative, f"{context}.ledger", errors)
                if local_root is not None and ledger_relative is not None
                else None
            )
            if local_root is not None and not local_root.is_dir():
                errors.append(f"{context}.root does not exist as a directory: {local_root}")
            if ledger_path is not None and not ledger_path.is_file():
                errors.append(f"{context}.ledger does not exist: {ledger_path}")
            sources[source_id] = SourceRecord(source_id, "local", local_root, ledger_path)
        else:
            repository = _string(
                source.get("repository"), f"{context}.repository", errors
            )
            revision = _string(source.get("revision"), f"{context}.revision", errors)
            if repository is not None and not repository.startswith("https://"):
                errors.append(f"{context}.repository must be an HTTPS Git URL")
            if revision is not None and FULL_GIT_REVISION.fullmatch(revision) is None:
                errors.append(f"{context}.revision must be a full lowercase Git commit hash")
            sources[source_id] = SourceRecord(source_id, "git", None, ledger_relative)
    return sources


def _validate_provenance(
    value: Any,
    *,
    context: str,
    sources: dict[str, SourceRecord],
    root: Path,
    branch: bool,
    expected_label: str | None,
    errors: list[str],
) -> None:
    if not isinstance(value, dict):
        errors.append(f"{context} must be an object")
        return
    allowed = V2_BRANCH_PROVENANCE_FIELDS if branch else V2_CLAIM_PROVENANCE_FIELDS
    _unknown_fields(value, allowed, context, errors)
    _missing_fields(value, {"source", "path"} if branch else {"source"}, context, errors)
    source_id = _string(value.get("source"), f"{context}.source", errors)
    source = sources.get(source_id) if source_id is not None else None
    if source_id is not None and source is None:
        errors.append(f"{context}.source references unknown source {source_id}")
    record_present = "record" in value
    path_present = "path" in value
    if not branch and not record_present and not path_present:
        errors.append(f"{context} must contain record or path")
    if record_present:
        _string(value.get("record"), f"{context}.record", errors)
    if path_present:
        relative = _safe_relative_path(value.get("path"), f"{context}.path", errors)
        if source is not None and source.kind == "local" and source.root and relative:
            resolved = _within(source.root, relative, f"{context}.path", errors)
            if resolved is not None and not resolved.is_file():
                errors.append(f"{context}.path does not exist: {resolved}")
            elif resolved is not None and expected_label is not None:
                try:
                    source_text = _strip_tex_comments(
                        resolved.read_text(encoding="utf-8")
                    )
                except (OSError, UnicodeError) as exc:
                    errors.append(f"{context}.path cannot be read: {exc}")
                else:
                    path_labels = {
                        match.group(1).strip() for match in LABEL.finditer(source_text)
                    }
                    if expected_label not in path_labels:
                        errors.append(
                            f"{context}.path does not contain label {expected_label}"
                        )


def _validate_evidence(
    value: Any,
    *,
    context: str,
    sources: dict[str, SourceRecord],
    errors: list[str],
) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        errors.append(f"{context} must be an array")
        return []
    result: list[dict[str, Any]] = []
    fingerprints: set[str] = set()
    for evidence_index, evidence in enumerate(value):
        item_context = f"{context}[{evidence_index}]"
        if not isinstance(evidence, dict):
            errors.append(f"{item_context} must be an object")
            continue
        kind = evidence.get("kind")
        allowed = EVIDENCE_FIELDS.get(kind) if isinstance(kind, str) else None
        if allowed is None:
            errors.append(f"{item_context}.kind is not a supported evidence kind")
            continue
        _unknown_fields(evidence, allowed, item_context, errors)
        _missing_fields(evidence, allowed, item_context, errors)
        source_id = _string(evidence.get("source"), f"{item_context}.source", errors)
        if source_id is not None and source_id not in sources:
            errors.append(f"{item_context}.source references unknown source {source_id}")
        if kind in {"agent_review", "human_review"}:
            _safe_relative_path(evidence.get("artifact"), f"{item_context}.artifact", errors)
        elif kind == "published":
            _string_list(evidence.get("references"), f"{item_context}.references", errors)
        else:
            _string(evidence.get("ledger_node"), f"{item_context}.ledger_node", errors)
            _string(evidence.get("declaration"), f"{item_context}.declaration", errors)
        fingerprint = json.dumps(evidence, sort_keys=True, separators=(",", ":"))
        if fingerprint in fingerprints:
            errors.append(f"{context} contains duplicate evidence entries")
        fingerprints.add(fingerprint)
        result.append(evidence)
    return result


def _validate_expression(
    value: Any,
    *,
    leaf_kind: Literal["node", "branch"],
    context: str,
    errors: list[str],
    depth: int = 0,
) -> ExpressionInfo:
    if depth > MAX_EXPRESSION_DEPTH:
        errors.append(f"{context} exceeds maximum expression depth {MAX_EXPRESSION_DEPTH}")
        return ExpressionInfo()
    if not isinstance(value, dict):
        errors.append(f"{context} must be an expression object")
        return ExpressionInfo()

    if set(value) == {leaf_kind}:
        reference = _string(value.get(leaf_kind), f"{context}.{leaf_kind}", errors)
        return ExpressionInfo({reference} if reference else set(), [])

    if "operator" not in value and "items" not in value:
        errors.append(
            f"{context} must be exactly a {leaf_kind} leaf or an operator/items group"
        )
        return ExpressionInfo()

    _unknown_fields(value, V2_GROUP_FIELDS, context, errors)
    _missing_fields(value, V2_GROUP_FIELDS, context, errors)
    operator = value.get("operator")
    if operator not in {"all_of", "any_of"}:
        errors.append(f"{context}.operator must be 'all_of' or 'any_of'")
    items = value.get("items")
    if not isinstance(items, list) or len(items) < 2:
        errors.append(f"{context}.items must be an array with at least two expressions")
        if not isinstance(items, list):
            return ExpressionInfo()

    references: set[str] = set()
    groups: list[list[set[str]]] = []
    choices: list[set[str]] = []
    for item_index, item in enumerate(items):
        child = _validate_expression(
            item,
            leaf_kind=leaf_kind,
            context=f"{context}.items[{item_index}]",
            errors=errors,
            depth=depth + 1,
        )
        duplicate = references & child.references
        for reference in sorted(duplicate):
            errors.append(f"{context}: duplicate {leaf_kind} reference: {reference}")
        references.update(child.references)
        groups.extend(child.any_of_choices)
        choices.append(set(child.references))
    if operator == "any_of":
        groups.append(choices)
    return ExpressionInfo(references, groups)


def _ledger_nodes(path: Path, errors: list[str]) -> dict[str, dict[str, Any]]:
    document = _load_json_object(path, "certification ledger", errors)
    if document is None:
        return {}
    nodes = document.get("nodes")
    if not isinstance(nodes, list):
        errors.append("certification ledger nodes must be an array")
        return {}
    result: dict[str, dict[str, Any]] = {}
    for index_number, node in enumerate(nodes):
        if not isinstance(node, dict):
            errors.append(f"certification ledger node #{index_number + 1} must be an object")
            continue
        node_id = node.get("id")
        if not isinstance(node_id, str) or not node_id:
            errors.append(f"certification ledger node #{index_number + 1} has no valid id")
            continue
        if node_id in result:
            errors.append(f"certification ledger has duplicate node id: {node_id}")
        else:
            result[node_id] = node
    return result


def _validate_claim_lean_evidence(
    claim: ClaimRecord,
    index: BlueprintIndex,
    sources: dict[str, SourceRecord],
    ledger_cache: dict[Path, dict[str, dict[str, Any]]],
    errors: list[str],
) -> None:
    lean_evidence = [item for item in claim.evidence if item.get("kind") == "lean"]
    block = index.blocks.get(claim.node)
    if block is not None and LEAN_OK.search(block.body) is not None and not lean_evidence:
        errors.append(
            f"routes claim {claim.node}: \\leanok requires explicit local Lean evidence"
        )
    for evidence_index, evidence in enumerate(lean_evidence):
        context = f"routes claim {claim.node}.evidence[{evidence_index}]"
        source_id = evidence.get("source")
        source = sources.get(source_id) if isinstance(source_id, str) else None
        if source is None:
            continue
        if source.kind != "local":
            errors.append(f"{context}: Lean evidence source must be local")
            continue
        if source.ledger is None or not source.ledger.is_file():
            errors.append(f"{context}: local Lean evidence source has no readable ledger")
            continue
        if source.ledger not in ledger_cache:
            ledger_cache[source.ledger] = _ledger_nodes(source.ledger, errors)
        ledger_node_id = evidence.get("ledger_node")
        ledger_node = ledger_cache[source.ledger].get(ledger_node_id)
        if ledger_node is None:
            errors.append(f"{context}: ledger is missing node {ledger_node_id}")
        elif ledger_node.get("status") != "proved" or ledger_node.get("checked_by") != "lean":
            errors.append(
                f"{context}: {ledger_node_id} must have status 'proved' and checked_by 'lean'"
            )
        if block is None:
            errors.append(f"routes claim {claim.node}: Lean evidence requires a TeX environment")
            continue
        declarations = {
            entry.strip()
            for match in LEAN.finditer(block.body)
            for entry in match.group(1).split(",")
            if entry.strip()
        }
        declaration = evidence.get("declaration")
        if declaration not in declarations:
            errors.append(f"routes claim {claim.node}: \\lean must name {declaration}")
        if LEAN_OK.search(block.body) is None:
            errors.append(f"routes claim {claim.node}: Lean evidence requires \\leanok")


def _validate_claims(
    value: Any,
    *,
    index: BlueprintIndex,
    sources: dict[str, SourceRecord],
    root: Path,
    errors: list[str],
) -> dict[str, ClaimRecord]:
    if not isinstance(value, list) or not value:
        errors.append("routes.claims must be a non-empty array")
        return {}
    claims: dict[str, ClaimRecord] = {}
    ledger_cache: dict[Path, dict[str, dict[str, Any]]] = {}
    for claim_index, value_item in enumerate(value):
        context = f"routes.claims[{claim_index}]"
        if not isinstance(value_item, dict):
            errors.append(f"{context} must be an object")
            continue
        _unknown_fields(value_item, V2_CLAIM_FIELDS, context, errors)
        _missing_fields(value_item, {"node", "state", "provenance", "evidence"}, context, errors)
        node = _string(value_item.get("node"), f"{context}.node", errors)
        state = value_item.get("state")
        if state not in CLAIM_STATES:
            errors.append(f"{context}.state is not a supported claim state")
            state = "invalid"
        _validate_provenance(
            value_item.get("provenance"),
            context=f"{context}.provenance",
            sources=sources,
            root=root,
            branch=False,
            expected_label=node,
            errors=errors,
        )
        evidence = _validate_evidence(
            value_item.get("evidence"),
            context=f"{context}.evidence",
            sources=sources,
            errors=errors,
        )
        if state == "open" and evidence:
            errors.append(f"{context}: open claims must not carry proof evidence")
        if state in {"proved", "conditional"} and not evidence:
            errors.append(f"{context}: {state} claims require explicit evidence")
        if state == "imported" and not any(item.get("kind") == "published" for item in evidence):
            errors.append(f"{context}: imported claims require published evidence")

        refuted_by: list[str] = []
        if state == "refuted":
            if "refuted_by" not in value_item:
                errors.append(f"{context}: refuted claims require refuted_by")
            else:
                refuted_by = _string_list(
                    value_item.get("refuted_by"), f"{context}.refuted_by", errors
                )
        elif "refuted_by" in value_item:
            errors.append(f"{context}: refuted_by is only allowed for refuted claims")

        if node is None:
            continue
        if node in claims:
            errors.append(f"duplicate route claim node: {node}")
            continue
        if node not in index.labels:
            errors.append(f"{context}.node references unknown label {node}")
        claim = ClaimRecord(node, state, evidence, refuted_by)
        claims[node] = claim
        _validate_claim_lean_evidence(claim, index, sources, ledger_cache, errors)

    for claim in claims.values():
        for refuter in claim.refuted_by:
            refuter_claim = claims.get(refuter)
            if refuter_claim is None:
                errors.append(f"routes claim {claim.node}: unknown refuter {refuter}")
            elif refuter_claim.state not in {"proved", "imported"} or not refuter_claim.evidence:
                errors.append(
                    f"routes claim {claim.node}: refuter {refuter} must be proved "
                    "or imported with evidence"
                )
    return claims


def _validate_branches(
    value: Any,
    *,
    index: BlueprintIndex,
    sources: dict[str, SourceRecord],
    claims: dict[str, ClaimRecord],
    root: Path,
    errors: list[str],
) -> dict[str, BranchRecord]:
    if not isinstance(value, list) or not value:
        errors.append("routes.branches must be a non-empty array")
        return {}
    branches: dict[str, BranchRecord] = {}
    for branch_index, value_item in enumerate(value):
        context = f"routes.branches[{branch_index}]"
        if not isinstance(value_item, dict):
            errors.append(f"{context} must be an object")
            continue
        _unknown_fields(value_item, V2_BRANCH_FIELDS, context, errors)
        _missing_fields(
            value_item,
            {"id", "route", "disposition", "provenance", "requires"},
            context,
            errors,
        )
        branch_id = _string(value_item.get("id"), f"{context}.id", errors)
        route = _string(value_item.get("route"), f"{context}.route", errors)
        disposition = value_item.get("disposition")
        if disposition not in BRANCH_DISPOSITIONS:
            errors.append(f"{context}.disposition is not supported")
            disposition = "invalid"
        _validate_provenance(
            value_item.get("provenance"),
            context=f"{context}.provenance",
            sources=sources,
            root=root,
            branch=True,
            expected_label=None,
            errors=errors,
        )
        requires = _validate_expression(
            value_item.get("requires"),
            leaf_kind="node",
            context=f"{context}.requires",
            errors=errors,
        )
        for node in sorted(requires.references):
            if node not in claims:
                errors.append(f"{context}.requires references unknown claim {node}")
            elif node not in index.labels:
                errors.append(f"{context}.requires references unknown label {node}")

        refuted_by: list[str] = []
        superseded_by: list[str] = []
        if "refuted_by" in value_item:
            refuted_by = _string_list(
                value_item.get("refuted_by"), f"{context}.refuted_by", errors
            )
        if "superseded_by" in value_item:
            superseded_by = _string_list(
                value_item.get("superseded_by"), f"{context}.superseded_by", errors
            )
        if disposition == "active":
            if "refuted_by" in value_item or "superseded_by" in value_item:
                errors.append(f"{context}: active branches cannot be refuted or superseded")
            for node in requires.references:
                if node in claims and claims[node].state == "refuted":
                    errors.append(f"{context}: active branch requires refuted claim {node}")
        elif disposition == "historical":
            if not superseded_by:
                errors.append(f"{context}: historical branches require superseded_by")
            if "refuted_by" in value_item:
                errors.append(f"{context}: historical branches cannot carry refuted_by")
        elif disposition == "refuted":
            if not refuted_by:
                errors.append(f"{context}: refuted branches require refuted_by")
            if not any(
                node in claims and claims[node].state == "refuted"
                for node in requires.references
            ):
                errors.append(f"{context}: refuted branch must require a refuted claim")

        if route is not None and f"route:{route}" not in index.labels:
            errors.append(f"{context}.route references unknown label route:{route}")
        if branch_id is None or route is None:
            continue
        if branch_id in branches:
            errors.append(f"duplicate route branch id: {branch_id}")
            continue
        branches[branch_id] = BranchRecord(
            branch_id, route, disposition, requires, refuted_by, superseded_by
        )

    for branch in branches.values():
        for successor in branch.superseded_by:
            successor_branch = branches.get(successor)
            if successor_branch is None:
                errors.append(f"routes branch {branch.branch_id}: unknown successor {successor}")
            elif successor_branch.disposition != "active":
                errors.append(
                    f"routes branch {branch.branch_id}: successor {successor} must be active"
                )
        for refuter in branch.refuted_by:
            refuter_claim = claims.get(refuter)
            if refuter_claim is None:
                errors.append(f"routes branch {branch.branch_id}: unknown refuter {refuter}")
            elif refuter_claim.state not in {"proved", "imported"} or not refuter_claim.evidence:
                errors.append(
                    f"routes branch {branch.branch_id}: refuter {refuter} must be "
                    "proved or imported with evidence"
                )

    active_routes = {
        branch.route for branch in branches.values() if branch.disposition == "active"
    }
    missing_routes = sorted(REQUIRED_ACTIVE_ROUTES - active_routes)
    unexpected_routes = sorted(active_routes - REQUIRED_ACTIVE_ROUTES)
    if missing_routes:
        errors.append(f"routes: missing required active route(s): {', '.join(missing_routes)}")
    if unexpected_routes:
        errors.append(
            f"routes: unexpected active route(s): {', '.join(unexpected_routes)}"
        )
    return branches


def _validate_targets(
    value: Any,
    *,
    index: BlueprintIndex,
    claims: dict[str, ClaimRecord],
    branches: dict[str, BranchRecord],
    errors: list[str],
) -> list[tuple[str, list[list[set[str]]]]]:
    if not isinstance(value, list) or not value:
        errors.append("routes.targets must be a non-empty array")
        return []
    result: list[tuple[str, list[list[set[str]]]]] = []
    target_names: set[str] = set()
    reachable_branches: set[str] = set()
    for target_index, value_item in enumerate(value):
        context = f"routes.targets[{target_index}]"
        if not isinstance(value_item, dict):
            errors.append(f"{context} must be an object")
            continue
        _unknown_fields(value_item, V2_TARGET_FIELDS, context, errors)
        _missing_fields(value_item, {"target", "composition"}, context, errors)
        target = _string(value_item.get("target"), f"{context}.target", errors)
        if target is not None:
            if target in target_names:
                errors.append(f"duplicate route target: {target}")
            target_names.add(target)
            if target not in claims:
                errors.append(f"{context}.target references unknown claim {target}")
            if target not in index.labels:
                errors.append(f"{context}.target references unknown label {target}")

        adapter_info = ExpressionInfo()
        adapter_value = value_item.get("adapters")
        if "adapters" in value_item:
            adapter_info = _validate_expression(
                adapter_value,
                leaf_kind="node",
                context=f"{context}.adapters",
                errors=errors,
            )
            for node in sorted(adapter_info.references):
                claim = claims.get(node)
                if claim is None:
                    errors.append(f"{context}.adapters references unknown claim {node}")
                elif claim.state == "refuted":
                    errors.append(f"{context}.adapters references refuted claim {node}")
                if node not in index.labels:
                    errors.append(f"{context}.adapters references unknown label {node}")

        composition_value = value_item.get("composition")
        composition = _validate_expression(
            composition_value,
            leaf_kind="branch",
            context=f"{context}.composition",
            errors=errors,
        )
        if (
            not isinstance(composition_value, dict)
            or composition_value.get("operator") != "any_of"
        ):
            errors.append(f"{context}.composition must have root operator 'any_of'")
        for branch_id in sorted(composition.references):
            branch = branches.get(branch_id)
            if branch is None:
                errors.append(f"{context}.composition references unknown branch {branch_id}")
            elif branch.disposition != "active":
                errors.append(
                    f"{context}.composition references non-active branch {branch_id}"
                )
            else:
                reachable_branches.add(branch_id)

        node_groups: list[list[set[str]]] = []
        for branch_choices in composition.any_of_choices:
            node_choices: list[set[str]] = []
            for branch_choice in branch_choices:
                nodes: set[str] = set()
                for branch_id in branch_choice:
                    if branch_id in branches:
                        nodes.update(branches[branch_id].requires.references)
                node_choices.append(nodes)
            node_groups.append(node_choices)
        for branch_id in composition.references:
            if branch_id in branches:
                node_groups.extend(branches[branch_id].requires.any_of_choices)
        if target is not None:
            result.append((target, node_groups))

        if target == "conj:kls":
            if not (
                isinstance(adapter_value, dict)
                and adapter_value.get("operator") == "all_of"
            ):
                errors.append(
                    f"{context}.adapters must have root operator 'all_of'"
                )
            missing_adapters = sorted(
                REQUIRED_REPOSITORY_ADAPTERS - adapter_info.references
            )
            if missing_adapters:
                errors.append(
                    f"{context}.adapters is missing required repository adapter(s): "
                    + ", ".join(missing_adapters)
                )

    if "conj:kls" not in target_names:
        errors.append("routes.targets must include conj:kls")
    active = {
        branch_id
        for branch_id, branch in branches.items()
        if branch.disposition == "active"
    }
    unreachable = sorted(active - reachable_branches)
    if unreachable:
        errors.append(f"routes: active branch is unreachable: {', '.join(unreachable)}")
    return result


def _validate_v2_routes(
    document: dict[str, Any],
    index: BlueprintIndex,
    root: Path,
    errors: list[str],
) -> RouteValidation:
    _unknown_fields(document, V2_TOP_LEVEL_FIELDS, "routes", errors)
    _missing_fields(document, V2_TOP_LEVEL_FIELDS, "routes", errors)
    sources = _validate_sources(document.get("sources"), root, errors)

    exploration = sources.get("kls-exploration")
    for source_index, source_value in enumerate(document.get("sources", [])):
        if not isinstance(source_value, dict) or source_value.get("id") != "kls-exploration":
            continue
        if source_value.get("repository") != PINNED_EXPLORATION_REPOSITORY:
            errors.append(
                f"routes.sources[{source_index}].repository must pin the canonical "
                "kls-exploration repository"
            )
        if source_value.get("revision") != PINNED_EXPLORATION_REVISION:
            errors.append(
                f"routes.sources[{source_index}].revision must pin {PINNED_EXPLORATION_REVISION}"
            )
    if exploration is None:
        errors.append("routes.sources must include kls-exploration")
    local = sources.get("kls-lean")
    if local is None or local.kind != "local":
        errors.append("routes.sources must include local source kls-lean")

    claims = _validate_claims(
        document.get("claims"),
        index=index,
        sources=sources,
        root=root,
        errors=errors,
    )
    branches = _validate_branches(
        document.get("branches"),
        index=index,
        sources=sources,
        claims=claims,
        root=root,
        errors=errors,
    )
    targets = _validate_targets(
        document.get("targets"),
        index=index,
        claims=claims,
        branches=branches,
        errors=errors,
    )
    route_count = len(
        {branch.route for branch in branches.values() if branch.disposition == "active"}
    )
    return RouteValidation(2, route_count, targets, claims, branches)


def _validate_routes(
    path: Path, index: BlueprintIndex, root: Path, errors: list[str]
) -> RouteValidation:
    document = _load_json_object(path, "Blueprint route composition", errors)
    if document is None:
        return RouteValidation(0, 0, [])
    version = document.get("version")
    if type(version) is not int or version not in {1, 2}:
        errors.append("routes.version must be the integer 1 or 2")
        return RouteValidation(0, 0, [])
    if version == 1:
        return _validate_v1_routes(document, index, errors)
    return _validate_v2_routes(document, index, root, errors)


def _target_uses(target: str, index: BlueprintIndex, errors: list[str]) -> set[str]:
    block = index.blocks.get(target)
    if block is None:
        errors.append(f"Blueprint target {target} must occur inside a LaTeX environment")
        return set()
    result: set[str] = set()
    for match in USES.finditer(block.body):
        result.update(entry.strip() for entry in match.group(1).split(",") if entry.strip())
    return result


def _validate_or_targets(
    validation: RouteValidation, index: BlueprintIndex, errors: list[str]
) -> None:
    for target, groups in validation.targets:
        target_uses = _target_uses(target, index, errors)
        for choices in groups:
            route_nodes = set().union(*choices) if choices else set()
            if choices and all(choices) and route_nodes.issubset(target_uses):
                errors.append(
                    f"Blueprint target {target} must not encode every any_of route node as \\uses"
                )
                break
        if validation.schema_version == 2:
            refuted_uses = sorted(
                node
                for node in target_uses
                if node in validation.claims and validation.claims[node].state == "refuted"
            )
            if refuted_uses:
                errors.append(
                    f"Blueprint target {target} must not use refuted claim(s): "
                    + ", ".join(refuted_uses)
                )


def _validate_certificates(
    index: BlueprintIndex, ledger_path: Path, errors: list[str]
) -> None:
    ledger = _ledger_nodes(ledger_path, errors)
    certificate_declarations = {
        declaration for _node, declaration in CERTIFICATES.values()
    }
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
            declarations.extend(
                entry.strip() for entry in match.group(1).split(",") if entry.strip()
            )
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
    validation = _validate_routes(
        blueprint / "route-composition.yaml", blueprint_index, root, errors
    )
    _validate_or_targets(validation, blueprint_index, errors)
    _validate_certificates(blueprint_index, ledger, errors)
    return errors, {
        "files": blueprint_index.file_count,
        "labels": len(blueprint_index.labels),
        "routes": validation.route_count,
        "schema_version": validation.schema_version,
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
        f"1 Blueprint schema v{summary['schema_version']}, "
        f"{summary['files']} chapter file(s), "
        f"{summary['labels']} labels, {summary['routes']} active routes. 0 error(s)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
