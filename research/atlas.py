#!/usr/bin/env python3
"""Derive a task atlas from Blueprint, route provenance and the certification ledger.

This is a scheduler input, not a proof checker. Read verification.md for the evidence boundary.
Only explicit task metadata classifies unformalized mathematics; prose is never parsed as proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import check_blueprint as blueprint
import check_ledger as ledger

ROOT = Path(__file__).resolve().parents[1]
MATHEMATICAL = {"definition", "theorem", "lemma", "corollary", "proposition",
                "conjecture", "assumption", "question", "obstruction"}
MATH_STATES = {"definition", "published", "local_argument", "conjectural", "refuted", "unknown"}
TASK_FIELDS = {"mathematics", "evidence", "assumptions", "priority", "note"}
INFRASTRUCTURE_STATES = {"available", "missing", "unchecked"}


def mathlib_revision(root: Path) -> str:
    manifest = load_json(root / "formalization/lake-manifest.json")
    return next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")


def validate_infrastructure(meta: Any, root: Path) -> list[str]:
    if not isinstance(meta, dict) or set(meta) != {"status", "mathlib_revision", "evidence", "gaps"}:
        return ["require status, mathlib_revision, evidence and gaps"]
    state = meta["status"]
    if state not in INFRASTRUCTURE_STATES:
        return ["unknown infrastructure status"]
    evidence, gaps = meta["evidence"], meta["gaps"]
    if not isinstance(evidence, list) or not isinstance(gaps, list) or not all(isinstance(g, str) and g.strip() for g in gaps):
        return ["evidence and gaps must be lists; gaps must name concrete missing interfaces"]
    if state == "unchecked":
        return [] if meta["mathlib_revision"] is None and not evidence and not gaps else ["unchecked must not assert assessed evidence or gaps"]
    errors = []
    if meta["mathlib_revision"] != mathlib_revision(root):
        errors.append("assessment is stale for the pinned Mathlib revision; reassess or mark unchecked")
    if not evidence:
        errors.append("assessed infrastructure requires source evidence")
    if (state == "missing") != bool(gaps):
        errors.append("missing requires concrete gaps; available requires no gaps")
    for item in evidence:
        if not isinstance(item, dict) or set(item) != {"path", "sha256"} or not isinstance(item["path"], str):
            errors.append("evidence requires a relative source path and sha256")
            continue
        path = root / item["path"]
        if Path(item["path"]).is_absolute() or not path.resolve().is_relative_to(root.resolve()) or not path.is_file():
            errors.append(f"missing or nonlocal infrastructure evidence: {item['path']}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            errors.append(f"stale infrastructure evidence: {item['path']}; reassess or mark unchecked")
    return errors


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False,
                                     separators=(",", ":")).encode()).hexdigest()


def source_snapshot(root: Path) -> dict[str, Any]:
    """Hash tracked and nonignored untracked sources, including deletions and dirty content."""
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"], cwd=root
    ).decode().split("\0")
    files = {}
    for name in sorted(set(filter(None, paths))):
        path = root / name
        files[name] = (hashlib.sha256(path.read_bytes()).hexdigest()
                       if path.is_file() else None)
    return {"sha256": digest(files), "files": files,
            "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root).decode().strip()}


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def commands(body: str, pattern: re.Pattern) -> list[str]:
    return sorted({s.strip() for match in pattern.finditer(body)
                   for s in match.group(1).split(",") if s.strip()})


def parse_nodes(root: Path) -> tuple[dict[str, dict], list[str]]:
    """Associate each immediately following proof with its statement, retaining proof edges."""
    nodes: dict[str, dict] = {}
    errors: list[str] = []
    for path in sorted((root / "formalization/blueprint/src/chapters").rglob("*.tex")):
        text = blueprint._strip_tex_comments(path.read_text(encoding="utf-8"))
        previous: str | None = None
        end = 0
        for match in blueprint.ENVIRONMENT.finditer(text):
            env, body = match.group("environment"), match.group("body")
            labels = blueprint.LABEL.findall(body)
            if env == "proof" and previous and not text[end:match.start()].strip():
                node = nodes[previous]
                node["proof_text"] = body.strip()
                node["dependencies"] = sorted(set(node["dependencies"]) | set(commands(body, blueprint.USES)))
                node["proof_leanok"] = bool(blueprint.LEAN_OK.search(body))
                previous = None
            elif env in MATHEMATICAL:
                if len(labels) != 1:
                    errors.append(f"{path.relative_to(root)}: {env} must have exactly one atlas label")
                    previous = None
                    continue
                name = labels[0].strip()
                if name in nodes:
                    errors.append(f"duplicate atlas node {name}")
                nodes[name] = {
                    "id": name, "kind": env,
                    "statement_ref": {"path": str(path.relative_to(root)), "label": name,
                                      "line": text.count("\n", 0, match.start()) + 1},
                    "statement_text": body.strip(), "proof_text": None,
                    "statement_sha256": digest(body.strip()),
                    "dependencies": commands(body, blueprint.USES),
                    "lean": {"declarations": commands(body, blueprint.LEAN),
                             "recorded": bool(blueprint.LEAN_OK.search(body)), "ledger_node": None},
                    "proof_leanok": False,
                    "statement_question": bool(re.search(r"\\notready\b", body)),
                }
                previous = name
            else:
                previous = None
            end = match.end()
    return nodes, errors


def cycle_errors(graph: dict[str, list[str]]) -> list[str]:
    errors, done, stack = [], set(), []

    def visit(name: str) -> None:
        if name in stack:
            errors.append("dependency cycle: " + " -> ".join(stack[stack.index(name):] + [name]))
            return
        if name in done:
            return
        stack.append(name)
        for dep in graph.get(name, []):
            visit(dep)
        stack.pop()
        done.add(name)

    for name in graph:
        visit(name)
    return errors


def certificate_map(root: Path) -> tuple[dict[str, dict], list[str]]:
    """Require exactly one explicit Blueprint mapping for every proved ledger certificate."""
    document = load_json(root / "research/a-series/ledger.yaml")
    nodes = {n["id"]: n for n in document["nodes"]}
    result, errors = {}, []
    for label, (node_id, declaration) in blueprint.CERTIFICATES.items():
        node = nodes.get(node_id)
        if node is None or node["status"] != "proved":
            errors.append(f"certificate {node_id}: missing proved ledger record")
            continue
        if node_id in result:
            errors.append(f"certificate {node_id}: duplicate mapping")
        result[node_id] = {"label": label, "declaration": declaration,
                           "module": node["lean_solution"][:-5].replace("/", ".")}
    for node in nodes.values():
        if node["status"] == "proved" and node["id"] not in result:
            errors.append(f"certificate {node['id']}: no axiom-audit mapping")
    return result, errors


def validate_tasks(tasks: Any, nodes: dict[str, dict], root: Path = ROOT) -> list[str]:
    errors = []
    if not isinstance(tasks, dict) or set(tasks) != {"version", "policy", "nodes"} or tasks.get("version") != 2:
        return ["tasks.json: expected version 2 with policy and nodes"]
    policy = tasks["policy"]
    if (not isinstance(policy, dict) or set(policy) != {"max_attempts", "on_exhaustion"}
            or type(policy["max_attempts"]) is not int or policy["max_attempts"] < 1
            or policy["on_exhaustion"] != "reclassify"):
        errors.append("tasks.policy: require positive max_attempts and on_exhaustion=reclassify")
    records = tasks["nodes"]
    if not isinstance(records, dict):
        return errors + ["tasks.nodes must be an object"]
    for name, meta in records.items():
        if name not in nodes:
            errors.append(f"task {name}: unknown mathematical node")
            continue
        required = TASK_FIELDS | ({"infrastructure"} if isinstance(meta, dict) and
            (meta.get("mathematics") in {"local_argument", "published"} or
             (meta.get("mathematics") == "definition" and "infrastructure" in meta)) else set())
        if not isinstance(meta, dict) or set(meta) != required:
            errors.append(f"task {name}: require exactly {sorted(required)}")
            continue
        if "infrastructure" in meta:
            errors.extend(f"task {name}: infrastructure: {e}" for e in validate_infrastructure(meta["infrastructure"], root))
        if meta["mathematics"] not in MATH_STATES:
            errors.append(f"task {name}: unknown mathematical state")
        if type(meta["priority"]) is not int or not 0 <= meta["priority"] <= 9:
            errors.append(f"task {name}: priority must be an integer from 0 to 9")
        if not isinstance(meta["note"], str) or not meta["note"].strip():
            errors.append(f"task {name}: missing scope note")
        evidence = meta["evidence"]
        if not isinstance(evidence, list) or not evidence or not all(isinstance(s, str) and s for s in evidence):
            errors.append(f"task {name}: missing evidence references")
        elif any(not ref.startswith("blueprint:") or ref[len("blueprint:"):] not in nodes for ref in evidence):
            errors.append(f"task {name}: evidence must reference an existing Blueprint mathematical node")
        assumptions = meta["assumptions"]
        if (not isinstance(assumptions, list) or not all(isinstance(s, str) for s in assumptions)
                or len(assumptions) != len(set(assumptions))):
            errors.append(f"task {name}: invalid assumptions")
            continue
        for dep in assumptions:
            if dep not in nodes[name]["dependencies"]:
                errors.append(f"task {name}: assumption {dep} is not a declared dependency")
            elif nodes[dep]["kind"] not in {"assumption", "question", "conjecture"}:
                errors.append(f"task {name}: {dep} is not an explicit assumption/question/conjecture")
    for name, node in nodes.items():
        if not node["lean"]["recorded"] and name not in records:
            errors.append(f"task {name}: unformalized mathematics requires explicit classification")
    return errors


def current_evidence(root: Path, snapshot: dict) -> dict:
    path = root / "build/verification/latest.json"
    if not path.exists():
        return {"current": False, "reason": "no verification report"}
    try:
        report = load_json(path)
        valid = report["status"] == "passed" and report["snapshot"]["sha256"] == snapshot["sha256"]
        return {"current": valid, "reason": "verified snapshot" if valid else "failed or stale verification",
                "report": report["artifact"]}
    except (OSError, ValueError, KeyError, TypeError):
        return {"current": False, "reason": "invalid verification report"}


def schedule(nodes: dict[str, dict], verified: bool) -> None:
    def inherited_assumptions(name: str, seen: set[str] | None = None) -> set[str]:
        seen = set() if seen is None else seen
        if name in seen:
            return set()
        seen.add(name)
        result = set(nodes[name]["task"]["assumptions"])
        for dep in nodes[name]["dependencies"]:
            result.update(inherited_assumptions(dep, seen))
        return {a for a in result if not nodes[a]["lean"]["recorded"]}

    for node in nodes.values():
        meta = node["task"]
        assumptions = set(meta["assumptions"])
        blockers = []
        for dep in node["dependencies"]:
            other = nodes[dep]
            if dep in assumptions:
                if not other["lean"]["declarations"]:
                    blockers.append({"node": dep, "reason": "assumption needs a Lean statement, not a proof"})
            elif not other["lean"]["recorded"]:
                blockers.append({"node": dep, "reason": "dependency not Lean-certified"})
            for premise in sorted(inherited_assumptions(dep) - assumptions):
                blockers.append({"node": premise, "reason": f"dependency {dep} retains this unproved premise"})
        state = meta["mathematics"]
        infrastructure = meta.get("infrastructure")
        infra_state = infrastructure["status"] if infrastructure else None
        if state == "refuted":
            action = "excluded"
        elif node["statement_question"]:
            action = "clarify_statement"
        elif state in {"conjectural", "unknown"}:
            action = "research" if state == "conjectural" else "review"
        elif node["lean"]["recorded"]:
            action = "complete" if verified else "verify_recorded"
        elif blockers:
            action = "blocked"
        elif infra_state == "missing":
            action = "develop_infrastructure"
        elif infra_state == "unchecked":
            action = "inspect_infrastructure"
        elif not verified:
            action = "verify_prerequisites"
        else:
            action = "formalize_conditional" if assumptions else "formalize"
        node["dispatch"] = {"action": action, "blockers": blockers,
                            "verification": "current" if verified else "required",
                            "infrastructure": infrastructure,
                            "retained_assumptions": sorted(assumptions)}


def build_atlas(root: Path = ROOT, *, snapshot: dict | None = None) -> tuple[dict, list[str]]:
    errors, _ = blueprint.check_blueprint(root=root)
    ledger_errors, _ = ledger.check_ledger(root=root)
    errors.extend(ledger_errors)
    nodes, parse_errors = parse_nodes(root)
    errors.extend(parse_errors)
    tasks = load_json(root / "research/tasks.json")
    errors.extend(validate_tasks(tasks, nodes, root))
    certificates, cert_errors = certificate_map(root)
    errors.extend(cert_errors)
    routes = load_json(root / "formalization/blueprint/route-composition.yaml")
    claims = {c["node"]: c for c in routes["claims"]}
    for name, node in nodes.items():
        for dep in node["dependencies"]:
            if dep not in nodes:
                errors.append(f"{name}: dependency {dep} is not a mathematical node")
        if node["lean"]["recorded"] and not node["lean"]["declarations"]:
            errors.append(f"{name}: leanok without a declaration")
        if node["lean"]["recorded"] and node["kind"] != "definition" and not node["proof_leanok"]:
            errors.append(f"{name}: certified theorem needs a matching proof leanok")
        node["task"] = tasks.get("nodes", {}).get(name, {
            "mathematics": "definition" if node["kind"] == "definition" else "local_argument",
            "evidence": ["lean:" + d for d in node["lean"]["declarations"]],
            "assumptions": [], "priority": 9, "note": "Certification annotation from Blueprint; validated separately."})
        node["provenance"] = claims.get(name)
        if name in claims and claims[name]["state"] == "refuted" and node["task"]["mathematics"] != "refuted":
            errors.append(f"{name}: refuted route claim cannot enter a proof queue")
    graph = {name: n["dependencies"] for name, n in nodes.items()}
    errors.extend(cycle_errors(graph))
    for node_id, cert in certificates.items():
        if cert["label"] in nodes:
            nodes[cert["label"]]["lean"]["ledger_node"] = node_id
    if errors:
        return {}, errors
    snapshot = snapshot if snapshot is not None else source_snapshot(root)
    evidence = current_evidence(root, snapshot)
    schedule(nodes, evidence["current"])
    for node in nodes.values():
        node["task_key"] = digest({"node": node["id"], "statement": node["statement_sha256"],
                                   "dependencies": node["dependencies"], "snapshot": snapshot["sha256"]})
    return {"version": 2, "snapshot": snapshot, "verification": evidence,
            "policy": tasks["policy"], "nodes": nodes, "sources": routes["sources"],
            "branches": routes["branches"], "targets": routes["targets"],
            "certificates": certificates}, []


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "export", "ready", "show", "diff"])
    parser.add_argument("node", nargs="?")
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--against", type=Path)
    args = parser.parse_args(argv)
    try:
        atlas, errors = build_atlas(args.root.resolve())
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"atlas: {exc}", file=sys.stderr)
        return 1
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    nodes = atlas["nodes"]
    if args.command == "check":
        print(f"Atlas: {len(nodes)} mathematical nodes, {len(atlas['certificates'])} certificates, no dependency cycles.")
    elif args.command == "export":
        output = args.output or args.root / "build/atlas.json"
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(atlas, indent=2, ensure_ascii=False) + "\n")
        print(output)
    elif args.command == "show":
        if args.node not in nodes:
            parser.error("show requires an existing mathematical node id")
        print(json.dumps(nodes[args.node], indent=2, ensure_ascii=False))
    elif args.command == "ready":
        print("Evidence: " + atlas["verification"]["reason"])
        for node in sorted(nodes.values(), key=lambda n: (n["task"]["priority"], n["id"])):
            action = node["dispatch"]["action"]
            if action != "complete":
                reasons = "; ".join(b["node"] + ": " + b["reason"] for b in node["dispatch"]["blockers"])
                infra = node["dispatch"]["infrastructure"]
                if infra and not node["lean"]["recorded"]:
                    detail = f"infrastructure {infra['status']}"
                    if infra["gaps"]:
                        detail += ": " + "; ".join(infra["gaps"])
                    reasons = "; ".join(filter(None, [reasons, detail]))
                print(f"{action:23} {node['id']}" + (f" — {reasons}" if reasons else ""))
    elif args.command == "diff":
        if args.against is None:
            parser.error("diff requires --against a previous exported atlas")
        previous = load_json(args.against)
        for name in sorted(set(previous["nodes"]) | set(nodes)):
            before, after = previous["nodes"].get(name), nodes.get(name)
            if before is None or after is None:
                print(f"{'added' if before is None else 'removed'}: {name}")
            else:
                changed = [key for key in ["statement_text", "proof_text", "dependencies", "task", "lean"]
                           if before.get(key) != after.get(key)]
                if changed:
                    print(f"{name}: {', '.join(changed)}")
        old_files, new_files = previous["snapshot"]["files"], atlas["snapshot"]["files"]
        for name in sorted(set(old_files) | set(new_files)):
            if old_files.get(name) != new_files.get(name):
                print(f"source changed: {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
