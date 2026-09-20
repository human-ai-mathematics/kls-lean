#!/usr/bin/env python3
"""Run local acceptance gates and bind their evidence to the actual working-tree contents."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

import atlas
import statement_snapshot

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATEMENT_CHECKS = {"Solutions.StatementChecks." + name for name in (
    'constant_energy',
    'constant_admissible',
    'zero_dimension_covariance',
    'zero_dimension_bound',
    'localSlope_id',
    'ambient_dirac_identity_energy',
    'borell_innerRegular',
    'borell_rpow_iSup',
    'borell_mul_iSup',
    'isotropic_fields',
    'zero_dimension_isotropic',
    'borel_logconcavity_fields',
    'zero_dimension_innerMeasure',
    'isoperimetric_inverse',
    'zero_dimension_isoperimetry',
    'ambient_dirac_isoperimetry',
    'isoperimetric_boundary_fields',
    'conditional_zero_dimension_excluded',
    'conditional_domain_fields',
    'conditional_bad_fiber',
    'affine_constant_unfold',
    'affine_test_fields',
    'affine_energy_integral',
    'zero_dimension_affine_constant',
    'ambient_dirac_affine_constant',
)}


def replay_sources(snapshot: dict) -> dict[str, str]:
    """Map every in-scope current module to its source, independently of build caches."""
    result = {}
    for name, source_hash in sorted(snapshot["files"].items()):
        if source_hash is None or not name.endswith(".lean"):
            continue
        if name == "formalization/FunctionalInequalities.lean" or name.startswith("formalization/FunctionalInequalities/"):
            relative = Path(name).relative_to("formalization").with_suffix("")
        elif name.startswith(("solutions/", "examples/")):
            relative = Path(name).with_suffix("")
        else:
            continue
        module = ".".join(relative.parts)
        result[module] = name
    if not result:
        raise RuntimeError("No current Lean source modules to replay")
    return result


def build_replay_inputs(root: Path, snapshot: dict, destination: Path, run) -> dict:
    """Build the exact replay scope, including modules outside default import closures."""
    targets = ["+" + module for module in replay_sources(snapshot)]
    run("lake-build-replay-scope", ["lake", "build", *targets], cwd=root / "formalization")
    return prepare_replay(root, snapshot, destination)


def prepare_replay(root: Path, snapshot: dict, destination: Path) -> dict:
    """Copy only current source modules, leaving obsolete development artifacts untouched."""
    if destination.exists() and any(destination.iterdir()):
        raise RuntimeError("The checked module view must be empty before copying current modules")
    compiled = root / "formalization/.lake/build/lib/lean"
    sources = replay_sources(snapshot)
    hashes = {}
    for module, name in sources.items():
        relative = Path(*module.split("."))
        for suffix in [".olean", ".olean.server", ".olean.private"]:
            source = compiled / relative.with_suffix(suffix)
            if not source.is_file():
                if suffix == ".olean":
                    raise RuntimeError(f"Current source {name} has no built module: {source}")
                continue
            target = destination / source.relative_to(compiled)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
            hashes[str(source.relative_to(compiled))] = hashlib.sha256(target.read_bytes()).hexdigest()
    return {"modules": list(sources), "compiled_sha256": hashes}


def parse_axioms(output: str, expected: set[str]) -> tuple[dict[str, list[str]], list[str]]:
    reports = {}
    errors = []
    pattern = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
    for match in pattern.finditer(output):
        name = match.group(1)
        if name in reports:
            errors.append(f"duplicate axiom report: {name}")
        reports[name] = sorted(filter(None, (s.strip() for s in (match.group(2) or "").split(","))))
    for name in sorted(expected - reports.keys()):
        errors.append(f"missing axiom report: {name}")
    for name, axioms in reports.items():
        unexpected = set(axioms) - STANDARD_AXIOMS
        if unexpected:
            errors.append(f"{name}: unexpected axioms {sorted(unexpected)}")
    return reports, errors


def axiom_audit_code(declarations: set[str]) -> str:
    """Inspect exact environment names, including compiler-generated auxiliary declarations.

    Use the same transitive collector as Lean's `#print axioms`, without elaborating generated
    names as source identifiers. Missing names must fail before collection: collectAxioms alone
    can return an empty list for a name absent from the environment.
    """
    names = ",\n    ".join(json.dumps(name, ensure_ascii=False) for name in sorted(declarations))
    return f'''run_cmd do
  let names : Array String := #[{names}]
  let env ← Lean.getEnv
  for text in names do
    let name := text.toName
    unless (env.find? name).isSome do
      throwError "Axiom audit declaration not found: {{text}}"
    let axioms ← Lean.collectAxioms name
    let rendered := String.intercalate ", " (axioms.toList.map Lean.Name.toString)
    Lean.logInfo m!"'{{text}}' depends on axioms: [{{rendered}}]"
'''


def check_research_audits(root: Path, snapshot: dict, run, *, lean: str, lean_path: str) -> list[str]:
    """Strictly elaborate every live audit source, including nonignored new files.

    Each file is a separate client: concatenating imports would mask missing dependencies.
    These checks do not register candidate statements as certificates or extend kernel replay.
    """
    paths = sorted(name for name, source_hash in snapshot["files"].items()
                   if source_hash is not None and name.startswith("research/audits/")
                   and name.endswith(".lean"))

    def check(item):
        index, name = item
        output = run(f"research-audit-{index:03d}",
                     [lean, "-DwarningAsError=true", str(root / name)],
                     cwd=root / "formalization", lean_path=lean_path)
        names = set(re.findall(r"'([^']+)' depends on axioms:", output))
        _, errors = parse_axioms(output, names)
        if errors:
            raise RuntimeError(f"{name}: " + "; ".join(errors))
        return name

    with ThreadPoolExecutor(max_workers=3) as workers:
        return list(workers.map(check, enumerate(paths)))


def undiscovered_lean_sources(root: Path, snapshot: dict) -> list[str]:
    """Reject on-disk production/audit sources hidden from the Git-aware snapshot."""
    live = {name for name, digest in snapshot["files"].items() if digest is not None}
    paths = [root / "formalization/FunctionalInequalities.lean"]
    for directory in ["formalization/FunctionalInequalities", "solutions", "examples",
                      "research/audits"]:
        paths.extend((root / directory).rglob("*.lean"))
    return sorted(str(p.relative_to(root)) for p in paths
                  if p.is_file() and str(p.relative_to(root)) not in live)


def run_verification(root: Path) -> int:
    started = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    artifact = Path("build/verification") / started
    output_dir = root / artifact
    output_dir.mkdir(parents=True, exist_ok=False)
    before = atlas.source_snapshot(root)
    report = {"version": 1, "started_utc": started, "artifact": str(artifact / "report.json"),
              "snapshot": before, "status": "failed", "gates": [], "errors": [],
              "trust_scope": "Local source build and local-module kernel replay; pinned third-party compiled imports are trusted. No fresh replay, external checker or isolated rebuild."}

    def run(name: str, command: list[str], *, cwd: Path = root, code: str | None = None,
            lean_path: str | None = None) -> str:
        print(f"Checking {name}...", flush=True)
        start = time.monotonic()
        env = {**os.environ, "LEAN_NUM_THREADS": "2"}
        # Ignore a search path inherited from another Lean project. Lake creates the correct one.
        env.pop("LEAN_PATH", None)
        if lean_path is not None:
            env["LEAN_PATH"] = lean_path
        logfile = output_dir / (name + ".log")
        with logfile.open("w", encoding="utf-8") as log:
            process = subprocess.run(command, cwd=cwd, input=code, text=True,
                                     stdout=log, stderr=subprocess.STDOUT, env=env)
        report["gates"].append({"name": name, "command": command, "cwd": str(cwd.relative_to(root)),
                                "exit_code": process.returncode, "seconds": round(time.monotonic()-start, 3),
                                "log": str(artifact / logfile.name)})
        if process.returncode:
            raise RuntimeError(f"{name} failed; see {artifact / logfile.name}")
        return logfile.read_text(encoding="utf-8")

    def internal_gate(name: str, errors: list[str], details: str) -> None:
        logfile = artifact / (name + ".log")
        (root / logfile).write_text(details + "\n" + "\n".join(errors))
        report["gates"].append({"name": name, "exit_code": int(bool(errors)), "log": str(logfile)})
        if errors:
            raise RuntimeError("\n".join(errors))

    try:
        hidden = undiscovered_lean_sources(root, before)
        internal_gate("source-discovery", [f"Lean source missing from snapshot: {p}" for p in hidden],
                      "Checked production and audit directories against the source snapshot")
        derived, errors = atlas.build_atlas(root, snapshot=before)
        internal_gate("atlas-ledger-blueprint", errors, "Structural and task metadata checks")
        (output_dir / "atlas.json").write_text(json.dumps(derived, ensure_ascii=False, indent=2) + "\n")
        run("python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "research/tests", "-p", "test_*.py"])
        run("lake-build", ["lake", "build"], cwd=root / "formalization")
        view = output_dir / "local-olean"
        replay = build_replay_inputs(root, before, view, run)
        report["replay_inputs"] = replay
        formalization = root / "formalization"
        search_path = run("lake-search-path", ["lake", "env", "printenv", "LEAN_PATH"], cwd=formalization).strip()
        toolchain = run("lean-toolchain", ["lake", "env", "lean", "--print-prefix"], cwd=formalization).strip()
        compiled = formalization / ".lake/build/lib/lean"
        paths = search_path.split(os.pathsep)
        matches = [i for i, p in enumerate(paths) if (formalization / p).resolve() == compiled.resolve()]
        if len(matches) != 1:
            raise RuntimeError("Lake search path must contain exactly one local compiled-library directory")
        paths[matches[0]] = str(view)
        checked_path = os.pathsep.join(paths)
        lean = str(Path(toolchain) / "bin/lean")
        report["checked_lean_path"] = paths
        report["research_audits"] = check_research_audits(
            root, before, run, lean=lean, lean_path=checked_path)
        code = statement_snapshot.snapshot_code(root)
        (output_dir / "StatementSnapshot.lean").write_text(code)
        output = run("statement-snapshot", [lean, "--stdin"],
                     cwd=root / "formalization", code=code, lean_path=checked_path)
        statement = statement_snapshot.parse_snapshot(output, root)
        (output_dir / "statement-snapshot.json").write_text(json.dumps(statement, indent=2, ensure_ascii=False) + "\n")
        internal_gate("statement-golden", statement_snapshot.check_snapshot(root, statement),
                      f"Compared {len(statement['declarations'])} local declarations with the explicit baseline")
        report["statement_snapshot"] = {"local_declarations": len(statement["declarations"]),
                                        "external_leaves": len(statement["external"]),
                                        "golden_sha256": statement_snapshot.sha256(root / statement_snapshot.DIRECTORY / "golden.json")}
        imports = {"FunctionalInequalities", "solutions.StatementChecks"}
        imports.update(c["module"] for c in derived["certificates"].values())
        declarations = {d for n in derived["nodes"].values() for d in n["lean"]["declarations"]}
        declarations.update(c["declaration"] for c in derived["certificates"].values())
        declarations.update(d["name"] for d in statement["declarations"])
        declarations.update(STATEMENT_CHECKS)
        code = "\n".join("import " + m for m in sorted(imports)) + "\n"
        code += axiom_audit_code(declarations)
        code += "set_option pp.all true\n"
        code += "\n".join("#print " + c["declaration"] for c in derived["certificates"].values()) + "\n"
        (output_dir / "DeclarationAudit.lean").write_text(code)
        output = run("declaration-audit", [lean, "--stdin"], cwd=root / "formalization",
                     code=code, lean_path=checked_path)
        reports, errors = parse_axioms(output, declarations)
        report["axioms"] = reports
        if errors:
            raise RuntimeError("\n".join(errors))
        output = run("leanchecker", [str(Path(toolchain) / "bin/leanchecker"), "--verbose", "FunctionalInequalities", "solutions", "examples"],
                     cwd=formalization, lean_path=os.pathsep.join(paths))
        replayed = sorted(set(re.findall(r"(?m)^replaying (\S+)\s*$", output)))
        expected_modules = set(replay["modules"])
        if expected_modules != set(replayed):
            raise RuntimeError(f"checker coverage differs from current sources; missing={sorted(expected_modules-set(replayed))}, extra={sorted(set(replayed)-expected_modules)}")
        report["replayed_modules"] = replayed
        report["status"] = "passed"
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
        report["errors"].append(str(exc))
    after = atlas.source_snapshot(root)
    if after["sha256"] != before["sha256"]:
        report["status"] = "failed"
        report["errors"].append("Sources changed during verification; rerun on a coherent snapshot.")
        report["after_snapshot"] = after
    serialized = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    (output_dir / "report.json").write_text(serialized)
    latest = root / "build/verification/latest.json"
    pending = latest.with_suffix(".tmp")
    pending.write_text(serialized)
    pending.replace(latest)
    print(f"Verification {report['status']}: {artifact / 'report.json'}", flush=True)
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=atlas.ROOT)
    args = parser.parse_args()
    raise SystemExit(run_verification(args.root.resolve()))
