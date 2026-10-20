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
import tempfile
import threading
import time

import atlas
import statement_snapshot
import vendor_lock

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
# Vendored third-party libraries (formalization/vendor/README.md): module root -> source directory.
VENDOR_ROOTS = {
    "LevyStochCalc": "formalization/vendor/LevyStochCalc",
    "BrownianMotion": "formalization/vendor/BrownianMotion",
    "MathFin": "formalization/vendor/MathFin",
    "KolmogorovExtension4": "formalization/vendor/KolmogorovExtension4",
}
# The synchronized BrownianMotion sources have no accepted upstream holes. Keep the exact
# allowlist mechanism so every new hole or dependent declaration fails the vendor audit.
VENDOR_UPSTREAM_SORRY: set[str] = set()


def vendor_module_path(name: str) -> Path | None:
    """The module path of a vendored source file, or None outside the vendored roots."""
    for module_root, directory in VENDOR_ROOTS.items():
        if name.startswith(directory + "/"):
            relative = Path(name).relative_to(directory)
            if relative.parts[0] == module_root:
                return relative.with_suffix("")
    return None


def is_vendor_module(module: str) -> bool:
    return module.split(".")[0] in VENDOR_ROOTS


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
        elif (vendored := vendor_module_path(name)) is not None:
            relative = vendored
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


# Text reports of `#print axioms`: anchored at a line start, the name is everything up to the
# last quote on that line before the verdict, so primes, generated suffixes and spaces inside
# `«…»` are kept; Lean may break the line between a long name and its verdict.
TEXT_REPORT = re.compile(r"(?m)^'([^\r\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
TEXT_MARKER = re.compile(r"depends on axioms:|does not depend on any axioms")
# Structured reports emitted by the generated audits below: one JSON object per line.
JSON_PREFIX = "AXIOM_REPORT "


def axiom_reports(output: str, *, structured: bool = False) -> tuple[list[tuple[str, list[str]]], list[str]]:
    """All axiom reports in `output`, failing closed on any report that cannot be parsed exactly.

    Generated audits emit JSON lines (`structured`); research audits use `#print axioms`, whose
    text is parsed only when every verdict marker belongs to a line-anchored report. A name
    containing a line break, or any other unparsed report, is an error rather than being skipped.
    """
    reports, errors = [], []
    if structured:
        for line in output.splitlines():
            if not line.startswith(JSON_PREFIX):
                continue
            try:
                item = json.loads(line[len(JSON_PREFIX):])
                name, axioms = item["name"], item["axioms"]
                if not isinstance(name, str) or not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms):
                    raise ValueError
            except (ValueError, KeyError, TypeError):
                errors.append(f"unparsed structured axiom report: {line[:200]}")
                continue
            reports.append((name, sorted(axioms)))
        if TEXT_MARKER.search(output):
            errors.append("unstructured axiom report in a structured audit")
        return reports, errors
    for match in TEXT_REPORT.finditer(output):
        reports.append((match.group(1), sorted(filter(None, (s.strip() for s in (match.group(2) or "").split(","))))))
    markers = len(TEXT_MARKER.findall(output))
    if markers != len(reports):
        errors.append(f"unparsed axiom report: {markers} verdicts, {len(reports)} parsed")
    return reports, errors


def reported_names(output: str, *, structured: bool = False) -> set[str]:
    return {name for name, _ in axiom_reports(output, structured=structured)[0]}


def parse_axioms(output: str, expected: set[str], *, structured: bool = False) -> tuple[dict[str, list[str]], list[str]]:
    found, errors = axiom_reports(output, structured=structured)
    reports = {}
    for name, axioms in found:
        if name in reports:
            errors.append(f"duplicate axiom report: {name}")
        reports[name] = axioms
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
    let report := Lean.Json.mkObj [("name", Lean.Json.str text),
      ("axioms", Lean.toJson (axioms.toList.map Lean.Name.toString))]
    Lean.logInfo m!"AXIOM_REPORT {{report.compress}}"
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
        _, errors = parse_axioms(output, reported_names(output))
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
                      "research/audits", *VENDOR_ROOTS.values()]:
        paths.extend((root / directory).rglob("*.lean"))
    return sorted(str(p.relative_to(root)) for p in paths
                  if p.is_file() and str(p.relative_to(root)) not in live)


# Classical KLS specification gate (research/audits/KLS/Classical/README.md): its templates, pins and driver are
# Lean-scope inputs.
CLASSICAL_KLS_DIR = "research/audits/KLS/Classical"


def verification_snapshot(root: Path, *, lean_only: bool = False) -> dict:
    snapshot = atlas.source_snapshot(root)
    if lean_only:
        # Bind Lean evidence to proof inputs and their tooling, not prose or ledger status.
        inputs = {"formalization/lean-toolchain", "formalization/lakefile.toml",
                  "formalization/lake-manifest.json", "research/verify.py", "research/atlas.py",
                  "research/cache_mathlib.py", "research/downstream.py"}
        files = {name: digest for name, digest in snapshot["files"].items()
                 if name in inputs or name.endswith(".lean") or name.startswith(CLASSICAL_KLS_DIR + "/")}
        snapshot = {**snapshot, "files": files, "sha256": atlas.digest(files)}
    return snapshot


def library_axiom_audit_code(modules: list[str]) -> str:
    """Audit actual local declarations without relying on documentation inventories."""
    imports = "\n".join("import " + module for module in sorted(set(modules) | {"Lean"}))
    names = ", ".join(json.dumps(module) for module in modules)
    return imports + f'''
run_cmd do
  let env ← Lean.getEnv
  let modules : Array String := #[{names}]
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let localDecl := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!.toString
      | none => (`FunctionalInequalities).isPrefixOf name ||
          (`solutions).isPrefixOf name || (`examples).isPrefixOf name
    if !localDecl then continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    let rendered := String.intercalate ", " (axioms.toList.map Lean.Name.toString)
    let report := Lean.Json.mkObj [("name", Lean.Json.str name.toString),
      ("axioms", Lean.toJson (axioms.toList.map Lean.Name.toString))]
    Lean.logInfo m!"AXIOM_REPORT {{report.compress}}"
    unless axioms.all (allowed.contains ·) do
      throwError "{{name}}: unexpected axioms [{{rendered}}]"
  if count == 0 then throwError "No local declarations audited"
  Lean.logInfo m!"Audited {{count}} local declarations."
'''


def vendor_axiom_audit_code(modules: list[str], upstream_sorry: set[str] = VENDOR_UPSTREAM_SORRY) -> str:
    """Audit every vendored declaration, isolating the exact listed upstream `sorry` ones."""
    imports = "\n".join("import " + module for module in sorted(set(modules) | {"Lean"}))
    names = ", ".join(json.dumps(module) for module in modules)
    roots = ", ".join("`" + root for root in VENDOR_ROOTS)
    listed = ", ".join(json.dumps(name) for name in sorted(upstream_sorry))
    return imports + f'''
run_cmd do
  let env ← Lean.getEnv
  let modules : Array String := #[{names}]
  let roots : Array Lean.Name := #[{roots}]
  let listed : Array Lean.Name := (#[{listed}] : Array String).map String.toName
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in listed do
    unless (env.find? name).isSome do
      throwError "Listed upstream sorry declaration not found: {{name}}"
  let mut count : Nat := 0
  let mut seenListed : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    let vendored := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!.toString
      | none => roots.any (·.isPrefixOf name)
    if !vendored then continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    let rendered := String.intercalate ", " (axioms.toList.map Lean.Name.toString)
    if listed.contains name then
      seenListed := seenListed.push name
      unless axioms.contains `sorryAx && axioms.all (fun a => allowed.contains a || a == `sorryAx) do
        throwError "{{name}}: listed upstream sorry declaration has axioms [{{rendered}}]"
    else
      unless axioms.all (allowed.contains ·) do
        throwError "{{name}}: unexpected axioms [{{rendered}}]"
  if count == 0 then throwError "No vendored declarations audited"
  -- Each listed name must be an audited vendored declaration, not a same-named import.
  for name in listed do
    unless seenListed.contains name do
      throwError "Listed upstream sorry declaration is not a vendored declaration: {{name}}"
  unless seenListed.size == listed.size do
    throwError "Listed upstream sorry declarations audited {{seenListed.size}} times, expected {{listed.size}}"
  Lean.logInfo m!"Audited {{count}} vendored declarations; {{listed.size}} listed upstream sorry declarations are isolated."
'''


def run_logged_command(command: list[str], *, cwd: Path, logfile: Path, env: dict,
                       code: str | None = None, interval: float = 30,
                       progress=None) -> subprocess.CompletedProcess:
    """Keep complete child logs on disk and report progress while the child is alive."""
    started = time.monotonic()
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as source, \
            logfile.open("w", encoding="utf-8") as log:
        if code is not None:
            source.write(code)
            source.seek(0)
        process = subprocess.Popen(command, cwd=cwd, stdin=source if code is not None else None,
                                   text=True, stdout=log, stderr=subprocess.STDOUT, env=env)
        try:
            while True:
                try:
                    returncode = process.wait(timeout=interval)
                    break
                except subprocess.TimeoutExpired:
                    if progress is not None:
                        with logfile.open("rb") as stream:
                            stream.seek(max(0, logfile.stat().st_size - 2048))
                            lines = stream.read().decode("utf-8", errors="replace").splitlines()
                        tail = lines[-1] if lines else "(no output yet)"
                        tail = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", tail)
                        tail = "".join(c for c in tail if c.isprintable())[-500:]
                        progress({"seconds": round(time.monotonic() - started, 1),
                                  "log_bytes": logfile.stat().st_size,
                                  "free_disk_bytes": shutil.disk_usage(cwd).free,
                                  "last_output": tail})
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
    return subprocess.CompletedProcess(command, returncode)


def run_verification(root: Path, *, lean_only: bool = False, no_kernel_replay: bool = False) -> int:
    if no_kernel_replay and not lean_only:
        raise ValueError("--no-kernel-replay requires --lean-only")
    started = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    artifact = Path("build/verification") / started
    output_dir = root / artifact
    output_dir.mkdir(parents=True, exist_ok=False)
    before = verification_snapshot(root, lean_only=lean_only)
    report = {"version": 1, "started_utc": started, "artifact": str(artifact / "report.json"),
              "snapshot": before, "scope": "lean-only" if lean_only else "full",
              "status": "failed", "gates": [], "errors": [],
              "trust_scope": "Local source build and local-module kernel replay, including the vendored libraries; pinned third-party compiled imports (Mathlib and its dependencies) are trusted. No fresh replay, external checker or isolated rebuild."}
    if no_kernel_replay:
        report.update(kernel_replay="skipped", replayed_modules=[])
        report["trust_scope"] = (
            "Lean source build and strict axiom audits, including the vendored libraries; "
            "local-module kernel replay was not run remotely and is covered by the full local receipt. "
            "Pinned third-party compiled imports (Mathlib and its dependencies) are trusted. "
            "No fresh replay, external checker or isolated rebuild.")
    progress_lock = threading.Lock()
    active = {}

    def write_progress(status="running"):
        # Called with progress_lock held: audit clients run concurrently.
        state = {"version": 1, "status": status, "started_utc": started,
                 "snapshot_sha256": before["sha256"], "scope": report["scope"],
                 "active": active, "completed_gates": report["gates"],
                 "errors": report["errors"]}
        pending = output_dir / "progress.tmp"
        pending.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n")
        pending.replace(output_dir / "progress.json")

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
        with progress_lock:
            active[name] = {"seconds": 0, "log": str(artifact / logfile.name)}
            write_progress()

        def heartbeat(metrics):
            with progress_lock:
                active[name].update(metrics)
                write_progress()
            print(f"Checking {name}: {metrics['seconds']:.0f}s elapsed, "
                  f"{metrics['log_bytes']} log bytes, "
                  f"{metrics['free_disk_bytes'] / (1024 ** 3):.1f} GiB free. "
                  f"Last output: {metrics['last_output']}", flush=True)

        process = run_logged_command(command, cwd=cwd, logfile=logfile, env=env,
                                     code=code, progress=heartbeat)
        seconds = round(time.monotonic() - start, 3)
        with progress_lock:
            report["gates"].append({"name": name, "command": command, "cwd": str(cwd.relative_to(root)),
                                    "exit_code": process.returncode, "seconds": seconds,
                                    "log": str(artifact / logfile.name)})
            active.pop(name)
            write_progress()
        print(f"Checked {name}: exit {process.returncode}, {seconds:.1f}s.", flush=True)
        if process.returncode:
            raise RuntimeError(f"{name} failed; see {artifact / logfile.name}")
        return logfile.read_text(encoding="utf-8")

    def internal_gate(name: str, errors: list[str], details: str) -> None:
        logfile = artifact / (name + ".log")
        (root / logfile).write_text(details + "\n" + "\n".join(errors))
        with progress_lock:
            report["gates"].append({"name": name, "exit_code": int(bool(errors)), "log": str(logfile)})
            write_progress()
        if errors:
            raise RuntimeError("\n".join(errors))

    try:
        hidden = undiscovered_lean_sources(root, before)
        internal_gate("source-discovery", [f"Lean source missing from snapshot: {p}" for p in hidden],
                      "Checked production and audit directories against the source snapshot")
        if not lean_only:
            derived, errors = atlas.build_atlas(root, snapshot=before)
            internal_gate("atlas-ledger-blueprint", errors, "Structural and task metadata checks")
            (output_dir / "atlas.json").write_text(json.dumps(derived, ensure_ascii=False, indent=2) + "\n")
            # Offline provenance of the vendored libraries (formalization/vendor/README.md).
            report["vendor_lock"], errors = vendor_lock.check_lock(root, set(VENDOR_ROOTS))
            internal_gate("vendor-provenance-lock", errors,
                          "Checked vendored files, port.patch and upstream hashes against vendor-lock.json")
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
        classical = output_dir / "classical-kls"
        run("classical-kls", [sys.executable, str(root / CLASSICAL_KLS_DIR / "check.py"), "--root", str(root),
                              "--lean", lean, "--lean-path", checked_path, "--out", str(classical)])
        report["classical_kls"] = json.loads((classical / "summary.json").read_text(encoding="utf-8"))
        vendored = [m for m in replay["modules"] if is_vendor_module(m)]
        code = vendor_axiom_audit_code(vendored)
        (output_dir / "VendorAudit.lean").write_text(code)
        output = run("vendor-axiom-audit", [lean, "--stdin"], cwd=formalization,
                     code=code, lean_path=checked_path)
        report["vendor"] = {"modules": len(vendored), "upstream_sorry": sorted(VENDOR_UPSTREAM_SORRY),
                            "summary": output.strip().splitlines()[-1] if output.strip() else ""}
        # Every project-local declaration, registered or not (public, private and generated), in
        # both modes: kernel replay alone accepts `sorryAx`, and the vendor allowlist does not
        # extend to local declarations. No local declaration is excluded, including `KLS.kls`.
        code = library_axiom_audit_code([m for m in replay["modules"] if not is_vendor_module(m)])
        (output_dir / "LocalDeclarationAudit.lean").write_text(code)
        output = run("local-declaration-audit", [lean, "--stdin"], cwd=formalization,
                     code=code, lean_path=checked_path)
        local_reports, errors = parse_axioms(output, reported_names(output, structured=True),
                                             structured=True)
        if not local_reports:
            errors.append("No local declaration axiom reports")
        report["local_declarations_audited"] = len(local_reports)
        report["excluded_open_targets"] = []
        if errors:
            raise RuntimeError("\n".join(errors))
        if lean_only:
            report["axioms"] = local_reports
        else:
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
            reports, errors = parse_axioms(output, declarations, structured=True)
            report["axioms"] = reports
            if errors:
                raise RuntimeError("\n".join(errors))
        if not no_kernel_replay:
            output = run("leanchecker", [str(Path(toolchain) / "bin/leanchecker"), "--verbose", "FunctionalInequalities", "solutions", "examples", *VENDOR_ROOTS],
                         cwd=formalization, lean_path=os.pathsep.join(paths))
            replayed = sorted(set(re.findall(r"(?m)^replaying (\S+)\s*$", output)))
            expected_modules = set(replay["modules"])
            if expected_modules != set(replayed):
                raise RuntimeError(f"checker coverage differs from current sources; missing={sorted(expected_modules-set(replayed))}, extra={sorted(set(replayed)-expected_modules)}")
            report["replayed_modules"] = replayed
        report["status"] = "passed"
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
        report["errors"].append(str(exc))
    after = verification_snapshot(root, lean_only=lean_only)
    if after["sha256"] != before["sha256"]:
        report["status"] = "failed"
        report["errors"].append("Sources changed during verification; rerun on a coherent snapshot.")
        report["after_snapshot"] = after
    serialized = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    (output_dir / "report.json").write_text(serialized)
    latest = root / ("build/verification/latest-lean.json" if lean_only else "build/verification/latest.json")
    pending = latest.with_suffix(".tmp")
    pending.write_text(serialized)
    pending.replace(latest)
    with progress_lock:
        write_progress(report["status"])
    print(f"Verification {report['status']}: {artifact / 'report.json'}", flush=True)
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=atlas.ROOT)
    parser.add_argument("--lean-only", action="store_true",
                        help="build, strictly audit and replay Lean; leave documentation/metadata checks local")
    parser.add_argument("--no-kernel-replay", action="store_true",
                        help="skip local-module kernel replay for remote CI; requires --lean-only")
    args = parser.parse_args()
    if args.no_kernel_replay and not args.lean_only:
        parser.error("--no-kernel-replay requires --lean-only")
    raise SystemExit(run_verification(args.root.resolve(), lean_only=args.lean_only,
                                     no_kernel_replay=args.no_kernel_replay))
