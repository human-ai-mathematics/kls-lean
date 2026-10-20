#!/usr/bin/env python3
"""Compare the unchanged KLS endpoint or the separate OpenAI endpoint.

Uses the current local source and explicit trusted compiled dependency caches.
The macOS development mode is deliberately separate from Linux sandbox acceptance.
All generated files/logs/receipts go into a new ignored build directory.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ROOT / "research/audits/KLS/Comparator"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {
    "kls": ["FunctionalInequalities.KLS.kls"],
    "openai": ["KLSOpenAI.kls", "KLSOpenAI.of_conjecture"],
}


def validate_config(config: dict, target: str) -> None:
    """Do not accept a successful check of fewer/different theorems as this target."""
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        raise RuntimeError("comparison must use the tracked Challenge and Solution modules")
    names = config.get("theorem_names", [])
    if not isinstance(names, list) or sorted(names) != sorted(TARGETS[target]):
        raise RuntimeError(f"comparison must check exactly these declarations: {TARGETS[target]}")
    if set(config.get("permitted_axioms", [])) != AXIOMS or config.get("definition_names"):
        raise RuntimeError("comparison requires exactly the standard axioms and no definition holes")
    if config.get("enable_nanoda", False) is not False or config.get("external_kernels"):
        raise RuntimeError("this runner reports Lean-kernel checks only; external kernels need a separate setup")


def validate_axiom_reports(output: str, target: str, *, build_log: bool = False) -> dict[str, list[str]]:
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
    if build_log:
        # Lake also replays diagnostics from imported modules. Only the named
        # targets are this client's reports; Comparator audits their full closure.
        reports = [(name, used) for name, used in reports if name in TARGETS[target]]
    names = [name for name, _ in reports]
    if sorted(names) != sorted(TARGETS[target]):
        raise RuntimeError("axiom reports must cover every configured declaration exactly once")
    result = {}
    for name, printed in reports:
        used = {a.strip() for a in printed.split(",") if a.strip()}
        if not used <= AXIOMS:
            raise RuntimeError(f"{name}: unexpected solution axioms: {sorted(used - AXIOMS)}")
        result[name] = sorted(used)
    return result


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path: Path, data: dict) -> None:
    path.write_text(json.dumps(data, indent=2) + "\n")


def source_hashes(project: Path) -> dict:
    if project == ROOT:
        names = subprocess.check_output(
            ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
            cwd=ROOT).decode().split("\0")
        return {p: digest(ROOT / p) for p in names if p and (ROOT / p).is_file()}
    return {str(p.relative_to(project)): digest(p) for p in project.rglob("*")
            if p.is_file() and not any(x in {"build", ".lake", ".git", "__pycache__"}
                                       for x in p.relative_to(project).parts)}


def run(cmd: list[str], cwd: Path, env: dict, log: Path) -> None:
    print(f"Running {log.stem}; log: {log}", flush=True)
    started = last = time.monotonic()
    with log.open("w") as stream:
        process = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT)
        try:
            while process.poll() is None:
                time.sleep(1)
                if time.monotonic() - last >= 30:
                    print(f"{log.stem}: {int(time.monotonic()-started)}s, "
                          f"{log.stat().st_size} log bytes", flush=True)
                    last = time.monotonic()
        except BaseException:
            process.terminate()
            process.wait()
            raise
    if process.returncode:
        tail = log.read_text(errors="replace")[-2400:]
        raise RuntimeError(f"{log.stem} exited {process.returncode}:\n{tail}")


def check_solution_client(mode: str, out: Path, env: dict, target: str) -> dict | None:
    """Never execute a Solution preflight outside the advertised Linux sandbox."""
    if mode == "sandbox":
        return None
    run(["lake", "build", "Solution"], out, env, out / "solution-build.log")
    run(["lake", "env", "lean", "-DwarningAsError=true", "Solution.lean"],
        out, env, out / "strict-solution.log")
    return validate_axiom_reports((out / "strict-solution.log").read_text(), target)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=["kls", "openai"], default="kls")
    parser.add_argument("--mode", choices=["compile", "development", "sandbox"],
                        default="compile")
    parser.add_argument("--tools", type=Path, help="pinned Comparator checkout (built)")
    parser.add_argument("--bridge-root", type=Path, default=ROOT.parent / "KLS-OpenAI")
    args = parser.parse_args()
    pins = json.loads((INPUTS / "tools.json").read_text())
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LEAN", "LAKE", "ELAN_TOOLCHAIN", "COMPARATOR_"))}
    env.update({"LEAN_NUM_THREADS": "2", "MATHLIB_NO_CACHE_ON_UPDATE": "1",
                "GIT_OPTIONAL_LOCKS": "0", "GIT_TERMINAL_PROMPT": "0"})
    project = ROOT if args.target == "kls" else args.bridge_root.resolve()
    package = ROOT / "formalization" if args.target == "kls" else project
    templates = INPUTS if args.target == "kls" else project / "research/comparator"
    if (package / "lean-toolchain").read_text().strip() != pins["lean_toolchain"]:
        raise RuntimeError("project toolchain differs from the pinned Comparator toolchain")
    config = json.loads((templates / "config.json").read_text())
    validate_config(config, args.target)
    if args.target == "openai":
        upstream = json.loads((project / "UPSTREAM.json").read_text())
        if digest(project / upstream["local"]) != upstream["sha256"]:
            raise RuntimeError("OpenAI statement differs from its pinned source hash")
    tools = args.tools.resolve() if args.tools else None
    comparator = exporter = landrun = None
    if args.mode != "compile":
        if tools is None:
            raise RuntimeError("--tools must name the pinned, built Comparator checkout")
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=tools,
                                         env=env).decode().strip()
        if actual != pins["comparator"]["revision"]:
            raise RuntimeError("Comparator source revision does not match tools.json")
        if subprocess.check_output(["git", "status", "--porcelain"], cwd=tools, env=env):
            raise RuntimeError("Comparator checkout must have no local source changes")
        export_root = tools / ".lake/packages/lean4export"
        export_rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=export_root,
                                             env=env).decode().strip()
        if export_rev != pins["lean4export"]["revision"]:
            raise RuntimeError("lean4export revision does not match tools.json")
        if subprocess.check_output(["git", "status", "--porcelain"], cwd=export_root, env=env):
            raise RuntimeError("lean4export checkout must have no local source changes")
        comparator = tools / ".lake/build/bin/comparator"
        exporter = export_root / ".lake/build/bin/lean4export"
        if not comparator.is_file() or not exporter.is_file():
            raise RuntimeError("build the pinned tools with lake build lean4export comparator")
        if args.mode == "development":
            landrun = tools / "scripts/fake-landrun.sh"
        else:
            if platform.system() != "Linux" or not shutil.which("systemd-run"):
                raise RuntimeError("sandbox mode requires Linux, systemd-run and real Landrun")
            found = shutil.which("landrun")
            if not found:
                raise RuntimeError("sandbox mode requires real Landrun in PATH")
            landrun = Path(found)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = ROOT / "build/comparator" / f"{stamp}-{args.target}-{args.mode}"
    out.mkdir(parents=True)
    report = {"status": "RUNNING", "target": args.target, "mode": args.mode,
              "checked_declarations": TARGETS[args.target],
              "sandboxed": args.mode == "sandbox", "external_kernel": False,
              "source_kind": "local working tree; trusted dependency build caches",
              "pins": pins, "source_before": source_hashes(project),
              "root_source_before": source_hashes(ROOT),
              "inputs": {str(p): digest(p) for p in [Path(__file__), INPUTS / "tools.json",
                  templates / "config.json", templates / "Challenge.lean.in",
                  templates / "Solution.lean.in"]},
              "root_staged_entries_sha256": hashlib.sha256(subprocess.check_output(
                  ["git", "ls-files", "--stage", "-z"], cwd=ROOT, env=env)).hexdigest()}
    dump(out / "receipt.json", report)
    try:
        (out / "lean-toolchain").write_text(pins["lean_toolchain"] + "\n")
        for name in ["Challenge", "Solution"]:
            shutil.copyfile(templates / f"{name}.lean.in", out / f"{name}.lean")
        dump(out / "config.json", config)
        name = "functional-inequalities" if args.target == "kls" else "kls-openai-bridge"
        (out / "lakefile.toml").write_text(
            'name = "kls-comparator-fixture"\nversion = "0.1.0"\n'
            'defaultTargets = ["Solution"]\n\n[[require]]\n'
            f'name = "{name}"\npath = {json.dumps(str(package))}\n\n'
            '[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n')
        # Make inherited package paths explicit, retaining the existing exact pins.
        manifest = json.loads((package / "lake-manifest.json").read_text())
        packages = [{"type": "path", "name": f"«{name}»", "dir": str(package),
                     "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
                     "inherited": False, "scope": ""}]
        for entry in manifest["packages"]:
            pkg_name = entry["name"].strip("«»")
            directory = ((package / entry["dir"]).resolve() if entry["type"] == "path"
                         else (package / ".lake/packages" / pkg_name).resolve())
            if not directory.is_dir():
                raise RuntimeError(f"missing trusted dependency checkout: {pkg_name}")
            packages.append({"type": "path", "name": entry["name"], "dir": str(directory),
                             "configFile": entry["configFile"],
                             "manifestFile": entry.get("manifestFile", "lake-manifest.json"),
                             "inherited": True, "scope": entry.get("scope", "")})
        dump(out / "lake-manifest.json", {"version": "1.2.0", "packagesDir": ".lake/packages",
             "packages": packages, "name": "«kls-comparator-fixture»", "lakeDir": ".lake",
             "fixedToolchain": False})
        reports = check_solution_client(args.mode, out, env, args.target)
        if reports is not None:
            report["solution_axiom_reports"] = reports
        if args.mode != "compile":
            env.update({"COMPARATOR_LANDRUN": str(landrun),
                        "COMPARATOR_LEAN4EXPORT": str(exporter)})
            cmd = ["lake", "env", str(comparator), "config.json"]
            if args.mode == "sandbox":
                cmd = ["systemd-run", "--property=RestrictAddressFamilies=~AF_UNIX",
                       "--user", "--wait", "--pipe", "--collect", "-E", f"PATH={env['PATH']}",
                       "-E", f"COMPARATOR_LANDRUN={landrun}", "-E",
                       f"COMPARATOR_LEAN4EXPORT={exporter}", "--working-directory", str(out),
                       "--", *cmd]
            run(cmd, out, env, out / "comparator.log")
            log = (out / "comparator.log").read_text(errors="replace")
            if "Your solution is okay!" not in log or "Lean default kernel accepts the solution" not in log:
                raise RuntimeError("Comparator did not emit both required acceptance messages")
            if args.mode == "sandbox":
                # These reports come from Comparator's own sandboxed Solution build.
                report["solution_axiom_reports"] = validate_axiom_reports(log, args.target, build_log=True)
        report["status"] = {"compile": "COMPILED_CLIENT_ONLY",
                            "development": "COMPARATOR_PASSED_WITHOUT_SANDBOX",
                            "sandbox": "COMPARATOR_PASSED_LINUX_SANDBOX"}[args.mode]
    except BaseException as error:
        report.update(status="FAILED", error=str(error))
    report["source_after"] = source_hashes(project)
    report["root_source_after"] = source_hashes(ROOT)
    report["source_preserved"] = (report["source_before"] == report["source_after"] and
                                  report["root_source_before"] == report["root_source_after"])
    after_index = hashlib.sha256(subprocess.check_output(
        ["git", "ls-files", "--stage", "-z"], cwd=ROOT, env=env)).hexdigest()
    report["staging_preserved"] = after_index == report["root_staged_entries_sha256"]
    if not report["source_preserved"] or not report["staging_preserved"]:
        report.update(status="FAILED", error="source or staging changed during the check")
    report["logs"] = {p.name: digest(p) for p in out.glob("*.log")}
    dump(out / "receipt.json", report)
    print(report["status"], out / "receipt.json", flush=True)
    if report["status"] == "FAILED":
        print(report.get("error"), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
