#!/usr/bin/env python3
"""Compare the unchanged KLS endpoint, the separate OpenAI endpoint or the Palomar project.

The judge is the toolchain-bundled `lake comparator` of the pinned Lean toolchain
(`research/audits/KLS/Comparator/bundled-judge.json`); its exporter (`leanexport`) and kernel
(`leanchecker`) come from the same toolchain. The external Comparator v4.33.0 pin in `tools.json`
is the historical judge of receipts made before the Lean v4.35 migration and is not used here.
Uses the current local source and explicit trusted compiled dependency caches. The macOS
development mode (`--inadvisably-no-sandbox`) is deliberately separate from Linux `bwrap`
sandbox acceptance. All generated files/logs/receipts go into a new ignored build directory.
Palomar's own full preflight is independent of this runner and is not replaced by it.
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
import tomllib
from pathlib import Path

import lean_header

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ROOT / "research/audits/KLS/Comparator"
JUDGE = INPUTS / "bundled-judge.json"
# Historical external Comparator v4.33.0 + lean4export pin; recorded in receipts, never the judge.
HISTORICAL_TOOLS = INPUTS / "tools.json"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = {
    "kls": ["FunctionalInequalities.KLS.kls"],
    "openai": ["KLSOpenAI.kls", "KLSOpenAI.of_conjecture"],
    "palomar": ["KLSOpenAI.kls"],
}
# Palomar forces NanoDa; its committed configuration must say so and name no other kernel.
NANODA_TARGETS = {"palomar"}
PALOMAR_CONFIG_KEYS = {"challenge_module", "solution_module", "theorem_names",
                       "definition_names", "permitted_axioms", "enable_nanoda"}
# `lake comparator` covers these with a tmpfs inside `bwrap` (Lake/CLI/Check.lean,
# `buildSandboxArgs`); only the fixture, the toolchain prefix and Lake's home are bound back.
SANDBOX_COVERED = (Path("/home"), Path("/root"), Path("/run/user"), Path("/tmp"))
SANDBOX_WARNING = "WARNING: Sandbox disabled, this run is not trustworthy."
LEAN_VERSION = re.compile(r"Lean \(version ([0-9][^,\s)]*)")
TOOLCHAIN = re.compile(r"^leanprover/lean4:v(\d+\.\d+\.\d+(?:-rc\d+)?)$")

# The exact module-system adaptation of the pinned upstream OpenAI model; UPSTREAM.json records
# the same steps under `transformation`, and the check below reverses them byte for byte.
MODEL_MODULE_HEADER = b"module\n\n"
MODEL_IMPORT = b"import Mathlib\n"
MODEL_PUBLIC_IMPORT = b"public import Mathlib\n"
MODEL_SECTION = (b"@[expose] public section\n", b"\n")
MODEL_NAMESPACE = b"namespace OAI\n"
MODEL_TRANSFORMATION = [
    "insert the line `module` followed by one blank line at the very top",
    "replace the line `import Mathlib` with `public import Mathlib`",
    "insert the line `@[expose] public section` followed by one blank line immediately before "
    "the line `namespace OAI`",
]
PLACEHOLDER = "TO_BE_COMPUTED_BY_INTEGRATOR"


def validate_config(config: dict, target: str) -> None:
    """Do not accept a successful check of fewer/different theorems as this target."""
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        raise RuntimeError("comparison must use the tracked Challenge and Solution modules")
    names = config.get("theorem_names", [])
    if not isinstance(names, list) or sorted(names) != sorted(TARGETS[target]):
        raise RuntimeError(f"comparison must check exactly these declarations: {TARGETS[target]}")
    if set(config.get("permitted_axioms", [])) != AXIOMS or config.get("definition_names"):
        raise RuntimeError("comparison requires exactly the standard axioms and no definition holes")
    if target in NANODA_TARGETS:
        if set(config) != PALOMAR_CONFIG_KEYS:
            raise RuntimeError("the Palomar configuration must have exactly the keys "
                               f"{sorted(PALOMAR_CONFIG_KEYS)}")
        if config["enable_nanoda"] is not True or config["definition_names"] != []:
            raise RuntimeError("the Palomar configuration must register NanoDa and list no definition holes")
    elif config.get("enable_nanoda", False) is not False or config.get("external_kernels"):
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


def validate_comparator_log(log: str, mode: str, *, nanoda: bool) -> None:
    """Require the bundled judge's own acceptance lines (Lake/CLI/Check.lean) for this mode."""
    required = ["Your solution is okay!", "Lean default kernel accepts the solution"]
    if nanoda:
        required.append("nanoda kernel accepts the solution")
    missing = [line for line in required if line not in log]
    if missing:
        raise RuntimeError(f"lake comparator did not emit the required acceptance messages: {missing}")
    if (SANDBOX_WARNING in log) != (mode == "development"):
        raise RuntimeError("lake comparator sandbox state differs from the requested mode")


def adapt_upstream_model(upstream: bytes) -> bytes:
    """Apply exactly MODEL_TRANSFORMATION to the pinned upstream model bytes."""
    lines = upstream.splitlines(keepends=True)
    if (lines.count(MODEL_IMPORT) != 1 or MODEL_PUBLIC_IMPORT in lines
            or lines.count(MODEL_NAMESPACE) != 1):
        raise RuntimeError("upstream model must have exactly one `import Mathlib` and one `namespace OAI` line")
    adapted = [MODEL_MODULE_HEADER]
    for line in lines:
        if line == MODEL_NAMESPACE:
            adapted.extend(MODEL_SECTION)
        adapted.append(MODEL_PUBLIC_IMPORT if line == MODEL_IMPORT else line)
    return b"".join(adapted)


def restore_upstream_model(local: bytes) -> bytes:
    """Reverse MODEL_TRANSFORMATION; reject a local file that is not exactly upstream + adaptation."""
    if not local.startswith(MODEL_MODULE_HEADER):
        raise RuntimeError("local OpenAI model does not start with the recorded module header")
    lines = local[len(MODEL_MODULE_HEADER):].splitlines(keepends=True)
    if lines.count(MODEL_PUBLIC_IMPORT) != 1 or lines.count(MODEL_NAMESPACE) != 1:
        raise RuntimeError("local OpenAI model lacks the recorded public import or namespace line")
    index = lines.index(MODEL_NAMESPACE)
    if index < 2 or tuple(lines[index - 2:index]) != MODEL_SECTION:
        raise RuntimeError("local OpenAI model lacks the recorded exposed public section")
    del lines[index - 2:index]
    upstream = b"".join(MODEL_IMPORT if line == MODEL_PUBLIC_IMPORT else line for line in lines)
    if adapt_upstream_model(upstream) != local:
        raise RuntimeError("local OpenAI model is not exactly the upstream file plus the recorded adaptation")
    return upstream


def check_upstream_model(bridge: Path) -> dict:
    """The local model must be the pinned upstream bytes plus exactly the recorded adaptation."""
    upstream = json.loads((bridge / "UPSTREAM.json").read_text())
    if upstream.get("transformation") != MODEL_TRANSFORMATION:
        raise RuntimeError("UPSTREAM.json transformation differs from the one this runner reverses")
    for key in ("sha256", "local_sha256"):
        if not re.fullmatch(r"[0-9a-f]{64}", str(upstream.get(key))):
            raise RuntimeError(f"UPSTREAM.json {key} is not a recorded SHA-256 (still {PLACEHOLDER!r}?)")
    local = (bridge / upstream["local"]).read_bytes()
    if hashlib.sha256(local).hexdigest() != upstream["local_sha256"]:
        raise RuntimeError("OpenAI statement differs from its recorded local hash")
    original = restore_upstream_model(local)
    if hashlib.sha256(original).hexdigest() != upstream["sha256"]:
        raise RuntimeError("OpenAI statement differs from its pinned source hash")
    return {"revision": upstream["revision"], "source": upstream["source"],
            "upstream_sha256": upstream["sha256"], "local_sha256": upstream["local_sha256"]}


def header_guards(challenge: str, solution: str) -> dict:
    """Palomar: a module Challenge importing only Mathlib, and a module Solution."""
    try:
        challenge_header = lean_header.parse_header(challenge)
        solution_header = lean_header.parse_header(solution)
    except lean_header.HeaderError as exc:
        raise RuntimeError(f"unparsable Challenge/Solution header: {exc}") from exc
    if not challenge_header.is_module or not solution_header.is_module:
        raise RuntimeError("Palomar Challenge and Solution must be `module` files")
    imports = challenge_header.imports
    if not imports or any(item.all or not (item.module == "Mathlib" or item.module.startswith("Mathlib."))
                          for item in imports):
        raise RuntimeError("the Palomar Challenge may import only Mathlib modules (no `import all`)")
    return {"challenge_imports": [item.directive() for item in imports],
            "solution_imports": [item.directive() for item in solution_header.imports]}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def capture(paths: list[Path]) -> dict[Path, bytes]:
    """Read each input exactly once; every later hash, parse, check and staged copy uses these bytes."""
    return {path: path.read_bytes() for path in paths}


def stage(out: Path, name: str, data: bytes, recorded: str) -> None:
    """Write captured bytes; the staged file must carry the digest already recorded in the receipt."""
    target = out / name
    target.write_bytes(data)
    if sha(data) != recorded or digest(target) != recorded:
        raise RuntimeError(f"staged {name} differs from its recorded input digest")


def captured_drift(captured: dict[Path, bytes], recorded: dict[str, str],
                   root_snapshot: dict[str, str]) -> list[str]:
    """Captured repository inputs whose source-snapshot digest differs from the recorded one."""
    return sorted(str(path) for path in captured if path.is_relative_to(ROOT)
                  and root_snapshot.get(path.relative_to(ROOT).as_posix()) != recorded[str(path)])


# Generated fixture files the judge and the Solution client read.
FIXTURE_FILES = ("Challenge.lean", "Solution.lean", "config.json", "lakefile.toml",
                 "lake-manifest.json", "lean-toolchain")


def fixture_digests(out: Path) -> dict[str, str]:
    return {name: digest(out / name) for name in FIXTURE_FILES}


def check_fixture(out: Path, expected: dict[str, str]) -> None:
    """The fixture inputs at invocation time must be exactly the recorded ones."""
    changed = sorted(name for name, value in expected.items()
                     if not (out / name).is_file() or digest(out / name) != value)
    if changed:
        raise RuntimeError(f"judge inputs changed after they were recorded: {changed}")


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


def solution_axiom_client(target: str) -> str:
    """A generated NON-module client printing the configured axiom reports of `Solution`.

    Used when the committed Solution prints nothing itself. A non-module root imports every
    module at the private level (Lean v4.35 `processHeaderCore`), as before the migration.
    """
    return "import Solution\n\n" + "".join(f"#print axioms {name}\n" for name in TARGETS[target])


def check_solution_client(mode: str, out: Path, env: dict, target: str,
                          judge_inputs: dict[str, str] | None = None) -> dict | None:
    """Never execute a Solution preflight outside the advertised Linux sandbox.

    With `judge_inputs`, the generated client's digest is recorded there and every fixture
    input is checked against the recorded digests immediately before each invocation.
    """
    if mode == "sandbox":
        return None
    client = "Solution.lean"
    if target in NANODA_TARGETS:
        client = "SolutionAxioms.lean"
        data = solution_axiom_client(target).encode()
        (out / client).write_bytes(data)
        if judge_inputs is not None:
            judge_inputs[client] = sha(data)
    if judge_inputs is not None:
        check_fixture(out, judge_inputs)
    run(["lake", "build", "Solution"], out, env, out / "solution-build.log")
    if judge_inputs is not None:
        check_fixture(out, judge_inputs)
    run(["lake", "env", "lean", "-DwarningAsError=true", client],
        out, env, out / "strict-solution.log")
    return validate_axiom_reports((out / "strict-solution.log").read_text(), target)


def toolchain_version(declared: str) -> str:
    match = TOOLCHAIN.match(declared.strip())
    if not match:
        raise RuntimeError(f"unsupported lean-toolchain: {declared.strip()!r}")
    return match.group(1)


def bundled_toolchain(out: Path, env: dict, declared: str, *, nanoda: bool) -> dict:
    """Locate the pinned toolchain through the fixture's own `lean-toolchain`; record its tools."""
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=out, env=env,
                                          text=True).strip())
    binary = prefix / "bin"
    version = subprocess.check_output([str(binary / "lean"), "--version"], cwd=out, env=env, text=True)
    found = LEAN_VERSION.search(version)
    if not found or found.group(1) != toolchain_version(declared):
        raise RuntimeError(f"toolchain at {prefix} is not {declared}: {version.strip()}")
    names = ["lake", "lean", "leanexport", "leanchecker"] + (["nanoda_bin"] if nanoda else [])
    missing = [name for name in names if not (binary / name).is_file()]
    if missing:
        raise RuntimeError(f"pinned toolchain lacks bundled tools: {missing}")
    githash = subprocess.check_output([str(binary / "lean"), "--githash"], cwd=out, env=env,
                                      text=True).strip()
    return {"prefix": str(prefix), "lean_version": found.group(1), "lean_githash": githash,
            "tool_sha256": {name: digest(binary / name) for name in names}}


def manifest_entry(entry: dict, base: Path, inherited: bool) -> dict:
    """The fixture's explicit path entry for one trusted, already materialised dependency."""
    pkg_name = entry["name"].strip("«»")
    if entry["type"] == "path":
        directory = (base / entry["dir"]).resolve()
    elif entry["type"] == "git":
        directory = (base / ".lake/packages" / pkg_name).resolve()
    else:
        raise RuntimeError(f"unsupported manifest entry type for {pkg_name}: {entry['type']}")
    if not directory.is_dir():
        raise RuntimeError(f"missing trusted dependency checkout: {pkg_name}")
    return {"type": "path", "name": entry["name"], "dir": str(directory),
            "configFile": entry["configFile"],
            "manifestFile": entry.get("manifestFile", "lake-manifest.json"),
            "inherited": inherited, "scope": entry.get("scope", "")}


def palomar_project(project: Path, bridge: Path, lakefile: bytes,
                    manifest_bytes: bytes) -> tuple[list[tuple[str, Path]], list[dict], dict]:
    """Requires, libraries and manifest of the committed Palomar project, checked for consistency.

    `lakefile` and `manifest_bytes` are the captured bytes recorded in the receipt.
    """
    config = tomllib.loads(lakefile.decode("utf-8"))
    manifest = json.loads(manifest_bytes)
    bridge_manifest = json.loads((bridge / "lake-manifest.json").read_text())
    bridge_revs = {e["name"].strip("«»"): e.get("rev") for e in bridge_manifest["packages"]
                   if e["type"] == "git"}
    entries = {e["name"].strip("«»"): e for e in manifest["packages"]}
    requires = []
    for require in config.get("require", []):
        name = require["name"]
        entry = entries.get(name)
        if entry is None or entry.get("inherited"):
            raise RuntimeError(f"Palomar requirement {name} is not a direct entry of its lake-manifest.json")
        if "path" in require:
            directory = (project / require["path"]).resolve()
            if entry["type"] != "path" or (project / entry["dir"]).resolve() != directory:
                raise RuntimeError(f"Palomar path requirement {name} differs from its manifest entry")
        elif "git" in require:
            directory = (project / ".lake/packages" / name).resolve()
            if entry["type"] != "git":
                raise RuntimeError(f"Palomar Git requirement {name} differs from its manifest entry")
        else:
            raise RuntimeError(f"unsupported Palomar requirement source: {name}")
        requires.append((name, directory))
    if bridge.resolve() not in {directory for _, directory in requires}:
        raise RuntimeError("the Palomar project must require the OpenAI bridge package by path")
    for name, entry in entries.items():
        if entry["type"] == "git" and bridge_revs.get(name) != entry.get("rev"):
            raise RuntimeError(f"Palomar pin of {name} differs from the OpenAI bridge manifest")
    libraries = config.get("lean_lib", [])
    if sorted(lib.get("name", "") for lib in libraries) != ["Challenge", "Solution"]:
        raise RuntimeError("the Palomar project must define exactly the Challenge and Solution libraries")
    for lib in libraries:
        if set(lib) - {"name", "roots", "leanOptions"} or lib.get("roots", [lib["name"]]) != [lib["name"]]:
            raise RuntimeError(f"unsupported Palomar lean_lib configuration: {lib['name']}")
    return requires, libraries, manifest


def toml_value(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, str)):
        return json.dumps(value)
    if isinstance(value, list):
        return "[" + ", ".join(toml_value(v) for v in value) + "]"
    if isinstance(value, dict):
        return "{" + ", ".join(f"{k} = {toml_value(v)}" for k, v in value.items()) + "}"
    raise RuntimeError(f"unsupported lakefile value: {value!r}")


def check_sandbox_reach(paths: list[Path]) -> None:
    """`bwrap` covers the home directories; dependencies there would be invisible to the build."""
    covered = [str(p) for p in paths if any(p == c or c in p.parents for c in SANDBOX_COVERED)]
    if covered:
        raise RuntimeError("sandbox mode needs dependencies outside /home, /root, /run/user and /tmp, "
                           f"which lake comparator's bwrap sandbox covers: {covered}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=sorted(TARGETS), default="kls")
    parser.add_argument("--mode", choices=["compile", "development", "sandbox"],
                        default="compile")
    parser.add_argument("--tools", type=Path,
                        help="historical external Comparator v4.33 checkout; rejected since the "
                             "Lean v4.35 migration (the judge is the toolchain-bundled lake comparator)")
    parser.add_argument("--bridge-root", type=Path, default=ROOT / "integrations/openai")
    parser.add_argument("--palomar-root", type=Path, default=ROOT / "integrations/palomar")
    args = parser.parse_args()
    if args.tools is not None:
        raise RuntimeError("--tools names the historical Comparator v4.33 checkout (tools.json); "
                           "the current judge is the toolchain-bundled `lake comparator`")
    judge_bytes = JUDGE.read_bytes()
    pins = json.loads(judge_bytes)
    if pins.get("judge") != "lake comparator":
        raise RuntimeError("bundled-judge.json must name the toolchain-bundled `lake comparator`")
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LEAN", "LAKE", "ELAN_TOOLCHAIN", "COMPARATOR_"))}
    env.update({"LEAN_NUM_THREADS": "2", "MATHLIB_NO_CACHE_ON_UPDATE": "1",
                "GIT_OPTIONAL_LOCKS": "0", "GIT_TERMINAL_PROMPT": "0"})
    bridge = args.bridge_root.resolve()
    nanoda = args.target in NANODA_TARGETS
    if args.target == "kls":
        project, package, templates = ROOT, ROOT / "formalization", INPUTS
        sources = {"Challenge": templates / "Challenge.lean.in", "Solution": templates / "Solution.lean.in"}
        config_path = templates / "config.json"
        toolchain_owners = [package]
    elif args.target == "openai":
        project = package = bridge
        templates = project / "research/comparator"
        sources = {"Challenge": templates / "Challenge.lean.in", "Solution": templates / "Solution.lean.in"}
        config_path = templates / "config.json"
        toolchain_owners = [package, ROOT / "formalization"]
    else:
        # The committed module files are staged unchanged; only the fixture's own Lake
        # configuration is regenerated, with absolute paths to the same pinned dependencies.
        project = package = args.palomar_root.resolve()
        sources = {"Challenge": project / "Challenge.lean", "Solution": project / "Solution.lean"}
        config_path = project / "comparator.json"
        toolchain_owners = [package, bridge, ROOT / "formalization"]
    # Every input below is read once; hashes, checks, parsing and staging use these bytes.
    manifest_path = package / "lake-manifest.json"
    captured_paths = [config_path, *sources.values(), manifest_path,
                      *(owner / "lean-toolchain" for owner in toolchain_owners)]
    if args.target == "palomar":
        captured_paths.append(project / "lakefile.toml")
    captured = capture(list(dict.fromkeys(captured_paths)))
    for owner in toolchain_owners:
        if captured[owner / "lean-toolchain"].decode("utf-8").strip() != pins["lean_toolchain"]:
            raise RuntimeError(f"{owner} toolchain differs from the pinned bundled-judge toolchain")
    config = json.loads(captured[config_path])
    validate_config(config, args.target)
    model = check_upstream_model(bridge) if args.target in {"openai", "palomar"} else None
    headers = None
    if args.target == "palomar":
        headers = header_guards(captured[sources["Challenge"]].decode("utf-8"),
                                captured[sources["Solution"]].decode("utf-8"))
        requires, libraries, manifest = palomar_project(project, bridge, captured[project / "lakefile.toml"],
                                                        captured[manifest_path])
    else:
        manifest = json.loads(captured[manifest_path])
    if args.mode == "sandbox" and platform.system() != "Linux":
        raise RuntimeError("sandbox mode requires Linux and bubblewrap (lake comparator's bwrap sandbox)")
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = ROOT / "build/comparator" / f"{stamp}-{args.target}-{args.mode}"
    out.mkdir(parents=True)
    recorded_inputs = {str(Path(__file__)): digest(Path(__file__)),
                       str(Path(lean_header.__file__)): digest(Path(lean_header.__file__)),
                       str(JUDGE): sha(judge_bytes)}
    recorded_inputs.update({str(path): sha(data) for path, data in captured.items()})
    report = {"status": "RUNNING", "target": args.target, "mode": args.mode,
              "checked_declarations": TARGETS[args.target],
              "judge": "toolchain-bundled lake comparator",
              "sandboxed": args.mode == "sandbox", "external_kernel": nanoda,
              "external_kernels": ["nanoda"] if nanoda else [],
              "source_kind": "local working tree; trusted dependency build caches",
              "trust_scope": ("Toolchain-bundled lake comparator: statement and definition-closure "
                              "comparison, permitted-axiom check and Lean kernel (leanchecker) replay of "
                              "the solution export"
                              + ("; NanoDa as registered by the configuration" if nanoda
                                 else "; no external kernel")
                              + ". Development mode runs without the bwrap sandbox. Precompiled path "
                              "dependencies and pinned third-party caches are trusted. This is not "
                              "Palomar's preflight."),
              "pins": pins,
              "historical_tools_pin": {"path": str(HISTORICAL_TOOLS.relative_to(ROOT)),
                                       "sha256": digest(HISTORICAL_TOOLS), "used": False},
              "source_before": source_hashes(project),
              "root_source_before": source_hashes(ROOT),
              "inputs": recorded_inputs,
              "root_staged_entries_sha256": hashlib.sha256(subprocess.check_output(
                  ["git", "ls-files", "--stage", "-z"], cwd=ROOT, env=env)).hexdigest()}
    if model is not None:
        report["openai_model"] = model
    if headers is not None:
        report["module_headers"] = headers
    dump(out / "receipt.json", report)
    try:
        # The captured bytes must also be the ones the source snapshot saw.
        drifted = captured_drift(captured, recorded_inputs, report["root_source_before"])
        if drifted:
            raise RuntimeError(f"inputs changed between capture and the source snapshot: {drifted}")
        (out / "lean-toolchain").write_text(pins["lean_toolchain"] + "\n")
        # Stage the captured bytes; each staged file must match the digest recorded above.
        for name, source in sources.items():
            stage(out, f"{name}.lean", captured[source], recorded_inputs[str(source)])
        stage(out, "config.json", captured[config_path], recorded_inputs[str(config_path)])
        if args.target == "palomar":
            lakefile = ['name = "kls-comparator-fixture"', 'version = "0.1.0"',
                        'defaultTargets = ["Solution"]', ""]
            for name, directory in requires:
                lakefile += ["[[require]]", f"name = {json.dumps(name)}",
                             f"path = {json.dumps(str(directory))}", ""]
            for lib in libraries:
                lakefile += (["[[lean_lib]]"] + [f"{key} = {toml_value(value)}" for key, value in lib.items()]
                             + [""])
            (out / "lakefile.toml").write_text("\n".join(lakefile))
            # Make the committed manifest's exact pins explicit as absolute paths.
            packages = [manifest_entry(entry, project, bool(entry.get("inherited")))
                        for entry in manifest["packages"]]
        else:
            name = "functional-inequalities" if args.target == "kls" else "kls-openai-bridge"
            (out / "lakefile.toml").write_text(
                'name = "kls-comparator-fixture"\nversion = "0.1.0"\n'
                'defaultTargets = ["Solution"]\n\n[[require]]\n'
                f'name = "{name}"\npath = {json.dumps(str(package))}\n\n'
                '[[lean_lib]]\nname = "Challenge"\n\n[[lean_lib]]\nname = "Solution"\n')
            # Make inherited package paths explicit, retaining the existing exact pins.
            packages = [{"type": "path", "name": f"«{name}»", "dir": str(package),
                         "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json",
                         "inherited": False, "scope": ""}]
            packages += [manifest_entry(entry, package, True) for entry in manifest["packages"]]
        # `lake comparator` refuses a project without a manifest; keep the source's format version.
        dump(out / "lake-manifest.json", {"version": manifest["version"], "packagesDir": ".lake/packages",
             "packages": packages, "name": "«kls-comparator-fixture»", "lakeDir": ".lake",
             "fixedToolchain": False})
        # The generated fixture inputs given to the judge, bound at staging and rechecked at
        # every invocation.
        report["judge_inputs"] = judge_inputs = fixture_digests(out)
        dump(out / "receipt.json", report)
        toolchain = bundled_toolchain(out, env, pins["lean_toolchain"], nanoda=nanoda)
        report["toolchain"] = toolchain
        binary = Path(toolchain["prefix"]) / "bin"
        # The bundled tools, including `nanoda_bin` when registered, resolve to this toolchain.
        env["PATH"] = str(binary) + os.pathsep + env.get("PATH", "")
        reports = check_solution_client(args.mode, out, env, args.target, judge_inputs)
        if reports is not None:
            report["solution_axiom_reports"] = reports
        if args.mode != "compile":
            cmd = [str(binary / "lake"), "comparator", "--config", "config.json"]
            if args.mode == "development":
                cmd.append("--inadvisably-no-sandbox")
            else:
                bwrap = shutil.which("bwrap", path=env["PATH"])
                if not bwrap:
                    raise RuntimeError("sandbox mode requires bubblewrap (`bwrap`) on PATH")
                report["sandbox"] = {"bwrap": bwrap, "sha256": digest(Path(bwrap))}
                check_sandbox_reach([Path(p["dir"]) for p in packages])
            check_fixture(out, judge_inputs)
            run(cmd, out, env, out / "comparator.log")
            check_fixture(out, judge_inputs)
            log = (out / "comparator.log").read_text(errors="replace")
            validate_comparator_log(log, args.mode, nanoda=nanoda)
            if args.mode == "sandbox" and args.target not in NANODA_TARGETS:
                # These reports come from the judge's own sandboxed Solution build, whose
                # tracked template prints them; the Palomar Solution prints none.
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
    except (RuntimeError, OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
