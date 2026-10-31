"""Classical KLS specification gate.

The Mathlib-only specification and its client are pinned templates (`config.json`). The gate compiles both freshly, checks
the four axiom reports, replays both runtime modules in the kernel, and requires each of three false-statement mutations
of the specification to compile while the unchanged client is rejected by an elaboration error.

    python3 research/audits/KLS/Classical/check.py --root ROOT --lean LEAN --lean-path PATH --out DIR

`research/verify.py` supplies the filtered fresh view as `--lean-path`. Nothing outside `--out` is written.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FORBIDDEN = re.compile(
    r"(?<![\w.])(?:sorry|admit|axiom|opaque|unsafe|partial|implemented_by|extern|native_decide|"
    r"run_cmd|run_tac|run_elab|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize)(?![\w'])"
    r"|#eval|#exit|debug\.skipKernelTC")
# Every import directive of the module grammar `[public] [meta] import [all] M`; modifiers never
# hide an edge from the allowlists below. Applied to comment- and string-stripped code.
IMPORT = re.compile(r"^[ \t]*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(\S+)", re.M)
IMPORT_FAILURE = re.compile(r"unknown module prefix|could not resolve import|object file .* does not exist|unknown package|"
                            r"failed to read file|No such file or directory")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strip_comments_and_strings(source: str) -> str:
    """Remove nested block comments, line comments and string literals, keeping line structure."""
    out, i, depth, n = [], 0, 0, len(source)
    while i < n:
        if depth:
            if source.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif source.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
        elif source.startswith("--", i):
            while i < n and source[i] != "\n":
                i += 1
        elif source[i] == '"':
            i += 1
            while i < n and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(out)


def specification_guard(source: str) -> list[str]:
    code = strip_comments_and_strings(source)
    imports = IMPORT.findall(code)
    if not imports or any(not name.startswith("Mathlib.") for name in imports):
        raise ValueError("The specification must import Mathlib only")
    if re.search(r"\b(?:FunctionalInequalities|Solutions|solutions)\b", code):
        raise ValueError("The specification names a project declaration")
    if match := FORBIDDEN.search(code):
        raise ValueError(f"Forbidden token in the specification: {match.group(0)}")
    return imports


def client_guard(source: str, specification_module: str, required_reports: list[str]) -> list[str]:
    code = strip_comments_and_strings(source)
    imports = IMPORT.findall(code)
    allowed = lambda name: name in {specification_module, "Lean", "FunctionalInequalities"} or name.startswith("FunctionalInequalities.")
    if specification_module not in imports or any(not allowed(name) for name in imports):
        raise ValueError("The client may import only the specification, project modules and Lean")
    if match := FORBIDDEN.search(code):
        raise ValueError(f"Forbidden token in the client: {match.group(0)}")
    missing = [name for name in required_reports
               if not re.search(r"^#print axioms\s+" + re.escape(name.rsplit(".", 1)[-1] if name.startswith("SecondIndependentReview.") else name) + r"\s*$", code, re.M)]
    if missing:
        raise ValueError(f"The client does not print the required axiom reports: {missing}")
    return imports


def check_pins(config: dict, here: Path = HERE) -> dict[str, bytes]:
    data = {}
    for role, template in config["templates"].items():
        content = (here / template["path"]).read_bytes()
        if sha(content) != template["sha256"]:
            raise ValueError(f"{template['path']} differs from its reviewed pin; review it and update config.json explicitly")
        data[role] = content
    return data


def apply_mutation(specification: str, mutation: dict) -> str:
    if specification.count(mutation["old"]) != 1:
        raise ValueError(f"Mutation anchor must occur exactly once: {mutation['name']}")
    mutated = specification.replace(mutation["old"], mutation["new"])
    if mutated == specification:
        raise ValueError(f"Mutation does not change the specification: {mutation['name']}")
    return mutated


def load_verify(root: Path):
    """The repository's own axiom-report parser (`research/verify.py`); this gate keeps no second parser."""
    research = str(root / "research")
    if research not in sys.path:
        sys.path.insert(0, research)
    import verify
    return verify


def axiom_reports(output: str, expected: list[str], verify) -> tuple[dict[str, list[str]], list[str]]:
    """`verify.parse_axioms` (missing, duplicate, nonstandard), plus: the reported names are exactly the expected ones."""
    found = verify.reported_names(output)
    reports, errors = verify.parse_axioms(output, set(expected))
    errors += [f"unexpected axiom report: {name}" for name in sorted(found - set(expected))]
    return reports, errors


ERROR_KINDS = {"type-mismatch": r"Type mismatch", "application-type-mismatch": r"Application type mismatch",
               "unsolved-goals": r"unsolved goals",
               "change-not-defeq": r"'change' tactic failed, pattern(?:\n.*)*?\nis not definitionally equal to target"}
EXCLUDED_FAILURE = re.compile(
    r"linter|warning|unexpected token|expected token|unknown module prefix|could not resolve import|object file .* does not exist|"
    r"unknown package|No such file or directory|failed to read file|heartbeats|deterministic\) timeout|maximum recursion depth|"
    r"[Ss]tack overflow|out of memory|PANIC|unknown (?:identifier|constant)", re.I)


def rejected_by_client(output: str, returncode: int, client_file: str, expected_kind: str) -> bool:
    """A mutation counts as rejected only by the expected elaboration error located in the client file, and only when no
    linter/warning, syntax, import, unknown-name, tool or resource failure occurs anywhere in the output."""
    if returncode == 0 or EXCLUDED_FAILURE.search(output):
        return False
    return bool(re.search(re.escape(client_file) + r":\d+:\d+: error(?:\([\w.]+\))?: " + ERROR_KINDS[expected_kind], output))


def run(name, command, *, out: Path, cwd: Path, lean_path: list[str]) -> subprocess.CompletedProcess:
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(LEAN_PATH=os.pathsep.join(lean_path), LEAN_NUM_THREADS="2")
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True, env=env)
    (out / f"{name}.log").write_text(f"$ {' '.join(command)}\n[exit {result.returncode}]\n{result.stdout}{result.stderr}")
    return result


def compile_module(name, directory: Path, module: str, *, out, cwd, lean, lean_path, emit=True):
    source = directory / f"{module}.lean"
    command = [lean, "-DwarningAsError=true", "-R", str(directory)]
    if emit:
        command += ["-o", str(directory / f"{module}.olean")]
    return run(name, command + [str(source)], out=out, cwd=cwd, lean_path=[str(directory), *lean_path])


def check(root: Path, lean: str, lean_path: list[str], out: Path) -> dict:
    verify = load_verify(root)
    config = json.loads((HERE / "config.json").read_text())
    pins = check_pins(config)
    spec_module, client_module = config["templates"]["specification"]["module"], config["templates"]["client"]["module"]
    specification, client = pins["specification"].decode(), pins["client"].decode()
    summary = {"templates": {role: t["sha256"] for role, t in config["templates"].items()},
               "specification_imports": specification_guard(specification),
               "client_imports": client_guard(client, spec_module, config["expected_axiom_reports"])}
    out.mkdir(parents=True, exist_ok=False)
    cwd = root / "formalization"
    runtime = out / "runtime"
    runtime.mkdir()
    (runtime / f"{spec_module}.lean").write_bytes(pins["specification"])
    (runtime / f"{client_module}.lean").write_bytes(pins["client"])
    for role, module in (("specification", spec_module), ("client", client_module)):
        result = compile_module(f"compile-{role}", runtime, module, out=out, cwd=cwd, lean=lean, lean_path=lean_path)
        if result.returncode:
            raise RuntimeError(f"{module} failed strict compilation")
    reports, errors = axiom_reports(result.stdout + result.stderr, config["expected_axiom_reports"], verify)
    if errors:
        raise RuntimeError("; ".join(errors))
    summary["axiom_reports"] = reports
    checker = str(Path(lean).with_name("leanchecker"))
    replay = run("kernel-replay", [checker, "--verbose", spec_module, client_module], out=out, cwd=cwd,
                 lean_path=[str(runtime), *lean_path])
    replayed = sorted(set(re.findall(r"(?m)^replaying (\S+)\s*$", replay.stdout + replay.stderr)))
    if replay.returncode or replayed != sorted([spec_module, client_module]):
        raise RuntimeError(f"Kernel replay must cover exactly both runtime modules; got {replayed}")
    summary["replayed_modules"] = replayed
    summary["rejected_mutations"] = []
    for mutation in config["mutations"]:
        directory = out / f"mutation-{mutation['name']}"
        directory.mkdir()
        (directory / f"{spec_module}.lean").write_text(apply_mutation(specification, mutation))
        (directory / f"{client_module}.lean").write_bytes(pins["client"])
        result = compile_module(f"mutation-{mutation['name']}-specification", directory, spec_module,
                                out=out, cwd=cwd, lean=lean, lean_path=lean_path)
        if result.returncode:
            raise RuntimeError(f"Mutated specification failed to compile: {mutation['name']}")
        result = compile_module(f"mutation-{mutation['name']}-client", directory, client_module,
                                out=out, cwd=cwd, lean=lean, lean_path=lean_path, emit=False)
        if not rejected_by_client(result.stdout + result.stderr, result.returncode, str(directory / f"{client_module}.lean"),
                                  mutation["expected_error"]):
            raise RuntimeError(f"Mutation was not rejected by a client elaboration error: {mutation['name']}")
        summary["rejected_mutations"].append(mutation["name"])
    summary["status"] = "passed"
    (out / "summary.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    return summary


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=HERE.parents[3])
    parser.add_argument("--lean", required=True)
    parser.add_argument("--lean-path", required=True, help="the search path, os.pathsep-separated")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        summary = check(args.root.resolve(), args.lean, args.lean_path.split(os.pathsep), args.out.resolve())
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"classical-kls failed: {exc}", file=sys.stderr)
        return 1
    print(f"classical-kls passed: {len(summary['axiom_reports'])} axiom reports, "
          f"{len(summary['replayed_modules'])} replayed modules, {len(summary['rejected_mutations'])} rejected mutations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
