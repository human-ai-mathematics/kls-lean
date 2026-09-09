#!/usr/bin/env python3
"""Compare elaborated local statement dependencies with a reviewed, versioned baseline."""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = Path("research/a-series/statement-snapshot")
ROOTS = ['FunctionalInequalities.KLS.Conjecture', 'FunctionalInequalities.KLS.LogConcave', 'FunctionalInequalities.Energy.LocalSlope.apply', 'FunctionalInequalities.Energy.LocalSlope.energy', 'FunctionalInequalities.Energy.LocalSlope.Admissible', 'FunctionalInequalities.Poincare.LocalSlope.Holds', 'FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant']


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot_code(root: Path) -> str:
    return ("import FunctionalInequalities.KLS.Statement\n" +
            (root / "research/StatementSnapshot.lean").read_text() +
            "\n#statement_snapshot " + " ".join(ROOTS) + "\n")


def parse_snapshot(output: str, root: Path) -> dict:
    data = json.loads(output)
    if set(data) != {"roots", "declarations", "external"} or data["roots"] != ROOTS:
        raise ValueError("statement snapshot: unexpected roots or output schema")
    if not data["declarations"] or len({d["name"] for d in data["declarations"]}) != len(data["declarations"]):
        raise ValueError("statement snapshot: missing or duplicate declarations")
    return {"version": 1,
            "toolchain": (root / "formalization/lean-toolchain").read_text().strip(),
            "lake_manifest_sha256": sha256(root / "formalization/lake-manifest.json"),
            "printing": {"pp.all": True, "pp.proofs": True, "pp.maxSteps": 1000000, "width": 100},
            **data}


def compare_snapshot(current: dict, golden: dict) -> list[str]:
    errors = []
    for key in ("version", "toolchain", "lake_manifest_sha256", "printing", "roots", "external"):
        if current.get(key) != golden.get(key):
            errors.append(f"statement snapshot changed: {key}")
    before = {d["name"]: d for d in golden["declarations"]}
    after = {d["name"]: d for d in current["declarations"]}
    for name in sorted(before.keys() | after.keys()):
        if before.get(name) != after.get(name):
            action = "added" if name not in before else "removed" if name not in after else "changed"
            errors.append(f"statement dependency {action}: {name}")
    return errors


def decision_record(root: Path, relative: str) -> dict:
    path = root / relative
    resolved = path.resolve()
    if (not resolved.is_relative_to((root / "research/decisions").resolve()) or
            resolved.suffix != ".md" or not resolved.is_file() or not resolved.read_text().strip()):
        raise ValueError("snapshot update requires a nonempty research/decisions/*.md record")
    return {"path": str(resolved.relative_to(root.resolve())), "sha256": sha256(resolved)}


def check_snapshot(root: Path, current: dict) -> list[str]:
    path = root / DIRECTORY / "golden.json"
    if not path.is_file():
        return ["statement snapshot golden is missing; create an explicit decision and baseline"]
    try:
        golden = json.loads(path.read_text())
        decision = golden["decision"]
        if decision_record(root, decision["path"]) != decision:
            return ["snapshot decision record changed; append a new record instead of rewriting it"]
        return compare_snapshot(current, golden)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        return [f"invalid statement golden: {exc}"]


def update_snapshot(root: Path, current: dict, decision: str) -> None:
    record = decision_record(root, decision)
    directory = root / DIRECTORY
    path = directory / "golden.json"
    if path.exists():
        old = json.loads(path.read_text())
        if old["decision"]["path"] == record["path"]:
            raise ValueError("a baseline update requires a new decision record")
    directory.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({**current, "decision": record}, indent=2, ensure_ascii=False) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "update"])
    parser.add_argument("--decision", help="new decision record required for an explicit baseline update")
    args = parser.parse_args()
    if args.command == "update" and not args.decision:
        parser.error("update requires --decision")
    try:
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        subprocess.run(["lake", "build", "FunctionalInequalities.KLS.Statement"],
                       cwd=ROOT / "formalization", env=env, check=True, stdout=sys.stderr)
        result = subprocess.run(["lake", "env", "lean", "--stdin"], input=snapshot_code(ROOT),
                                cwd=ROOT / "formalization", env=env, text=True, capture_output=True, check=True)
        current = parse_snapshot(result.stdout, ROOT)
        if args.command == "update":
            update_snapshot(ROOT, current, args.decision)
        else:
            errors = check_snapshot(ROOT, current)
            if errors:
                print("\n".join(errors), file=sys.stderr)
                path = ROOT / DIRECTORY / "golden.json"
                if path.exists():
                    golden = json.loads(path.read_text())
                    golden.pop("decision", None)
                    print("".join(difflib.unified_diff(
                        json.dumps(golden, indent=2, ensure_ascii=False).splitlines(True),
                        json.dumps(current, indent=2, ensure_ascii=False).splitlines(True),
                        fromfile="golden", tofile="current")), file=sys.stderr)
                return 1
        print(f"Statement snapshot: {len(current['declarations'])} local declarations; {args.command} passed.")
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as exc:
        print(f"statement snapshot: {exc}", file=sys.stderr)
        if isinstance(exc, subprocess.CalledProcessError):
            print(exc.stdout or "", exc.stderr or "", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
