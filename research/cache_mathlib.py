#!/usr/bin/env python3
"""Fetch the pinned Mathlib import closure and reject incomplete compiled caches."""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess

from downstream import parse_imports

ROOT = Path(__file__).resolve().parents[1]


def project_sources(root: Path) -> list[Path]:
    paths = [root / "formalization/FunctionalInequalities.lean"]
    for directory in ("formalization/FunctionalInequalities", "formalization/vendor",
                      "solutions", "examples", "research/audits"):
        paths.extend((root / directory).rglob("*.lean"))
    return sorted(path for path in paths if path.is_file())


def mathlib_roots(root: Path) -> dict[str, list[str]]:
    """Keep the aggregate `Mathlib` import as well as dotted module imports."""
    result: dict[str, list[str]] = {}
    for path in project_sources(root):
        for module in parse_imports(path.read_text(encoding="utf-8")):
            if module == "Mathlib" or module.startswith("Mathlib."):
                result.setdefault(module, []).append(str(path.relative_to(root)))
    if not result:
        raise ValueError("No Mathlib imports found; refusing an unspecified cache request")
    return result


def required_modules(mathlib: Path, roots: list[str]) -> set[str]:
    pending = list(roots)
    seen: set[str] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = mathlib.joinpath(*module.split(".")).with_suffix(".lean")
        if not source.is_file():
            raise ValueError(f"Pinned Mathlib source is missing: {module}")
        pending.extend(name for name in parse_imports(source.read_text(encoding="utf-8"))
                       if name == "Mathlib" or name.startswith("Mathlib."))
    return seen


def check_cache(mathlib: Path, modules: set[str]) -> list[str]:
    compiled = mathlib / ".lake/build/lib/lean"
    return sorted(module for module in modules
                  if not compiled.joinpath(*module.split(".")).with_suffix(".olean").is_file())


def prepare_cache(root: Path, *, check_only: bool = False) -> int:
    roots = mathlib_roots(root)
    # The aggregate module already imports all dotted Mathlib modules.
    targets = ["Mathlib"] if "Mathlib" in roots else sorted(roots)
    print(f"Mathlib cache: {len(roots)} direct imports; targets: {', '.join(targets)}", flush=True)
    if "Mathlib" in roots:
        print(f"Aggregate Mathlib is required by {len(roots['Mathlib'])} source files.", flush=True)
    if not check_only:
        subprocess.run(["lake", "exe", "cache", "get", *targets],
                       cwd=root / "formalization", check=True)
    mathlib = root / "formalization/.lake/packages/mathlib"
    modules = required_modules(mathlib, targets)
    missing = check_cache(mathlib, modules)
    if missing:
        raise ValueError(f"Mathlib cache incomplete: {len(missing)} of {len(modules)} modules missing. "
                         "Refusing an accidental source rebuild. First missing modules: "
                         + ", ".join(missing[:20]))
    print(f"Mathlib cache complete: {len(modules)} required compiled modules found. "
          "Pinned third-party compiled imports remain trusted.", flush=True)
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true", help="check existing files without fetching")
    args = parser.parse_args()
    try:
        raise SystemExit(prepare_cache(args.root.resolve(), check_only=args.check))
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"Mathlib cache preparation failed: {exc}\n")
