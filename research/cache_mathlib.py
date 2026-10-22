#!/usr/bin/env python3
"""Prepare pinned Mathlib caches for the library and optional OpenAI bridge."""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess

from downstream import parse_imports

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {"formalization": "formalization", "openai": "integrations/openai"}


def project_sources(root: Path, project: str = "formalization") -> list[Path]:
    if project not in PROJECTS:
        raise ValueError(f"Unknown cache project: {project}")
    paths = [root / "formalization/FunctionalInequalities.lean"]
    for directory in ("formalization/FunctionalInequalities", "formalization/vendor",
                      "solutions", "examples", "research/audits"):
        paths.extend((root / directory).rglob("*.lean"))
    if project == "openai":
        # The bridge imports the substantive library as a path dependency, but
        # Lake may resolve its Git dependencies to the bridge's own checkouts.
        bridge = root / PROJECTS[project]
        paths.extend(bridge.glob("*.lean"))
        for directory in ("OAI", "KLSOpenAI", "research/audits"):
            paths.extend((bridge / directory).rglob("*.lean"))
    return sorted(path for path in paths if path.is_file())


def mathlib_roots(root: Path, project: str = "formalization") -> dict[str, list[str]]:
    """Keep the aggregate `Mathlib` import as well as dotted module imports."""
    result: dict[str, list[str]] = {}
    for path in project_sources(root, project):
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


def prepare_cache(root: Path, *, project: str = "formalization", check_only: bool = False) -> int:
    if project == "all":
        for selected in PROJECTS:
            prepare_cache(root, project=selected, check_only=check_only)
        return 0
    if project not in PROJECTS:
        raise ValueError(f"Unknown cache project: {project}")
    package = root / PROJECTS[project]
    if not package.is_dir():
        raise ValueError(f"Cache project directory is missing: {package}")
    roots = mathlib_roots(root, project)
    # The aggregate module already imports all dotted Mathlib modules.
    targets = ["Mathlib"] if "Mathlib" in roots else sorted(roots)
    print(f"[{project}] Mathlib cache: {len(roots)} direct imports; "
          f"targets: {', '.join(targets)}", flush=True)
    if "Mathlib" in roots:
        print(f"Aggregate Mathlib is required by {len(roots['Mathlib'])} source files.", flush=True)
    if not check_only:
        subprocess.run(["lake", "exe", "cache", "get", *targets],
                       cwd=package, check=True)
    mathlib = package / ".lake/packages/mathlib"
    modules = required_modules(mathlib, targets)
    missing = check_cache(mathlib, modules)
    if missing:
        raise ValueError(f"[{project}] Mathlib cache incomplete: "
                         f"{len(missing)} of {len(modules)} modules missing. "
                         "Refusing an accidental source rebuild. First missing modules: "
                         + ", ".join(missing[:20]))
    print(f"[{project}] Mathlib cache complete: {len(modules)} required compiled modules found. "
          "Pinned third-party compiled imports remain trusted.", flush=True)
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--project", choices=[*PROJECTS, "all"], default="formalization",
                        help="Lake package cache to prepare (default: formalization)")
    parser.add_argument("--check", action="store_true", help="check existing files without fetching")
    args = parser.parse_args()
    try:
        raise SystemExit(prepare_cache(args.root.resolve(), project=args.project,
                                      check_only=args.check))
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"Mathlib cache preparation failed: {exc}\n")
