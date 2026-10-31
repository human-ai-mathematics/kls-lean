#!/usr/bin/env python3
"""Prepare pinned Mathlib caches for the library, the OpenAI bridge and the Palomar project."""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess

from downstream import parse_imports
import lean_header

ROOT = Path(__file__).resolve().parents[1]
PROJECTS = {"formalization": "formalization", "openai": "integrations/openai",
            "palomar": "integrations/palomar"}
# Contained Lake projects and the in-repository path packages whose sources they build. Lake
# may resolve their Git dependencies (Mathlib) to each project's own checkout, so each needs its
# own cache. The Palomar project requires ../openai, which requires the library.
CONTAINED_SOURCES = {"openai": ("integrations/openai",),
                     "palomar": ("integrations/openai", "integrations/palomar")}


def project_sources(root: Path, project: str = "formalization") -> list[Path]:
    if project not in PROJECTS:
        raise ValueError(f"Unknown cache project: {project}")
    paths = [root / "formalization/FunctionalInequalities.lean"]
    for directory in ("formalization/FunctionalInequalities", "formalization/vendor",
                      "solutions", "examples", "research/audits"):
        paths.extend((root / directory).rglob("*.lean"))
    for package in CONTAINED_SOURCES.get(project, ()):
        # The bridge imports the substantive library as a path dependency, but
        # Lake may resolve its Git dependencies to the bridge's own checkouts.
        bridge = root / package
        paths.extend(bridge.glob("*.lean"))
        for directory in ("OAI", "KLSOpenAI", "research/audits"):
            if (bridge / directory).is_dir():
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


def check_cache(mathlib: Path, modules: set[str]) -> list[tuple[str, str]]:
    """Missing `(module, artifact)` pairs under the replay artifact policy.

    Each pinned source's own header decides: a `module` needs `.olean`, `.olean.server`,
    `.olean.private`, `.ir.sig` and `.ir` (an import reads the server/private parts
    unconditionally); a non-module source keeps the legacy `.olean`-only requirement.
    """
    compiled = mathlib / ".lake/build/lib/lean"
    missing = []
    for module in sorted(modules):
        source = mathlib.joinpath(*module.split(".")).with_suffix(".lean")
        try:
            required = lean_header.required_artifacts(source.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, lean_header.HeaderError) as exc:
            raise ValueError(f"Cannot classify pinned Mathlib source {module}: {exc}") from exc
        base = compiled.joinpath(*module.split("."))
        missing.extend((module, suffix) for suffix in required
                       if not base.with_suffix(suffix).is_file())
    return missing


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
        incomplete = len({module for module, _ in missing})
        raise ValueError(f"[{project}] Mathlib cache incomplete: {len(missing)} artifacts missing "
                         f"for {incomplete} of {len(modules)} modules. "
                         "Refusing an accidental source rebuild. First missing artifacts: "
                         + ", ".join(f"{module} ({suffix})" for module, suffix in missing[:20]))
    print(f"[{project}] Mathlib cache complete: every required artifact of {len(modules)} "
          "compiled modules found. Pinned third-party compiled imports remain trusted.", flush=True)
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
