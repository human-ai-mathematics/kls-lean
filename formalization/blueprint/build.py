#!/usr/bin/env python3
"""Build the nested KLS Lean Blueprint without assuming a root Lake package."""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path


BLUEPRINT = Path(__file__).resolve().parent
FORMALIZATION = BLUEPRINT.parent
SRC = BLUEPRINT / "src"
PRINT = BLUEPRINT / "print"
WEB = BLUEPRINT / "web"


def run(command: list[str], *, cwd: Path) -> None:
    print(f"[{cwd}] {' '.join(command)}", flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def environment_executable(name: str) -> str:
    """Prefer a console script beside the Python interpreter running this helper."""
    candidate = Path(sys.executable).parent / name
    if candidate.is_file():
        return str(candidate)
    resolved = shutil.which(name)
    if resolved is None:
        raise RuntimeError(f"required executable is not available: {name}")
    return resolved


def build_pdf() -> Path:
    PRINT.mkdir(parents=True, exist_ok=True)
    run(
        [
            "latexmk",
            "-r",
            "latexmkrc",
            "-interaction=nonstopmode",
            "-halt-on-error",
            "-output-directory=../print",
            "print.tex",
        ],
        cwd=SRC,
    )
    output = PRINT / "print.pdf"
    if not output.is_file():
        raise RuntimeError(f"PDF build did not create {output}")
    return output


def build_web() -> Path:
    bibliography = PRINT / "print.bbl"
    if not bibliography.is_file():
        build_pdf()
    shutil.copy2(bibliography, SRC / "web.bbl")
    WEB.mkdir(parents=True, exist_ok=True)
    run([environment_executable("plastex"), "-c", "plastex.cfg", "web.tex"], cwd=SRC)
    output = WEB / "index.html"
    if not output.is_file():
        raise RuntimeError(f"web build did not create {output}")
    return output


def check_declarations() -> Path:
    declarations = BLUEPRINT / "lean_decls"
    if not declarations.is_file():
        build_web()
    run(["lake", "exe", "checkdecls", "blueprint/lean_decls"], cwd=FORMALIZATION)
    return declarations


def clean() -> None:
    for directory in (PRINT, WEB):
        if directory.exists():
            shutil.rmtree(directory)
    for path in (BLUEPRINT / "lean_decls", SRC / "web.bbl", SRC / "web.paux"):
        path.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "target",
        choices=("pdf", "web", "checkdecls", "all", "clean"),
        help="artifact or check to run",
    )
    args = parser.parse_args()

    if args.target == "pdf":
        build_pdf()
    elif args.target == "web":
        build_web()
    elif args.target == "checkdecls":
        check_declarations()
    elif args.target == "all":
        build_pdf()
        build_web()
        check_declarations()
    else:
        clean()


if __name__ == "__main__":
    main()
