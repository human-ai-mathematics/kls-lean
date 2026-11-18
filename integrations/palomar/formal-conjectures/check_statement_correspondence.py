#!/usr/bin/env python3
"""Reproduce the Formal Conjectures / Palomar statement-correspondence check.

The `OAI` block of `../Challenge.lean` (`namespace OAI` through `end OAI`) and its
`KLSOpenAI` block (up to the docstring of `KLSOpenAI.kls`) must each occur exactly once
in `StatementCorrespondence.lean.in`.

In a supplied Formal Conjectures checkout built with the pinned toolchain, the command
elaborates the same client bytes from a temporary file outside the checkout with
`lake env lean -DwarningAsError=true`. The checkout is either the base pin with
`FC_CONTRIBUTION.patch` applied or the published pull-request head; in both cases the
contribution files must have exactly the patch content.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHALLENGE = HERE.parent / "Challenge.lean"
CLIENT = HERE / "StatementCorrespondence.lean.in"
PATCH = HERE / "FC_CONTRIBUTION.patch"

TOOLCHAIN = "leanprover/lean4:v4.33.1"
BASE = "b6939a3a0d89e5f999fa8c6483a6ef646c1e2923"
PUBLISHED_HEAD = "9bb8202ff1cd8c97d1c28619e56a8b643ae96de5"
MODULE = "FormalConjectures.Randomstrasse.KLS"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(
    r"'FCStatementAudit\.palomar_iff_fc' depends on axioms:\s*\[([^\]]*)\]")
# Inherited variables that would redirect Git or select another Lean toolchain.
INHERITED = re.compile(r"^(GIT_|LEAN_|LAKE|LEAN$|ELAN_TOOLCHAIN$)")


class Failure(Exception):
    pass


def unique(data: bytes, marker: bytes) -> int:
    if data.count(marker) != 1:
        raise Failure(f"Challenge.lean: expected exactly one {marker!r}, "
                      f"found {data.count(marker)}")
    return data.index(marker)


def definition_blocks(challenge: bytes) -> dict[str, bytes]:
    """The two definition blocks of `Challenge.lean`, located by their unique boundaries."""
    oai_start = unique(challenge, b"\nnamespace OAI\n") + 1
    oai_close = b"\nend OAI\n"
    oai_end = unique(challenge, oai_close) + len(oai_close)
    kls_start = unique(challenge, b"\nnamespace KLSOpenAI\n") + 1
    theorem = unique(challenge, b"\ntheorem kls :")
    docstring = challenge.rfind(b"\n/--", kls_start, theorem) + 1
    comment = challenge[docstring:theorem]
    if not (oai_start < oai_end <= kls_start < docstring
            and comment.endswith(b"-/") and comment.count(b"-/") == 1):
        raise Failure("Challenge.lean: block boundaries are not in the expected order")
    return {"OAI": challenge[oai_start:oai_end], "KLSOpenAI": challenge[kls_start:docstring]}


def check_bytes(challenge: bytes, client: bytes) -> None:
    for name, block in definition_blocks(challenge).items():
        count = client.count(block)
        if count != 1:
            raise Failure(f"the {name} block of Challenge.lean ({len(block)} bytes) occurs "
                          f"{count} times in the client; expected exactly once")
        print(f"ok: {name} block, {len(block)} bytes, occurs once in the client")


def succeed(command: list[str], checkout: Path, hint: str) -> str:
    env = {key: value for key, value in os.environ.items() if not INHERITED.match(key)}
    env["GIT_OPTIONAL_LOCKS"] = "0"
    result = subprocess.run(command, cwd=checkout, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise Failure(f"`{' '.join(command)}` exited {result.returncode} ({hint}):\n"
                      f"{result.stdout.rstrip()}")
    return result.stdout


def check_checkout(checkout: Path) -> None:
    """The pinned toolchain, a pinned commit and exactly the contribution files of the patch."""
    toolchain = (checkout / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != TOOLCHAIN:
        raise Failure(f"lean-toolchain is {toolchain!r}; expected {TOOLCHAIN!r}")
    head = succeed(["git", "rev-parse", "HEAD"], checkout, "not a Git checkout").strip()
    if head not in (BASE, PUBLISHED_HEAD):
        raise Failure(f"HEAD is {head}; expected the base pin {BASE} with the patch applied "
                      f"or the published head {PUBLISHED_HEAD}")
    # Removing the added files applies cleanly only if they have exactly the patch content.
    succeed(["git", "apply", "--reverse", "--check", "--no-ignore-whitespace", str(PATCH)], checkout,
            "the contribution files differ from FC_CONTRIBUTION.patch")
    kind = "base pin with the patch applied" if head == BASE else "published pull-request head"
    print(f"ok: checkout is the {kind} ({head}), toolchain {TOOLCHAIN}; "
          f"the contribution files equal the patch")


def check_lean(checkout: Path, client: bytes) -> None:
    # A stale build would let the client import an old statement; `--no-build` only checks.
    succeed(["lake", "--wfail", "build", "--no-build", MODULE], checkout,
            f"build it first: lake --wfail build {MODULE}")
    print(f"ok: {MODULE} is built and current")
    with tempfile.TemporaryDirectory(prefix="fc-statement-correspondence-") as scratch:
        source = Path(scratch) / "StatementCorrespondence.lean"
        source.write_bytes(client)
        output = succeed(["lake", "env", "lean", "-DwarningAsError=true", str(source)],
                         checkout, "the correspondence client failed")
    report = AXIOM_REPORT.search(output)
    axioms = {name.strip() for name in report[1].split(",")} if report else set()
    if not axioms or not axioms <= AXIOMS:
        raise Failure(f"unexpected axiom report:\n{output.rstrip()}")
    print(f"ok: client elaborated with warningAsError; palomar_iff_fc depends on "
          f"{sorted(axioms)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("checkout", type=Path,
                        help="built Formal Conjectures checkout (patched base or published head)")
    checkout = parser.parse_args().checkout.resolve()
    try:
        client = CLIENT.read_bytes()
        check_bytes(CHALLENGE.read_bytes(), client)
        check_checkout(checkout)
        check_lean(checkout, client)
    except (Failure, OSError) as error:
        sys.stdout.flush()
        print(f"FAILED: {error}", file=sys.stderr)
        return 1
    print("Statement correspondence reproduced.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
