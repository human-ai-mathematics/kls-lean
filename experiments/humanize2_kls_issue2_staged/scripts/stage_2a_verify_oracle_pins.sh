#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_2a_common.sh"

python3 - \
  "$h2_stage2a_repo_root/formalization/FunctionalInequalities/Poincare.lean" \
  "$h2_stage2a_experiment_root/oracle/stage_2a_reference.sha256" <<'PY'
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

names = (
    "linearTest",
    "linearTest_apply",
    "linearTest_eq_inner",
    "hasGradientAt_linearTest",
    "gradient_linearTest",
)
source = Path(sys.argv[1]).read_text(encoding="utf-8").splitlines(keepends=True)
blocks = []
for name in names:
    start_pattern = re.compile(rf"^(?:theorem|def)\s+{re.escape(name)}\b")
    starts = [index for index, line in enumerate(source) if start_pattern.match(line)]
    if len(starts) != 1:
        raise SystemExit(f"expected one Poincare.lean declaration named {name}, found {len(starts)}")
    declaration_start = starts[0]
    start = declaration_start
    for probe in range(declaration_start - 1, max(-1, declaration_start - 10), -1):
        if re.match(r"^omit\s+.+\s+in\s*$", source[probe]):
            start = probe
            break
        if re.match(r"^@\[.*\]\s*$", source[probe]):
            start = probe
            continue
        if re.match(r"^(?:theorem|def|structure|namespace|section|end)\b", source[probe]):
            break
    end = len(source)
    for index in range(declaration_start + 1, len(source)):
        if re.match(r"^(?:theorem|def|structure|namespace|section|end)\b", source[index]):
            end = index
            break
    blocks.append(f"-- {name}\n" + "".join(source[start:end]).rstrip() + "\n")
actual = hashlib.sha256("\n".join(blocks).encode()).hexdigest()
pin = Path(sys.argv[2]).read_text(encoding="utf-8").split()
if not pin:
    raise SystemExit("Stage 2A oracle pin is empty")
expected = pin[0]
if actual != expected:
    raise SystemExit(f"Stage 2A Poincare.lean surface drifted: expected {expected}, got {actual}")
print(f"{actual}  Poincare.lean Stage 2A five-declaration surface")
PY

echo "Stage 2A hidden human-oracle surface pin matches"
