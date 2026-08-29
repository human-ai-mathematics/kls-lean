#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_actor_root="${1:?usage: verify_candidate.sh ACTOR_ROOT}"
h2_candidate="$h2_actor_root/CandidateStage1A.lean"
h2_fixture="$h2_issue2_experiment_root/fixtures/actor_workspace/CandidateStage1A.lean.initial"

"$h2_issue2_script_dir/verify_actor_workspace.sh" "$h2_actor_root"
if cmp -s "$h2_fixture" "$h2_candidate"; then
  echo "candidate is still the Stage 1A reset fixture" >&2
  exit 2
fi

python3 - "$h2_candidate" <<'PY'
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
expected_imports = [
    "Mathlib.Analysis.Calculus.ContDiff.Basic",
    "Mathlib.Analysis.Calculus.Gradient.Basic",
    "Mathlib.Probability.Moments.Variance",
]
imports = re.findall(r"^import\s+(\S+)\s*$", text, flags=re.MULTILINE)
if imports != expected_imports:
    raise SystemExit(f"imports drifted: {imports!r}")
if "namespace Issue2Autoformalization.Stage1A" not in text:
    raise SystemExit("required Stage 1A namespace is absent")
if "HUMANIZE2_UNATTEMPTED_STAGE_1A" in text or "stage1AImplementationRequired" in text:
    raise SystemExit("Stage 1A reset sentinel remains")

declarations = re.findall(
    r"^(?:structure|def|theorem|lemma|axiom|opaque|instance|class)\s+([^\s({:]+)",
    text,
    flags=re.MULTILINE,
)
if declarations != ["IsAdmissible", "dirichletEnergy", "HasPoincare"]:
    raise SystemExit(f"unexpected top-level declarations: {declarations!r}")
for field in ("smooth'", "memLp_two", "energy_integrable"):
    if not re.search(rf"^\s+{re.escape(field)}\s*:", text, flags=re.MULTILINE):
        raise SystemExit(f"required structure field is absent: {field}")
if re.search(r"(^|\W)(sorry|admit|unsafe|external)(\W|$)", text):
    raise SystemExit("candidate contains a forbidden escape hatch")
PY

LEAN_PATH="$(h2_issue2_mathlib_lean_path)" "$(h2_issue2_lean_bin)" "$h2_candidate"
echo "Stage 1A candidate has the frozen surface and compiles with upstream Mathlib only"
