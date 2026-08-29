#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_1b_common.sh"

h2_actor_root="${1:?usage: stage_1b_verify_candidate.sh ACTOR_ROOT}"
h2_actor_root="$(h2_stage1b_realpath "$h2_actor_root")"
h2_candidate="$h2_actor_root/CandidateStage1B.lean"
h2_fixture="$h2_stage1b_experiment_root/fixtures/stage_1b_actor_workspace/CandidateStage1B.lean.initial"

"$h2_stage1b_script_dir/stage_1b_verify_actor_workspace.sh" "$h2_actor_root"
if cmp -s "$h2_fixture" "$h2_candidate"; then
  echo "candidate is still the Stage 1B reset fixture" >&2
  exit 2
fi

python3 - "$h2_candidate" <<'PY'
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
imports = re.findall(r"^import\s+(\S+)\s*$", text, flags=re.MULTILINE)
if imports != ["AcceptedStage1A"]:
    raise SystemExit(f"imports drifted: {imports!r}")

def strip_comments(source: str) -> str:
    """Remove line and nested block comments while preserving line structure."""
    held = []
    index = 0
    depth = 0
    while index < len(source):
        pair = source[index : index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    held.append("\n")
                index += 1
            continue
        if pair == "--":
            newline = source.find("\n", index + 2)
            if newline < 0:
                break
            held.append("\n")
            index = newline + 1
        elif pair == "/-":
            depth = 1
            index += 2
        elif pair == "-/":
            raise SystemExit("candidate contains an unmatched block-comment terminator")
        else:
            held.append(source[index])
            index += 1
    if depth:
        raise SystemExit("candidate contains an unterminated block comment")
    return "".join(held)


# Explanatory comments are allowed and cannot create false escape/declaration matches.
code = strip_comments(text)

namespaces = re.findall(r"^namespace\s+(\S+)\s*$", code, flags=re.MULTILINE)
if namespaces != ["Issue2Autoformalization.Stage1A", "HasPoincare"]:
    raise SystemExit(f"namespace surface drifted: {namespaces!r}")

expected = [
    ("theorem", "dirichletEnergy_nonneg"),
    ("theorem", "norm_fderiv_eq_norm_gradient"),
    ("theorem", "dirichletEnergy_eq_fderiv"),
    ("theorem", "isProbabilityMeasure"),
    ("theorem", "constant_nonneg"),
    ("theorem", "variance_le"),
    ("theorem", "mono"),
    ("def", "optimalPoincareConstant"),
    ("theorem", "optimalPoincareConstant_le"),
    ("theorem", "le_optimalPoincareConstant"),
    ("theorem", "optimalPoincareConstant_eq_top_of_no_finite"),
    ("theorem", "optimalPoincareConstant_ne_top_of_hasPoincare"),
    ("theorem", "optimalPoincareConstant_eq_top_iff"),
]
declarations = re.findall(
    r"^(def|theorem|lemma|abbrev|structure|class|inductive|axiom|opaque|instance)\s+([^\s({:]+)",
    code,
    flags=re.MULTILINE,
)
if declarations != expected:
    raise SystemExit(f"unexpected Stage 1B declarations: {declarations!r}")

if re.search(
    r"^\s*(?:private|protected)\s+(?:def|theorem|lemma|abbrev|structure|class|inductive|axiom|opaque|instance)\b",
    code,
    flags=re.MULTILINE,
):
    raise SystemExit("candidate contains an unrequested private or protected declaration")
if re.search(r"(^|\W)(sorry|admit|unsafe|external|sorryAx)(\W|$)", code):
    raise SystemExit("candidate contains a forbidden escape hatch")
if re.search(r"^\s*(?:syntax|macro|notation|scoped\s+notation|elab|attribute)\b", code, re.MULTILINE):
    raise SystemExit("candidate contains unrequested syntax, macro, notation, elaborator, or attribute")
if re.search(r"^\s*#\w+\b", code, re.MULTILINE):
    raise SystemExit("candidate contains an unrequested command")
if re.search(
    r"(^|\W)(?:include_str|run_cmd|run_tac|IO|Socket|Network|Http|System\.FilePath)(\W|$)",
    code,
):
    raise SystemExit("candidate contains forbidden metaprogram, filesystem, or network machinery")
if "HUMANIZE2_UNATTEMPTED_STAGE_1B" in text or "stage1BImplementationRequired" in text:
    raise SystemExit("Stage 1B reset sentinel remains")
if "FunctionalInequalities" in code or "Solutions" in code:
    raise SystemExit("candidate references a forbidden existing implementation namespace")
PY

h2_verify_root="$(mktemp -d /private/tmp/h2-issue2-stage1b-verify.XXXXXX)"
trap 'chmod -R u+rwX "$h2_verify_root" 2>/dev/null || true; rm -rf "$h2_verify_root"' EXIT
cp "$h2_actor_root/AcceptedStage1A.lean" "$h2_verify_root/AcceptedStage1A.lean"
cp "$h2_actor_root/AcceptedStage1A.olean" "$h2_verify_root/AcceptedStage1A.olean"
cp "$h2_candidate" "$h2_verify_root/CandidateStage1B.lean"
cp "$h2_stage1b_experiment_root/verifier/issue2_stage_1b_surface.lean" \
  "$h2_verify_root/Stage1BSurfaceCheck.lean"
chmod u+rw "$h2_verify_root"/*

(
  cd "$h2_verify_root"
  LEAN_PATH="$(h2_stage1b_actor_lean_path "$h2_verify_root")" \
    "$(h2_stage1b_lean_bin)" -o CandidateStage1B.olean CandidateStage1B.lean
  LEAN_PATH="$(h2_stage1b_actor_lean_path "$h2_verify_root")" \
    "$(h2_stage1b_lean_bin)" Stage1BSurfaceCheck.lean
)

"$h2_stage1b_script_dir/stage_1b_verify_actor_workspace.sh" "$h2_actor_root" >/dev/null
echo "Stage 1B candidate has the exact thirteen-declaration surface and compiles against the immutable accepted dependency plus upstream Mathlib only"
