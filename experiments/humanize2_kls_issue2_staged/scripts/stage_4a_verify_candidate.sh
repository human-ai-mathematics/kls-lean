#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_4a_common.sh"

h2_actor_root="${1:?usage: stage_4a_verify_candidate.sh ACTOR_ROOT}"
h2_actor_root="$(h2_stage4a_realpath "$h2_actor_root")"
h2_candidate="$h2_actor_root/CandidateStage4A.lean"
h2_fixture="$h2_stage4a_experiment_root/fixtures/stage_4a_actor_workspace/CandidateStage4A.lean.initial"

"$h2_stage4a_script_dir/stage_4a_verify_actor_workspace.sh" "$h2_actor_root"
if cmp -s "$h2_fixture" "$h2_candidate"; then
  echo "candidate is still the Stage 4A reset fixture" >&2
  exit 2
fi

python3 - "$h2_candidate" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
imports = re.findall(r"^import\s+(\S+)\s*$", text, flags=re.MULTILINE)
if imports != ["AcceptedStage3", "Mathlib.Probability.Moments.CovarianceBilin"]:
    raise SystemExit(f"imports drifted: {imports!r}")

def strip_comments(source: str) -> str:
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

code = strip_comments(text)
ambient_commands = re.findall(
    r"^variable\s+(.+?)(?=\n(?:@\[|def|theorem)\b)",
    code,
    flags=re.MULTILINE | re.DOTALL,
)
ambient_normalized = [" ".join(command.split()) for command in ambient_commands]
expected_ambient = (
    "{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] "
    "[MeasurableSpace E] [BorelSpace E]"
)
if ambient_normalized != [expected_ambient]:
    raise SystemExit(f"ambient variable surface drifted: {ambient_normalized!r}")

namespaces = re.findall(r"^namespace\s+(\S+)\s*$", code, flags=re.MULTILINE)
if namespaces != ["Issue2Autoformalization.Stage1A"]:
    raise SystemExit(f"namespace surface drifted: {namespaces!r}")

expected = [
    ("def", "centeredCovarianceOperator"),
    ("theorem", "centeredCovarianceOperator_inner"),
    ("theorem", "centeredCovarianceOperator_isSymmetric"),
    ("theorem", "centeredCovarianceOperator_self_nonneg"),
    ("theorem", "centeredCovarianceOperator_self_eq_variance"),
    ("def", "covarianceRayleighMax"),
    ("theorem", "covarianceRayleighMax_eq_iSup_covariance_sphere"),
    ("theorem", "covarianceRayleighMax_nonneg"),
]
declarations = re.findall(
    r"^(def|theorem|lemma|abbrev|structure|class|inductive|axiom|opaque|instance)\s+([^\s({:]+)",
    code,
    flags=re.MULTILINE,
)
if declarations != expected:
    raise SystemExit(f"unexpected Stage 4A declarations: {declarations!r}")

attributes = re.findall(
    r"@\[\s*([^\]]+?)\s*\]\s*(?:\n\s*)?(?:theorem|lemma|def)\s+([^\s({:]+)",
    code,
    flags=re.MULTILINE,
)
if attributes != [("simp", "centeredCovarianceOperator_inner")]:
    raise SystemExit(f"Stage 4A attributes drifted: {attributes!r}")

if re.search(
    r"^\s*(?:private|protected)\s+(?:def|theorem|lemma|abbrev|structure|class|inductive|axiom|opaque|instance)\b",
    code,
    flags=re.MULTILINE,
):
    raise SystemExit("candidate contains an unrequested private or protected declaration")
if re.search(r"(^|\W)(sorry|admit|unsafe|external|sorryAx)(\W|$)", code):
    raise SystemExit("candidate contains a forbidden escape hatch")
if re.search(r"^\s*(?:syntax|macro|notation|scoped\s+notation|elab|attribute|set_option)\b", code, re.MULTILINE):
    raise SystemExit("candidate contains forbidden syntax, notation, attribute command, or option override")
if re.search(r"^\s*#\w+\b", code, re.MULTILINE):
    raise SystemExit("candidate contains an unrequested command")
if re.search(r"^\s*section(?:\s|$)", code, re.MULTILINE):
    raise SystemExit("candidate contains an unrequested section")
if re.search(
    r"(^|\W)(?:include_str|run_cmd|run_tac|IO|Socket|Network|Http|System\.FilePath)(\W|$)",
    code,
):
    raise SystemExit("candidate contains forbidden metaprogram, filesystem, or network machinery")
if "HUMANIZE2_UNATTEMPTED_STAGE_4A" in text or "stage4aImplementationRequired" in text:
    raise SystemExit("Stage 4A reset sentinel remains")
if "FunctionalInequalities" in code or "Solutions" in code:
    raise SystemExit("candidate references a forbidden existing implementation namespace")
if re.search(r"\[(?:[^\]]*\s)?(?:FiniteDimensional\s+ℝ\s+E|Nontrivial\s+E)\]", code):
    raise SystemExit("candidate contains an unrequested global finite-dimensional or nontrivial assumption")
if re.search(
    r"\b(centeredCovarianceOperator_hasEigenvalue_iSup|lambdaMaxCovariance(?:_toReal|"
    r"_eq_zero_of_subsingleton|_le_operatorNorm|_ne_top|_le|_le_optimal)?|"
    r"HasEigenvalue|EuclideanSpace|Separability)\b",
    code,
):
    raise SystemExit("candidate contains a stronger assumption or later-stage material")
PY

h2_verify_root="$(mktemp -d /private/tmp/h2-issue2-stage4a-verify.XXXXXX)"
trap 'chmod -R u+rwX "$h2_verify_root" 2>/dev/null || true; rm -rf "$h2_verify_root"' EXIT
for h2_dependency in \
  AcceptedStage1A.lean AcceptedStage1A.olean \
  AcceptedStage1B.lean AcceptedStage1B.olean \
  AcceptedStage2A.lean AcceptedStage2A.olean \
  AcceptedStage2B.lean AcceptedStage2B.olean \
  AcceptedStage3.lean AcceptedStage3.olean; do
  cp "$h2_actor_root/$h2_dependency" "$h2_verify_root/$h2_dependency"
done
cp "$h2_candidate" "$h2_verify_root/CandidateStage4A.lean"
cp "$h2_stage4a_experiment_root/verifier/issue2_stage_4a_surface.lean" \
  "$h2_verify_root/Stage4ASurfaceCheck.lean"
chmod u+rw "$h2_verify_root"/*

(
  cd "$h2_verify_root"
  h2_candidate_log="$h2_verify_root/CandidateStage4A.log"
  h2_surface_log="$h2_verify_root/Stage4ASurfaceCheck.log"
  if ! LEAN_PATH="$(h2_stage4a_actor_lean_path "$h2_verify_root")" \
      "$(h2_stage4a_lean_bin)" -o CandidateStage4A.olean CandidateStage4A.lean \
      >"$h2_candidate_log" 2>&1; then
    cat "$h2_candidate_log" >&2
    echo "Stage 4A candidate failed Lean compilation" >&2
    exit 1
  fi
  if [[ -s "$h2_candidate_log" ]]; then
    cat "$h2_candidate_log" >&2
    echo "Stage 4A candidate emitted forbidden compiler or linter diagnostics" >&2
    exit 1
  fi
  if ! LEAN_PATH="$(h2_stage4a_actor_lean_path "$h2_verify_root")" \
      "$(h2_stage4a_lean_bin)" Stage4ASurfaceCheck.lean >"$h2_surface_log" 2>&1; then
    cat "$h2_surface_log" >&2
    echo "Stage 4A exact-surface checker failed Lean compilation" >&2
    exit 1
  fi
  if [[ -s "$h2_surface_log" ]]; then
    cat "$h2_surface_log" >&2
    echo "Stage 4A exact-surface checker emitted forbidden diagnostics" >&2
    exit 1
  fi
)

"$h2_stage4a_script_dir/stage_4a_verify_actor_workspace.sh" "$h2_actor_root" >/dev/null
echo "Stage 4A candidate has the exact eight-declaration surface and compiles silently against immutable accepted dependencies plus upstream Mathlib only"
