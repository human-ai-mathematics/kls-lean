#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_3_common.sh"

h2_actor_root="${1:?usage: stage_3_verify_candidate.sh ACTOR_ROOT}"
h2_actor_root="$(h2_stage3_realpath "$h2_actor_root")"
h2_candidate="$h2_actor_root/CandidateStage3.lean"
h2_fixture="$h2_stage3_experiment_root/fixtures/stage_3_actor_workspace/CandidateStage3.lean.initial"

"$h2_stage3_script_dir/stage_3_verify_actor_workspace.sh" "$h2_actor_root"
if cmp -s "$h2_fixture" "$h2_candidate"; then
  echo "candidate is still the Stage 3 reset fixture" >&2
  exit 2
fi

python3 - "$h2_candidate" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
imports = re.findall(r"^import\s+(\S+)\s*$", text, flags=re.MULTILINE)
if imports != ["AcceptedStage2B"]:
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
namespaces = re.findall(r"^namespace\s+(\S+)\s*$", code, flags=re.MULTILINE)
if namespaces != ["Issue2Autoformalization.Stage1A"]:
    raise SystemExit(f"namespace surface drifted: {namespaces!r}")

expected = [
    ("def", "poincareRayleighQuotient"),
    ("theorem", "poincareRayleighQuotient_le_optimal"),
    ("theorem", "poincareRayleighQuotient_eq_of_pos"),
    ("theorem", "poincareRayleighQuotient_eq_top_of_energy_eq_zero"),
    ("theorem", "admissibleRayleighQuotient_le_optimal"),
]
declarations = re.findall(
    r"^(def|theorem|lemma|abbrev|structure|class|inductive|axiom|opaque|instance)\s+([^\s({:]+)",
    code,
    flags=re.MULTILINE,
)
if declarations != expected:
    raise SystemExit(f"unexpected Stage 3 declarations: {declarations!r}")

attributes = re.findall(
    r"@\[\s*([^\]]+?)\s*\]\s*(?:\n\s*)?(?:theorem|lemma|def)\s+([^\s({:]+)",
    code,
    flags=re.MULTILINE,
)
if attributes:
    raise SystemExit(f"Stage 3 attributes drifted: {attributes!r}")

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
if "HUMANIZE2_UNATTEMPTED_STAGE_3" in text or "stage3ImplementationRequired" in text:
    raise SystemExit("Stage 3 reset sentinel remains")
if "FunctionalInequalities" in code or "Solutions" in code:
    raise SystemExit("candidate references a forbidden existing implementation namespace")
if re.search(
    r"\b(BorelSpace|FiniteDimensional|Nontrivial|Separability|"
    r"covariance(?:Bilin|Operator|Rayleigh|Max)?|lambdaMax|HasEigenvalue|EuclideanSpace)\b",
    code,
):
    raise SystemExit("candidate contains a stronger assumption or later-stage material")
PY

h2_verify_root="$(mktemp -d /private/tmp/h2-issue2-stage3-verify.XXXXXX)"
trap 'chmod -R u+rwX "$h2_verify_root" 2>/dev/null || true; rm -rf "$h2_verify_root"' EXIT
for h2_dependency in \
  AcceptedStage1A.lean AcceptedStage1A.olean \
  AcceptedStage1B.lean AcceptedStage1B.olean \
  AcceptedStage2A.lean AcceptedStage2A.olean \
  AcceptedStage2B.lean AcceptedStage2B.olean; do
  cp "$h2_actor_root/$h2_dependency" "$h2_verify_root/$h2_dependency"
done
cp "$h2_candidate" "$h2_verify_root/CandidateStage3.lean"
cp "$h2_stage3_experiment_root/verifier/issue2_stage_3_surface.lean" \
  "$h2_verify_root/Stage3SurfaceCheck.lean"
chmod u+rw "$h2_verify_root"/*

(
  cd "$h2_verify_root"
  h2_candidate_log="$h2_verify_root/CandidateStage3.log"
  h2_surface_log="$h2_verify_root/Stage3SurfaceCheck.log"
  if ! LEAN_PATH="$(h2_stage3_actor_lean_path "$h2_verify_root")" \
      "$(h2_stage3_lean_bin)" -o CandidateStage3.olean CandidateStage3.lean \
      >"$h2_candidate_log" 2>&1; then
    cat "$h2_candidate_log" >&2
    echo "Stage 3 candidate failed Lean compilation" >&2
    exit 1
  fi
  if [[ -s "$h2_candidate_log" ]]; then
    cat "$h2_candidate_log" >&2
    echo "Stage 3 candidate emitted forbidden compiler or linter diagnostics" >&2
    exit 1
  fi
  if ! LEAN_PATH="$(h2_stage3_actor_lean_path "$h2_verify_root")" \
      "$(h2_stage3_lean_bin)" Stage3SurfaceCheck.lean >"$h2_surface_log" 2>&1; then
    cat "$h2_surface_log" >&2
    echo "Stage 3 exact-surface checker failed Lean compilation" >&2
    exit 1
  fi
  if [[ -s "$h2_surface_log" ]]; then
    cat "$h2_surface_log" >&2
    echo "Stage 3 exact-surface checker emitted forbidden diagnostics" >&2
    exit 1
  fi
)

"$h2_stage3_script_dir/stage_3_verify_actor_workspace.sh" "$h2_actor_root" >/dev/null
echo "Stage 3 candidate has the exact five-declaration surface and compiles silently against immutable accepted dependencies plus upstream Mathlib only"
