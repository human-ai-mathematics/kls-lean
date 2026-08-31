#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_2a_common.sh"

h2_test_root="$(mktemp -d /private/tmp/h2-issue2-stage2a-model-free.XXXXXX)"
trap 'chmod -R u+rwX "$h2_test_root" 2>/dev/null || true; rm -rf "$h2_test_root"' EXIT
export H2_ISSUE2_STAGE2A_STATE_ROOT="$h2_test_root/state"
h2_state_root="$(h2_stage2a_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"

set +e
H2_ISSUE2_STAGE2A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b-run3 \
  bash -c 'source "$1"; h2_stage2a_require_state_root' _ \
  "$h2_stage2a_script_dir/stage_2a_common.sh" >/dev/null 2>&1
h2_shared_root_status=$?
set -e
if [[ "$h2_shared_root_status" -eq 0 ]]; then
  echo "Stage 2A state validation accepted the historical Stage 1B Run 3 root" >&2
  exit 1
fi

"$h2_stage2a_script_dir/stage_2a_reset_actor_workspace.sh" >/dev/null
"$h2_stage2a_script_dir/stage_2a_verify_scaffold.sh" >/dev/null
h2_first_stage1a_source="$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')"
h2_first_stage1a_olean="$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')"
h2_first_stage1b_source="$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1B.lean" | awk '{print $1}')"
h2_first_stage1b_olean="$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1B.olean" | awk '{print $1}')"
h2_first_candidate="$(h2_stage2a_sha256 "$h2_actor_root/CandidateStage2A.lean" | awk '{print $1}')"

"$h2_stage2a_script_dir/stage_2a_reset_actor_workspace.sh" >/dev/null
"$h2_stage2a_script_dir/stage_2a_verify_scaffold.sh" >/dev/null
test "$h2_first_stage1a_source" = "$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')"
test "$h2_first_stage1a_olean" = "$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')"
test "$h2_first_stage1b_source" = "$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1B.lean" | awk '{print $1}')"
test "$h2_first_stage1b_olean" = "$(h2_stage2a_sha256 "$h2_actor_root/AcceptedStage1B.olean" | awk '{print $1}')"
test "$h2_first_candidate" = "$(h2_stage2a_sha256 "$h2_actor_root/CandidateStage2A.lean" | awk '{print $1}')"

set +e
"$h2_stage2a_script_dir/stage_2a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/sentinel-verifier.out" 2>&1
h2_sentinel_status=$?
set -e
if [[ "$h2_sentinel_status" -ne 2 ]]; then
  echo "Stage 2A verifier did not reject the sentinel with exit 2" >&2
  exit 1
fi

python3 - \
  "$h2_stage2a_experiment_root/tests/fixtures/CandidateStage2A.lean.known_good" \
  "$h2_actor_root/CandidateStage2A.lean" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes())
PY
"$h2_stage2a_script_dir/stage_2a_verify_candidate.sh" "$h2_actor_root" >/dev/null

python3 - "$h2_actor_root/CandidateStage2A.lean" <<'PY'
from pathlib import Path
import sys

target = Path(sys.argv[1])
target.write_text(target.read_text(encoding="utf-8") + "\naxiom stage2A_escape : False\n", encoding="utf-8")
PY
if "$h2_stage2a_script_dir/stage_2a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/adversarial-verifier.out" 2>&1; then
  echo "Stage 2A verifier accepted an adversarial extra axiom" >&2
  exit 1
fi

python3 - \
  "$h2_stage2a_experiment_root/tests/fixtures/CandidateStage2A.lean.known_good" \
  "$h2_actor_root/CandidateStage2A.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
Path(sys.argv[2]).write_text("set_option linter.unnecessarySimpa false\n" + source, encoding="utf-8")
PY
if "$h2_stage2a_script_dir/stage_2a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/suppression-verifier.out" 2>&1; then
  echo "Stage 2A verifier accepted diagnostic suppression" >&2
  exit 1
fi

"$h2_stage2a_script_dir/stage_2a_reset_actor_workspace.sh" >/dev/null
"$h2_stage2a_script_dir/stage_2a_verify_scaffold.sh" >/dev/null
echo "Stage 2A model-free tests passed: deterministic accepted dependency rebuild, exact seven-entry reset, sentinel rejection, silent known-good surface, adversarial axiom rejection, and diagnostic-suppression rejection"
