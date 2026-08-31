#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_1b_common.sh"

h2_test_root="$(mktemp -d /private/tmp/h2-issue2-stage1b-model-free.XXXXXX)"
trap 'chmod -R u+rwX "$h2_test_root" 2>/dev/null || true; rm -rf "$h2_test_root"' EXIT
export H2_ISSUE2_STAGE1B_STATE_ROOT="$h2_test_root/state"
h2_state_root="$(h2_stage1b_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"

set +e
H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1a \
  bash -c 'source "$1"; h2_stage1b_require_state_root' _ \
  "$h2_stage1b_script_dir/stage_1b_common.sh" >/dev/null 2>&1
h2_shared_root_status=$?
set -e
if [[ "$h2_shared_root_status" -eq 0 ]]; then
  echo "Stage 1B state validation accepted the historical Stage 1A root" >&2
  exit 1
fi

"$h2_stage1b_script_dir/stage_1b_reset_run_state.sh" >/dev/null
"$h2_stage1b_script_dir/stage_1b_verify_scaffold.sh" >/dev/null
h2_first_source="$(h2_stage1b_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')"
h2_first_olean="$(h2_stage1b_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')"
h2_first_candidate="$(h2_stage1b_sha256 "$h2_actor_root/CandidateStage1B.lean" | awk '{print $1}')"
h2_first_baseline="$(h2_stage1b_sha256 "$h2_state_root/audit/stage1b-workspace-baseline.json" | awk '{print $1}')"

"$h2_stage1b_script_dir/stage_1b_reset_run_state.sh" >/dev/null
"$h2_stage1b_script_dir/stage_1b_verify_scaffold.sh" >/dev/null
test "$h2_first_source" = "$(h2_stage1b_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')"
test "$h2_first_olean" = "$(h2_stage1b_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')"
test "$h2_first_candidate" = "$(h2_stage1b_sha256 "$h2_actor_root/CandidateStage1B.lean" | awk '{print $1}')"
test "$h2_first_baseline" = "$(h2_stage1b_sha256 "$h2_state_root/audit/stage1b-workspace-baseline.json" | awk '{print $1}')"

set +e
"$h2_stage1b_script_dir/stage_1b_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/sentinel-verifier.out" 2>&1
h2_sentinel_status=$?
set -e
if [[ "$h2_sentinel_status" -ne 2 ]]; then
  echo "Stage 1B verifier did not reject the sentinel with exit 2" >&2
  exit 1
fi

h2_rebuild_root="$h2_test_root/rebuilt-accepted"
mkdir -p "$h2_rebuild_root"
cp "$h2_stage1b_experiment_root/accepted/AcceptedStage1A.lean" \
  "$h2_rebuild_root/AcceptedStage1A.lean"
(
  cd "$h2_rebuild_root"
  LEAN_PATH="$(h2_stage1b_mathlib_lean_path)" \
    "$(h2_stage1b_lean_bin)" -o AcceptedStage1A.olean AcceptedStage1A.lean
)
test "$(h2_stage1b_sha256 "$h2_rebuild_root/AcceptedStage1A.olean" | awk '{print $1}')" = \
  "$h2_stage1b_olean_sha256"

python3 - \
  "$h2_stage1b_experiment_root/tests/fixtures/CandidateStage1B.lean.known_good" \
  "$h2_actor_root/CandidateStage1B.lean" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes())
PY
"$h2_stage1b_script_dir/stage_1b_verify_candidate.sh" "$h2_actor_root" >/dev/null

python3 - \
  "$h2_stage1b_experiment_root/review/pending/CandidateStage1BRun2.lean" \
  "$h2_actor_root/CandidateStage1B.lean" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes())
PY
if "$h2_stage1b_script_dir/stage_1b_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/warning-verifier.out" 2>&1; then
  echo "Stage 1B verifier accepted a candidate with a linter diagnostic" >&2
  exit 1
fi
rg -Fq 'unnecessarySimpa' "$h2_test_root/warning-verifier.out"
rg -Fq 'emitted forbidden compiler or linter diagnostics' "$h2_test_root/warning-verifier.out"

python3 - \
  "$h2_stage1b_experiment_root/tests/fixtures/CandidateStage1B.lean.known_good" \
  "$h2_actor_root/CandidateStage1B.lean" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes())
PY

python3 - "$h2_actor_root/CandidateStage1B.lean" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
path.write_text(path.read_text(encoding="utf-8") + "\naxiom stage1B_escape : False\n", encoding="utf-8")
PY
if "$h2_stage1b_script_dir/stage_1b_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/adversarial-verifier.out" 2>&1; then
  echo "Stage 1B verifier accepted an adversarial extra axiom" >&2
  exit 1
fi

"$h2_stage1b_script_dir/stage_1b_verify_isolation.sh" >/dev/null
python3 -m unittest "$h2_stage1b_experiment_root/tests/test_stage_1b_audit_actor_trace.py" >/dev/null

set +e
env -u H2_ISSUE2_STAGE1B_LIVE_RUN_ACK \
  H2_ISSUE2_STAGE1B_STATE_ROOT="$h2_state_root" \
  "$h2_stage1b_script_dir/stage_1b_run.sh" >"$h2_test_root/no-ack.out" 2>&1
h2_no_ack_status=$?
H2_ISSUE2_STAGE1B_STATE_ROOT="$h2_state_root" \
H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-run3-zero-warning-human-review \
  "$h2_stage1b_script_dir/stage_1b_run.sh" >"$h2_test_root/no-login.out" 2>&1
h2_no_login_status=$?
set -e
if [[ "$h2_no_ack_status" -ne 2 || "$h2_no_login_status" -ne 2 ]]; then
  echo "Stage 1B runner did not fail closed on acknowledgement/login gates" >&2
  exit 1
fi
rg -Fq 'acknowledge the authorized Issue 2 Stage 1B Run 3 zero-warning model run' \
  "$h2_test_root/no-ack.out"
rg -Fq 'authenticate the dedicated Stage 1B actor home' "$h2_test_root/no-login.out"

"$h2_stage1b_script_dir/stage_1b_reset_run_state.sh" >/dev/null
"$h2_stage1b_script_dir/stage_1b_verify_scaffold.sh" >/dev/null
echo "Stage 1B model-free tests passed: deterministic reset/rerun, immutable accepted artifacts, deterministic upstream-only compiled provenance, sentinel rejection, warning-free success, warning and adversarial rejection, read/write isolation, and complete trace policy"
