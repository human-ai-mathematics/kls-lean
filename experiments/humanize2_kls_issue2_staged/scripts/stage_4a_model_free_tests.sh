#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_4a_common.sh"

h2_test_root="$(mktemp -d /private/tmp/h2-issue2-stage4a-model-free.XXXXXX)"
trap 'chmod -R u+rwX "$h2_test_root" 2>/dev/null || true; rm -rf "$h2_test_root"' EXIT
export H2_ISSUE2_STAGE4A_STATE_ROOT="$h2_test_root/state"
h2_state_root="$(h2_stage4a_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"

set +e
H2_ISSUE2_STAGE4A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b-run3 \
  bash -c 'source "$1"; h2_stage4a_require_state_root' _ \
  "$h2_stage4a_script_dir/stage_4a_common.sh" >/dev/null 2>&1
h2_shared_root_status=$?
set -e
if [[ "$h2_shared_root_status" -eq 0 ]]; then
  echo "Stage 4A state validation accepted the historical Stage 1B Run 3 root" >&2
  exit 1
fi
set +e
H2_ISSUE2_STAGE4A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage2a-run1 \
  bash -c 'source "$1"; h2_stage4a_require_state_root' _ \
  "$h2_stage4a_script_dir/stage_4a_common.sh" >/dev/null 2>&1
h2_shared_stage2a_root_status=$?
set -e
if [[ "$h2_shared_stage2a_root_status" -eq 0 ]]; then
  echo "Stage 4A state validation accepted the historical Stage 2A Run 1 root" >&2
  exit 1
fi
set +e
H2_ISSUE2_STAGE4A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage2b-run1 \
  bash -c 'source "$1"; h2_stage4a_require_state_root' _ \
  "$h2_stage4a_script_dir/stage_4a_common.sh" >/dev/null 2>&1
h2_shared_stage2b_root_status=$?
set -e
if [[ "$h2_shared_stage2b_root_status" -eq 0 ]]; then
  echo "Stage 4A state validation accepted the historical Stage 2B Run 1 root" >&2
  exit 1
fi
set +e
H2_ISSUE2_STAGE4A_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage3-run1 \
  bash -c 'source "$1"; h2_stage4a_require_state_root' _ \
  "$h2_stage4a_script_dir/stage_4a_common.sh" >/dev/null 2>&1
h2_shared_stage3_root_status=$?
set -e
if [[ "$h2_shared_stage3_root_status" -eq 0 ]]; then
  echo "Stage 4A state validation accepted the historical Stage 3 Run 1 root" >&2
  exit 1
fi

"$h2_stage4a_script_dir/stage_4a_reset_actor_workspace.sh" >/dev/null
"$h2_stage4a_script_dir/stage_4a_verify_scaffold.sh" >/dev/null
h2_first_stage1a_source="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')"
h2_first_stage1a_olean="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')"
h2_first_stage1b_source="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1B.lean" | awk '{print $1}')"
h2_first_stage1b_olean="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1B.olean" | awk '{print $1}')"
h2_first_stage2a_source="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2A.lean" | awk '{print $1}')"
h2_first_stage2a_olean="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2A.olean" | awk '{print $1}')"
h2_first_stage2b_source="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2B.lean" | awk '{print $1}')"
h2_first_stage2b_olean="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2B.olean" | awk '{print $1}')"
h2_first_stage3_source="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage3.lean" | awk '{print $1}')"
h2_first_stage3_olean="$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage3.olean" | awk '{print $1}')"
h2_first_candidate="$(h2_stage4a_sha256 "$h2_actor_root/CandidateStage4A.lean" | awk '{print $1}')"

"$h2_stage4a_script_dir/stage_4a_reset_actor_workspace.sh" >/dev/null
"$h2_stage4a_script_dir/stage_4a_verify_scaffold.sh" >/dev/null
test "$h2_first_stage1a_source" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')"
test "$h2_first_stage1a_olean" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')"
test "$h2_first_stage1b_source" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1B.lean" | awk '{print $1}')"
test "$h2_first_stage1b_olean" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage1B.olean" | awk '{print $1}')"
test "$h2_first_stage2a_source" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2A.lean" | awk '{print $1}')"
test "$h2_first_stage2a_olean" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2A.olean" | awk '{print $1}')"
test "$h2_first_stage2b_source" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2B.lean" | awk '{print $1}')"
test "$h2_first_stage2b_olean" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage2B.olean" | awk '{print $1}')"
test "$h2_first_stage3_source" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage3.lean" | awk '{print $1}')"
test "$h2_first_stage3_olean" = "$(h2_stage4a_sha256 "$h2_actor_root/AcceptedStage3.olean" | awk '{print $1}')"
test "$h2_first_candidate" = "$(h2_stage4a_sha256 "$h2_actor_root/CandidateStage4A.lean" | awk '{print $1}')"

set +e
"$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/sentinel-verifier.out" 2>&1
h2_sentinel_status=$?
set -e
if [[ "$h2_sentinel_status" -ne 2 ]]; then
  echo "Stage 4A verifier did not reject the sentinel with exit 2" >&2
  exit 1
fi

python3 - \
  "$h2_stage4a_experiment_root/tests/fixtures/CandidateStage4A.lean.known_good" \
  "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes())
PY
"$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" >/dev/null

python3 - \
  "$h2_stage4a_experiment_root/tests/fixtures/CandidateStage4A.lean.known_good" \
  "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
Path(sys.argv[2]).write_text(
    source.replace(
        "import Mathlib.Probability.Moments.CovarianceBilin\n",
        "import Mathlib.Probability.Moments.CovarianceBilin\nimport Mathlib.Data.Real.Basic\n",
        1,
    ),
    encoding="utf-8",
)
PY
if "$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/third-import-verifier.out" 2>&1; then
  echo "Stage 4A verifier accepted a third import" >&2
  exit 1
fi

python3 - \
  "$h2_stage4a_experiment_root/tests/fixtures/CandidateStage4A.lean.known_good" \
  "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
first = "import AcceptedStage3\nimport Mathlib.Probability.Moments.CovarianceBilin\n"
second = "import Mathlib.Probability.Moments.CovarianceBilin\nimport AcceptedStage3\n"
Path(sys.argv[2]).write_text(source.replace(first, second, 1), encoding="utf-8")
PY
if "$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/import-order-verifier.out" 2>&1; then
  echo "Stage 4A verifier accepted reversed imports" >&2
  exit 1
fi

python3 - \
  "$h2_stage4a_experiment_root/tests/fixtures/CandidateStage4A.lean.known_good" \
  "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
Path(sys.argv[2]).write_text(
    source.replace(" [MeasurableSpace E] [BorelSpace E]", " [MeasurableSpace E]", 1),
    encoding="utf-8",
)
PY
if "$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/missing-borel-verifier.out" 2>&1; then
  echo "Stage 4A verifier accepted a missing BorelSpace ambient assumption" >&2
  exit 1
fi

python3 - "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

target = Path(sys.argv[1])
target.write_text(target.read_text(encoding="utf-8") + "\naxiom stage4a_escape : False\n", encoding="utf-8")
PY
if "$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/adversarial-verifier.out" 2>&1; then
  echo "Stage 4A verifier accepted an adversarial extra axiom" >&2
  exit 1
fi

python3 - \
  "$h2_stage4a_experiment_root/tests/fixtures/CandidateStage4A.lean.known_good" \
  "$h2_actor_root/CandidateStage4A.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
Path(sys.argv[2]).write_text("set_option linter.unnecessarySimpa false\n" + source, encoding="utf-8")
PY
if "$h2_stage4a_script_dir/stage_4a_verify_candidate.sh" "$h2_actor_root" \
  >"$h2_test_root/suppression-verifier.out" 2>&1; then
  echo "Stage 4A verifier accepted diagnostic suppression" >&2
  exit 1
fi

"$h2_stage4a_script_dir/stage_4a_verify_isolation.sh" >/dev/null
python3 -m unittest "$h2_stage4a_experiment_root/tests/test_stage_4a_audit_actor_trace.py" \
  >/dev/null 2>&1

set +e
env -u H2_ISSUE2_STAGE4A_LIVE_RUN_ACK \
  H2_ISSUE2_STAGE4A_STATE_ROOT="$h2_state_root" \
  "$h2_stage4a_script_dir/stage_4a_run.sh" >"$h2_test_root/no-ack.out" 2>&1
h2_no_ack_status=$?
H2_ISSUE2_STAGE4A_STATE_ROOT="$h2_state_root" \
H2_ISSUE2_STAGE4A_LIVE_RUN_ACK=issue2-stage4a-run1-human-review \
  "$h2_stage4a_script_dir/stage_4a_run.sh" >"$h2_test_root/no-login.out" 2>&1
h2_no_login_status=$?
set -e
if [[ "$h2_no_ack_status" -ne 2 || "$h2_no_login_status" -ne 2 ]]; then
  echo "Stage 4A runner did not fail closed on acknowledgement/login gates" >&2
  exit 1
fi
rg -Fq 'acknowledge the authorized Issue 2 Stage 4A Run 1 model call' \
  "$h2_test_root/no-ack.out"
rg -Fq 'authenticate the dedicated Stage 4A actor home' "$h2_test_root/no-login.out"

"$h2_stage4a_script_dir/stage_4a_reset_actor_workspace.sh" >/dev/null
"$h2_stage4a_script_dir/stage_4a_verify_scaffold.sh" >/dev/null
echo "Stage 4A model-free tests passed: deterministic five-layer accepted dependency rebuild, exact thirteen-entry reset, sentinel rejection, silent known-good surface, fail-closed two-import order and BorelSpace controls, adversarial axiom and diagnostic-suppression rejection, candidate-only Seatbelt isolation, complete trace policy, and closed acknowledgement/login gates"
