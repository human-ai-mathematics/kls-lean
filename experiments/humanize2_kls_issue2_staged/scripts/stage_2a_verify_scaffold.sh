#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_2a_common.sh"

h2_state_root="$(h2_stage2a_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_candidate="$h2_actor_root/CandidateStage2A.lean"
h2_fixture="$h2_stage2a_experiment_root/fixtures/stage_2a_actor_workspace/CandidateStage2A.lean.initial"

cd "$h2_stage2a_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/pins/stage_2a.sha256
"$h2_stage2a_script_dir/stage_2a_verify_oracle_pins.sh"
"$h2_stage2a_script_dir/stage_2a_verify_actor_workspace.sh" "$h2_actor_root"
cmp "$h2_fixture" "$h2_candidate"
rg -Fq 'HUMANIZE2_UNATTEMPTED_STAGE_2A' "$h2_candidate"

h2_diagnostic="$h2_state_root/stage2a-initial-lean-diagnostic.txt"
if (
  cd "$h2_actor_root"
  LEAN_PATH="$(h2_stage2a_actor_lean_path "$h2_actor_root")" \
    "$(h2_stage2a_lean_bin)" CandidateStage2A.lean
) >"$h2_diagnostic" 2>&1; then
  echo "Stage 2A sentinel unexpectedly compiled" >&2
  exit 1
fi
if ! rg -Fq 'stage2AImplementationRequired' "$h2_diagnostic"; then
  echo "Stage 2A sentinel did not produce the expected compiler diagnostic" >&2
  exit 1
fi
"$h2_stage2a_script_dir/stage_2a_verify_actor_workspace.sh" "$h2_actor_root" >/dev/null

echo "Stage 2A fixture is restored at the expected compiler-failing sentinel"
