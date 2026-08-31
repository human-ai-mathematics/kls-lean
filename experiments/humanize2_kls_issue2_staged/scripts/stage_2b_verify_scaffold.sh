#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_2b_common.sh"

h2_state_root="$(h2_stage2b_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_candidate="$h2_actor_root/CandidateStage2B.lean"
h2_fixture="$h2_stage2b_experiment_root/fixtures/stage_2b_actor_workspace/CandidateStage2B.lean.initial"

cd "$h2_stage2b_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/pins/stage_2b.sha256
"$h2_stage2b_script_dir/stage_2b_verify_oracle_pins.sh"
"$h2_stage2b_script_dir/stage_2b_verify_actor_workspace.sh" "$h2_actor_root"
cmp "$h2_fixture" "$h2_candidate"
rg -Fq 'HUMANIZE2_UNATTEMPTED_STAGE_2B' "$h2_candidate"

h2_diagnostic="$h2_state_root/stage2b-initial-lean-diagnostic.txt"
if (
  cd "$h2_actor_root"
  LEAN_PATH="$(h2_stage2b_actor_lean_path "$h2_actor_root")" \
    "$(h2_stage2b_lean_bin)" CandidateStage2B.lean
) >"$h2_diagnostic" 2>&1; then
  echo "Stage 2B sentinel unexpectedly compiled" >&2
  exit 1
fi
if ! rg -Fq 'stage2BImplementationRequired' "$h2_diagnostic"; then
  echo "Stage 2B sentinel did not produce the expected compiler diagnostic" >&2
  exit 1
fi
"$h2_stage2b_script_dir/stage_2b_verify_actor_workspace.sh" "$h2_actor_root" >/dev/null

echo "Stage 2B fixture is restored at the expected compiler-failing sentinel"
