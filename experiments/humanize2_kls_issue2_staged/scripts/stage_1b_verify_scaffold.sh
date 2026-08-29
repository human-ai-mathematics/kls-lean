#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_1b_common.sh"

h2_state_root="$(h2_stage1b_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_candidate="$h2_actor_root/CandidateStage1B.lean"
h2_fixture="$h2_stage1b_experiment_root/fixtures/stage_1b_actor_workspace/CandidateStage1B.lean.initial"

cd "$h2_stage1b_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/pins/stage_1b.sha256
"$h2_stage1b_script_dir/stage_1b_verify_oracle_pins.sh"
"$h2_stage1b_script_dir/stage_1b_verify_actor_workspace.sh" "$h2_actor_root"
cmp "$h2_fixture" "$h2_candidate"
rg -Fq 'HUMANIZE2_UNATTEMPTED_STAGE_1B' "$h2_candidate"

h2_diagnostic="$h2_state_root/stage1b-initial-lean-diagnostic.txt"
if (
  cd "$h2_actor_root"
  LEAN_PATH="$(h2_stage1b_actor_lean_path "$h2_actor_root")" \
    "$(h2_stage1b_lean_bin)" CandidateStage1B.lean
) >"$h2_diagnostic" 2>&1; then
  echo "Stage 1B sentinel unexpectedly compiled" >&2
  exit 1
fi
if ! rg -Fq 'stage1BImplementationRequired' "$h2_diagnostic"; then
  echo "Stage 1B sentinel did not produce the expected compiler diagnostic" >&2
  exit 1
fi
"$h2_stage1b_script_dir/stage_1b_verify_actor_workspace.sh" "$h2_actor_root" >/dev/null

echo "Stage 1B fixture is restored at the expected compiler-failing sentinel"
