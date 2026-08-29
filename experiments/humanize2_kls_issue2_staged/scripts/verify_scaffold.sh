#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_issue2_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_candidate="$h2_actor_root/CandidateStage1A.lean"
h2_fixture="$h2_issue2_experiment_root/fixtures/actor_workspace/CandidateStage1A.lean.initial"

cd "$h2_issue2_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/pins/stage_1a.sha256
"$h2_issue2_script_dir/verify_oracle_pins.sh"
"$h2_issue2_script_dir/verify_actor_workspace.sh" "$h2_actor_root"
cmp "$h2_fixture" "$h2_candidate"
rg -Fq 'HUMANIZE2_UNATTEMPTED_STAGE_1A' "$h2_candidate"

h2_diagnostic="$h2_state_root/stage1a-initial-lean-diagnostic.txt"
if LEAN_PATH="$(h2_issue2_mathlib_lean_path)" \
  "$(h2_issue2_lean_bin)" "$h2_candidate" >"$h2_diagnostic" 2>&1; then
  echo "Stage 1A sentinel unexpectedly compiled" >&2
  exit 1
fi
if ! rg -Fq 'stage1AImplementationRequired' "$h2_diagnostic"; then
  echo "Stage 1A sentinel did not produce the expected compiler diagnostic" >&2
  exit 1
fi

echo "Stage 1A fixture is restored at the expected compiler-failing sentinel"
