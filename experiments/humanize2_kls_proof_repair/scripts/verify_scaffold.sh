#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_require_external_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"

"$h2_proof_script_dir/verify_oracle_pins.sh"
"$h2_proof_script_dir/verify_actor_workspace.sh" "$h2_actor_root"
cmp \
  "$h2_proof_experiment_root/fixtures/actor_workspace/CandidateProof.lean.initial" \
  "$h2_actor_root/CandidateProof.lean"

h2_diagnostic="$h2_state_root/scaffold-lean-diagnostic.txt"
if "$(h2_lean_bin)" "$h2_actor_root/CandidateProof.lean" >"$h2_diagnostic" 2>&1; then
  echo "broken proof fixture unexpectedly compiled" >&2
  exit 1
fi
if ! rg -Fq 'Nat.zero_add n' "$h2_diagnostic"; then
  echo "broken proof fixture did not produce the pinned compiler mismatch" >&2
  exit 1
fi
rm -f "$h2_diagnostic"

python3 -m unittest discover -s "$h2_proof_experiment_root/tests" -p 'test_*.py'
echo "proof-repair scaffold is at the expected failing reset state"
