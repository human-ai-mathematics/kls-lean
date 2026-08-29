#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_actor_root="${1:?usage: verify_candidate.sh ACTOR_ROOT}"
h2_candidate="$h2_actor_root/CandidateProof.lean"
h2_initial="$h2_proof_experiment_root/fixtures/actor_workspace/CandidateProof.lean.initial"
h2_declaration='theorem humanize2_isolated_add_zero (n : Nat) : n + 0 = n := by'

"$h2_proof_script_dir/verify_actor_workspace.sh" "$h2_actor_root"
if cmp -s "$h2_initial" "$h2_candidate"; then
  echo "candidate is still the deliberately broken reset fixture" >&2
  exit 2
fi
if [[ "$(sed -n '1p' "$h2_candidate")" != "$h2_declaration" ]]; then
  echo "candidate theorem declaration drifted" >&2
  exit 1
fi
if [[ "$(rg -c '^theorem ' "$h2_candidate")" != "1" ]]; then
  echo "candidate must contain exactly one theorem" >&2
  exit 1
fi
if rg -n --pcre2 '(^|[^[:alnum:]_])(sorry|admit|axiom|unsafe)([^[:alnum:]_]|$)' "$h2_candidate"; then
  echo "candidate contains a forbidden proof escape hatch" >&2
  exit 1
fi

"$(h2_lean_bin)" "$h2_candidate"
echo "candidate preserves the disposable statement and compiles with Lean 4.33.0"
