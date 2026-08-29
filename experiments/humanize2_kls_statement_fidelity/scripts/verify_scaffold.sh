#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
h2_experiment="$h2_repo_root/experiments/humanize2_kls_statement_fidelity"

diff -u \
  "$h2_experiment/fixtures/CandidateStatement.lean.initial" \
  "$h2_experiment/candidate/CandidateStatement.lean"
rg -Fq 'HUMANIZE2_UNATTEMPTED' "$h2_experiment/candidate/CandidateStatement.lean"
"$h2_experiment/scripts/verify_oracle_pins.sh"

cd "$h2_repo_root/formalization"
lake env lean \
  ../experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean
