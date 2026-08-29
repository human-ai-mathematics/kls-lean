#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
cp \
  "$h2_repo_root/experiments/humanize2_kls_statement_fidelity/fixtures/CandidateStatement.lean.initial" \
  "$h2_repo_root/experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean"
