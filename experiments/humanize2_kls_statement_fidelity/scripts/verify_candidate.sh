#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
h2_candidate="experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean"

cd "$h2_repo_root"
if rg -Fq 'HUMANIZE2_UNATTEMPTED' "$h2_candidate"; then
  echo "candidate is still the unattempted sentinel" >&2
  exit 2
fi
if rg -n --pcre2 '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' "$h2_candidate"; then
  echo "candidate contains a forbidden proof placeholder" >&2
  exit 1
fi

h2_status="$(git status --porcelain=v1 --untracked-files=all)"
while IFS= read -r h2_line; do
  [[ -z "$h2_line" ]] && continue
  h2_path="${h2_line:3}"
  if [[ "$h2_path" != "$h2_candidate" ]]; then
    echo "unexpected repository change: $h2_line" >&2
    exit 1
  fi
done <<< "$h2_status"

experiments/humanize2_kls_statement_fidelity/scripts/verify_oracle_pins.sh
cd "$h2_repo_root/formalization"
lake env lean \
  ../experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean
