#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
h2_hmz_bin="${HMZ_BIN:-hmz}"
h2_model="${HUMANIZE2_AGENT_MODEL:-gpt-5.6-sol}"
h2_effort="${HUMANIZE2_AGENT_EFFORT:-high}"
h2_prompt_file="$h2_repo_root/experiments/humanize2_baseline/prompts/python_read_only.md"
h2_state_root="${HUMANIZE2_STATE_ROOT:?Set HUMANIZE2_STATE_ROOT to an absolute directory outside the repository}"

if [[ "$h2_state_root" != /* || "$h2_state_root/" == "$h2_repo_root/"* ]]; then
  echo "HUMANIZE2_STATE_ROOT must be absolute and outside the repository" >&2
  exit 1
fi
export HUMANIZE_HOME="$h2_state_root/python-read-only"

cd "$h2_repo_root"
"$h2_hmz_bin" exec -f chat \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=read-only" \
  "$(<"$h2_prompt_file")"
