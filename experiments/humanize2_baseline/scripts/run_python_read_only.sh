#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
h2_hmz_bin="${HMZ_BIN:-hmz}"
h2_model="${HUMANIZE2_AGENT_MODEL:-gpt-5.6-sol}"
h2_effort="${HUMANIZE2_AGENT_EFFORT:-high}"
h2_prompt_file="$h2_repo_root/experiments/humanize2_baseline/prompts/python_read_only.md"

cd "$h2_repo_root"
"$h2_hmz_bin" exec -f chat \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=read-only" \
  "$(<"$h2_prompt_file")"

