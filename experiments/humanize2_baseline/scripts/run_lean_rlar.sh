#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
h2_hmz_bin="${HMZ_BIN:-hmz}"
h2_model="${HUMANIZE2_AGENT_MODEL:-gpt-5.6-sol}"
h2_effort="${HUMANIZE2_AGENT_EFFORT:-high}"
h2_prompt_file="$h2_repo_root/experiments/humanize2_baseline/prompts/lean_actor_reviewer.md"
h2_prepare="$h2_repo_root/experiments/humanize2_baseline/scripts/prepare_flowverse.sh"
h2_flowverse_name="humanize2-baseline-flowverse"

cd "$h2_repo_root"
"$h2_prepare"
"$h2_hmz_bin" exec -f "$h2_flowverse_name/rlar" \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=workspace-write" \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=read-only" \
  "$(<"$h2_prompt_file")"
