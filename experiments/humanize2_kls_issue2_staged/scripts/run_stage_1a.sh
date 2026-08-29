#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

if [[ "${H2_ISSUE2_STAGE1A_LIVE_RUN_ACK:-}" != "issue2-stage1a-human-review" ]]; then
  echo "Set H2_ISSUE2_STAGE1A_LIVE_RUN_ACK=issue2-stage1a-human-review to acknowledge the authorized Issue 2 model run" >&2
  exit 2
fi

h2_state_root="$(h2_issue2_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_actor_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_humanize_home="$h2_state_root/humanize-home"
h2_flow="$h2_issue2_experiment_root/flows/stage_1a_actor.py"
h2_prompt="$h2_issue2_experiment_root/prompts/issue2_stage_1a_actor.md"
h2_model="${HUMANIZE2_AGENT_MODEL:-gpt-5.6-sol}"
h2_effort="${HUMANIZE2_AGENT_EFFORT:-high}"
h2_main_checkout="$(h2_issue2_main_checkout)"
h2_baseline_kls_source="$(h2_issue2_baseline_formalization_root)/FunctionalInequalities"

"$h2_issue2_script_dir/reset_run_state.sh"
"$h2_issue2_script_dir/verify_scaffold.sh"
"$h2_issue2_script_dir/verify_isolation.sh"
h2_humanize_source="$("$h2_issue2_script_dir/prepare_humanize2.sh" | tail -n 1)"

if ! CODEX_HOME="$h2_actor_codex_home" codex login status >/dev/null 2>&1; then
  echo "authenticate the dedicated Stage 1A actor home with the ChatGPT subscription, then rerun:" >&2
  echo "  CODEX_HOME=$h2_actor_codex_home codex login" >&2
  exit 2
fi

export HUMANIZE_HOME="$h2_humanize_home"
export HUMANIZE_SENTRY=off
export HUMANIZE2_CODEX_ACTOR_HOME="$h2_actor_codex_home"
export HUMANIZE2_CODEX_ACTOR_TMP="$h2_actor_runtime_tmp"
export HUMANIZE2_CODEX_ACTOR_SEATBELT="$h2_actor_seatbelt"
export H2_ISSUE2_STAGE1A_ACTOR_ROOT="$h2_actor_root"
export LEAN_PATH="$(h2_issue2_mathlib_lean_path)"
export PATH="$(dirname "$(h2_issue2_lean_bin)"):$PATH"

# Both the Humanize process and the Codex session are rooted in the external three-file fixture.
cd "$h2_actor_root"
uv run --project "$h2_humanize_source" hmz exec \
  -f "$h2_flow" \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=workspace-write,web_search=off" \
  "$(<"$h2_prompt")"

"$h2_issue2_script_dir/verify_candidate.sh" "$h2_actor_root"
"$h2_issue2_script_dir/verify_oracle_pins.sh"
python3 "$h2_issue2_script_dir/audit_actor_trace.py" \
  --codex-home "$h2_actor_codex_home" \
  --actor-root "$h2_actor_root" \
  --forbidden-root "$h2_issue2_repo_root" \
  --forbidden-root "$h2_main_checkout" \
  --forbidden-root "$h2_baseline_kls_source" \
  --seatbelt-profile "$h2_actor_seatbelt" \
  >"$h2_state_root/audit/trace-audit.json"

echo "Stage 1A candidate compiled and its actor trace passed the mechanical gates"
echo "candidate: $h2_actor_root/CandidateStage1A.lean"
echo "trace summary: $h2_state_root/audit/trace-audit.json"
echo "STOP: a human must apply review/issue2_stage_1a_human_checklist.md; no acceptance or mathematical status change is automatic"
