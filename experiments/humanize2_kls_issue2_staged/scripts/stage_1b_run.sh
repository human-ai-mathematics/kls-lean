#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_1b_common.sh"

if [[ "${H2_ISSUE2_STAGE1B_LIVE_RUN_ACK:-}" != "issue2-stage1b-run3-zero-warning-human-review" ]]; then
  echo "Set H2_ISSUE2_STAGE1B_LIVE_RUN_ACK=issue2-stage1b-run3-zero-warning-human-review to acknowledge the authorized Issue 2 Stage 1B Run 3 zero-warning model run" >&2
  exit 2
fi

h2_state_root="$(h2_stage1b_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_actor_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_humanize_home="$h2_state_root/humanize-home"
h2_flow="$h2_stage1b_experiment_root/flows/stage_1b_actor.py"
h2_prompt="$h2_stage1b_experiment_root/prompts/issue2_stage_1b_actor.md"
h2_model="${HUMANIZE2_AGENT_MODEL:-gpt-5.6-sol}"
h2_effort="${HUMANIZE2_AGENT_EFFORT:-high}"
h2_main_checkout="$(h2_stage1b_main_checkout)"
h2_baseline_kls_source="$(h2_stage1b_baseline_formalization_root)/FunctionalInequalities"
h2_baseline_manifest="$h2_state_root/audit/stage1b-workspace-baseline.json"

"$h2_stage1b_script_dir/stage_1b_reset_run_state.sh"
if ! h2_login_status="$(CODEX_HOME="$h2_actor_codex_home" codex login status 2>&1)"; then
  echo "authenticate the dedicated Stage 1B actor home with the ChatGPT subscription, then rerun:" >&2
  echo "  CODEX_HOME=$h2_actor_codex_home codex login" >&2
  exit 2
fi
if ! grep -Fqx 'Logged in using ChatGPT' <<<"$h2_login_status"; then
  echo "the dedicated Stage 1B actor home must be logged in using the ChatGPT subscription" >&2
  echo "  CODEX_HOME=$h2_actor_codex_home codex logout" >&2
  echo "  CODEX_HOME=$h2_actor_codex_home codex login" >&2
  exit 2
fi

"$h2_stage1b_script_dir/stage_1b_verify_scaffold.sh"
"$h2_stage1b_script_dir/stage_1b_verify_isolation.sh"
h2_humanize_source="$("$h2_stage1b_script_dir/stage_1b_prepare_humanize2.sh" | tail -n 1)"

export HUMANIZE_HOME="$h2_humanize_home"
export HUMANIZE_SENTRY=off
export HUMANIZE2_CODEX_ACTOR_HOME="$h2_actor_codex_home"
export HUMANIZE2_CODEX_ACTOR_TMP="$h2_actor_runtime_tmp"
export HUMANIZE2_CODEX_ACTOR_SEATBELT="$h2_actor_seatbelt"
export H2_ISSUE2_STAGE1B_ACTOR_ROOT="$h2_actor_root"
export LEAN_PATH="$(h2_stage1b_actor_lean_path "$h2_actor_root")"
export PATH="$(dirname "$(h2_stage1b_lean_bin)"):$PATH"

# Both the Humanize process and the Codex session are rooted in the external five-entry fixture.
cd "$h2_actor_root"
uv run --project "$h2_humanize_source" hmz exec \
  -f "$h2_flow" \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=workspace-write,web_search=off" \
  "$(<"$h2_prompt")"

"$h2_stage1b_script_dir/stage_1b_verify_candidate.sh" "$h2_actor_root"
"$h2_stage1b_script_dir/stage_1b_verify_oracle_pins.sh"
python3 "$h2_stage1b_script_dir/stage_1b_audit_actor_trace.py" \
  --codex-home "$h2_actor_codex_home" \
  --actor-root "$h2_actor_root" \
  --forbidden-root "$h2_stage1b_repo_root" \
  --forbidden-root "$h2_main_checkout" \
  --forbidden-root "$h2_baseline_kls_source" \
  --seatbelt-profile "$h2_actor_seatbelt" \
  --baseline-manifest "$h2_baseline_manifest" \
  >"$h2_state_root/audit/stage1b-trace-audit.json"

echo "Stage 1B candidate compiled with zero diagnostics and its complete actor trace passed the mechanical gates"
echo "candidate: $h2_actor_root/CandidateStage1B.lean"
echo "trace summary: $h2_state_root/audit/stage1b-trace-audit.json"
echo "STOP: a human must apply review/issue2_stage_1b_human_checklist.md; no acceptance or mathematical status change is automatic"
