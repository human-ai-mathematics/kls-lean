#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

if [[ "${H2_PROOF_LIVE_RUN_ACK:-}" != "disposable-only" ]]; then
  echo "Set H2_PROOF_LIVE_RUN_ACK=disposable-only to acknowledge an external model run on the non-KLS fixture" >&2
  exit 2
fi

h2_state_root="$(h2_require_external_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_reviewer_codex_home="$h2_state_root/reviewer-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_reviewer_runtime_tmp="$h2_state_root/reviewer-runtime-tmp"
h2_actor_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_humanize_home="$h2_state_root/humanize-home"
h2_flow="$h2_proof_experiment_root/flows/proof_rlar.py"
h2_config="$h2_proof_experiment_root/configs/flow.yaml"
h2_prompt="$h2_proof_experiment_root/prompts/proof_actor.md"
h2_model="${HUMANIZE2_AGENT_MODEL:-gpt-5.6-sol}"
h2_effort="${HUMANIZE2_AGENT_EFFORT:-high}"

"$h2_proof_script_dir/reset_run_state.sh"
"$h2_proof_script_dir/verify_scaffold.sh"
"$h2_proof_script_dir/verify_isolation.sh"
h2_humanize_source="$("$h2_proof_script_dir/prepare_humanize2.sh" | tail -n 1)"

for h2_lane in actor reviewer; do
  if [[ "$h2_lane" == actor ]]; then
    h2_lane_home="$h2_actor_codex_home"
  else
    h2_lane_home="$h2_reviewer_codex_home"
  fi
  if ! CODEX_HOME="$h2_lane_home" codex login status >/dev/null 2>&1; then
    echo "authenticate the experiment-specific $h2_lane Codex home first:" >&2
    echo "  CODEX_HOME=$h2_lane_home codex login" >&2
    exit 2
  fi
done

export HUMANIZE_HOME="$h2_humanize_home"
export HUMANIZE_SENTRY=off
export HUMANIZE2_CODEX_ACTOR_HOME="$h2_actor_codex_home"
export HUMANIZE2_CODEX_ACTOR_TMP="$h2_actor_runtime_tmp"
export HUMANIZE2_CODEX_REVIEWER_HOME="$h2_reviewer_codex_home"
export HUMANIZE2_CODEX_REVIEWER_TMP="$h2_reviewer_runtime_tmp"
export HUMANIZE2_CODEX_ACTOR_SEATBELT="$h2_actor_seatbelt"
export H2_PROOF_ACTOR_ROOT="$h2_actor_root"
export H2_PROOF_REVIEWER_ROOT="$h2_proof_repo_root"
export H2_PROOF_EXPERIMENT_ROOT="$h2_proof_experiment_root"
export H2_PROOF_ACTOR_CODEX_HOME="$h2_actor_codex_home"
export H2_PROOF_ACTOR_SEATBELT="$h2_actor_seatbelt"
export PATH="$(dirname "$(h2_lean_bin)"):$PATH"

cd "$h2_proof_repo_root"
uv run --project "$h2_humanize_source" hmz exec \
  -f "$h2_flow" \
  -c "$h2_config" \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=workspace-write,web_search=off" \
  -a "cli=codex,model=$h2_model,effort=$h2_effort,permission=read-only,web_search=off" \
  "$(<"$h2_prompt")"

"$h2_proof_script_dir/verify_oracle_pins.sh"
"$h2_proof_script_dir/verify_candidate.sh" "$h2_actor_root"
python3 "$h2_proof_script_dir/audit_actor_trace.py" \
  --codex-home "$h2_actor_codex_home" \
  --actor-root "$h2_actor_root" \
  --forbidden-root "$h2_proof_repo_root" \
  --seatbelt-profile "$h2_actor_seatbelt" \
  >"$h2_state_root/audit/trace-audit.json"
echo "accepted disposable run; audit summary: $h2_state_root/audit/trace-audit.json"
