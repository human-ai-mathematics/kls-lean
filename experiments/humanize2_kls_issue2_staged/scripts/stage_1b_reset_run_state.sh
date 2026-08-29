#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_1b_common.sh"

h2_state_root="$(h2_stage1b_require_state_root)"
h2_actor_codex_home="$h2_state_root/actor-codex-home"

mkdir -p "$h2_state_root" "$h2_actor_codex_home"
for h2_reset_target in \
  "$h2_state_root/actor-workspace" \
  "$h2_state_root/accepted-build" \
  "$h2_state_root/humanize-home" \
  "$h2_state_root/audit" \
  "$h2_state_root/actor-runtime-tmp" \
  "$h2_state_root/actor-seatbelt.sb" \
  "$h2_state_root/stage1b-initial-lean-diagnostic.txt"; do
  if [[ -e "$h2_reset_target" ]]; then
    chmod -R u+rwX "$h2_reset_target" 2>/dev/null || true
    rm -rf "$h2_reset_target"
  fi
done
find "$h2_actor_codex_home" -mindepth 1 -maxdepth 1 ! -name auth.json -exec rm -rf {} +

"$h2_stage1b_script_dir/stage_1b_reset_actor_workspace.sh" >/dev/null
"$h2_stage1b_script_dir/stage_1b_render_actor_config.sh"
mkdir -p "$h2_state_root/audit"

echo "reset Stage 1B run state at $h2_state_root"
echo "preserved only an existing experiment-specific actor auth.json"
