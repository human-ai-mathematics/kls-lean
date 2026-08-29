#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_issue2_require_state_root)"
h2_actor_codex_home="$h2_state_root/actor-codex-home"

mkdir -p "$h2_state_root" "$h2_actor_codex_home"
rm -rf \
  "$h2_state_root/actor-workspace" \
  "$h2_state_root/humanize-home" \
  "$h2_state_root/audit" \
  "$h2_state_root/actor-runtime-tmp" \
  "$h2_state_root/actor-seatbelt.sb" \
  "$h2_state_root/stage1a-initial-lean-diagnostic.txt"
find "$h2_actor_codex_home" -mindepth 1 -maxdepth 1 ! -name auth.json -exec rm -rf {} +

"$h2_issue2_script_dir/reset_actor_workspace.sh" >/dev/null
"$h2_issue2_script_dir/render_actor_config.sh"
mkdir -p "$h2_state_root/audit"

echo "reset Stage 1A run state at $h2_state_root"
echo "preserved only an existing experiment-specific actor auth.json"
