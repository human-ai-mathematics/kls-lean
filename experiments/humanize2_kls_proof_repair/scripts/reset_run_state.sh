#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_require_external_state_root)"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_reviewer_codex_home="$h2_state_root/reviewer-codex-home"

mkdir -p "$h2_state_root" "$h2_actor_codex_home" "$h2_reviewer_codex_home"
rm -rf \
  "$h2_state_root/actor-workspace" \
  "$h2_state_root/humanize-home" \
  "$h2_state_root/audit" \
  "$h2_state_root/actor-runtime-tmp" \
  "$h2_state_root/reviewer-runtime-tmp"
for h2_codex_home in "$h2_actor_codex_home" "$h2_reviewer_codex_home"; do
  find "$h2_codex_home" -mindepth 1 -maxdepth 1 ! -name auth.json -exec rm -rf {} +
done

"$h2_proof_script_dir/reset_actor_workspace.sh" >/dev/null
"$h2_proof_script_dir/render_actor_config.sh"
mkdir -p "$h2_state_root/audit"

echo "reset disposable run state at $h2_state_root"
echo "preserved any experiment-specific actor/reviewer Codex authentication files"
