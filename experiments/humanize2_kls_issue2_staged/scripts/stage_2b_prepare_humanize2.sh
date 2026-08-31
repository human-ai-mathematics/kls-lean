#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_2b_common.sh"

h2_state_root="$(h2_stage2b_require_state_root)"
h2_source="$h2_state_root/tooling/humanize2"
h2_patch="$h2_stage2b_experiment_root/patches/humanize2-codex-seatbelt.patch"
h2_url="https://github.com/humanfia/humanize2.git"

mkdir -p "$(dirname "$h2_source")"
if [[ ! -d "$h2_source/.git" ]]; then
  if [[ -e "$h2_source" ]]; then
    echo "refusing non-Git Humanize2 tooling path: $h2_source" >&2
    exit 1
  fi
  git clone "$h2_url" "$h2_source"
  git -C "$h2_source" checkout --detach "$h2_stage2b_humanize_commit"
fi

if [[ "$(git -C "$h2_source" config --get remote.origin.url)" != "$h2_url" ]]; then
  echo "unexpected Humanize2 origin" >&2
  exit 1
fi
if [[ "$(git -C "$h2_source" rev-parse HEAD)" != "$h2_stage2b_humanize_commit" ]]; then
  echo "Humanize2 source is not at the pinned commit" >&2
  exit 1
fi

if git -C "$h2_source" apply --reverse --check "$h2_patch" >/dev/null 2>&1; then
  : # already patched
elif git -C "$h2_source" apply --check "$h2_patch" >/dev/null 2>&1; then
  git -C "$h2_source" apply "$h2_patch"
else
  echo "Humanize2 Seatbelt adapter patch does not apply cleanly" >&2
  exit 1
fi

HUMANIZE2_CODEX_ACTOR_SEATBELT=/private/tmp/disposable-stage2b-actor.sb \
  uv run --project "$h2_source" python - <<'PY'
from hmz.agents.codex import unattended

actor = unattended("workspace-write")
assert actor["sandbox"] == "danger-full-access"
assert actor["approvalPolicy"] == "never"
PY

h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_home="$h2_state_root/actor-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
if [[ -d "$h2_actor_root" && -f "$h2_seatbelt" ]]; then
  (
    cd "$h2_actor_root"
    HUMANIZE2_CODEX_ACTOR_HOME="$h2_actor_home" \
    HUMANIZE2_CODEX_ACTOR_TMP="$h2_actor_runtime_tmp" \
    HUMANIZE2_CODEX_ACTOR_SEATBELT="$h2_seatbelt" \
      uv run --project "$h2_source" python - <<'PY'
from hmz.agents.codex import CodexAgent, CodexAgentConfig

agent = CodexAgent(
    CodexAgentConfig(
        model="gpt-5.6-sol",
        effort="high",
        permission="workspace-write",
    )
)
assert agent.server is not None
agent.stop()
PY
  )
fi

echo "prepared Seatbelt-wrapped Humanize2 at $h2_stage2b_humanize_commit"
printf '%s\n' "$h2_source"
