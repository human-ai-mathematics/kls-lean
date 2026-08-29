#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_require_external_state_root)"
h2_source="$h2_state_root/tooling/humanize2"
h2_patch="$h2_proof_experiment_root/patches/humanize2-codex-seatbelt.patch"
h2_url="https://github.com/humanfia/humanize2.git"
h2_commit="e8bcede84d4b3365378e04f9c80d0fd397903c30"

mkdir -p "$(dirname "$h2_source")"
if [[ ! -d "$h2_source/.git" ]]; then
  if [[ -e "$h2_source" ]]; then
    echo "refusing non-Git Humanize2 tooling path: $h2_source" >&2
    exit 1
  fi
  git clone "$h2_url" "$h2_source"
  git -C "$h2_source" checkout --detach "$h2_commit"
fi

if [[ "$(git -C "$h2_source" config --get remote.origin.url)" != "$h2_url" ]]; then
  echo "unexpected Humanize2 origin" >&2
  exit 1
fi
if [[ "$(git -C "$h2_source" rev-parse HEAD)" != "$h2_commit" ]]; then
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

HUMANIZE2_CODEX_ACTOR_SEATBELT=/private/tmp/disposable-actor.sb \
  uv run --project "$h2_source" python - <<'PY'
from hmz.agents.codex import unattended

actor = unattended("workspace-write")
reviewer = unattended("read-only")
assert actor["sandbox"] == "danger-full-access"
assert reviewer["sandbox"] == "read-only"
PY

h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_home="$h2_state_root/actor-codex-home"
h2_reviewer_home="$h2_state_root/reviewer-codex-home"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_reviewer_tmp="$h2_state_root/reviewer-runtime-tmp"
if [[ -d "$h2_actor_root" && -f "$h2_seatbelt" ]]; then
  (
    cd "$h2_actor_root"
    HUMANIZE2_CODEX_ACTOR_HOME="$h2_actor_home" \
    HUMANIZE2_CODEX_ACTOR_TMP="$h2_runtime_tmp" \
    HUMANIZE2_CODEX_REVIEWER_HOME="$h2_reviewer_home" \
    HUMANIZE2_CODEX_REVIEWER_TMP="$h2_reviewer_tmp" \
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

echo "prepared Seatbelt-wrapped Humanize2 at $h2_commit"
printf '%s\n' "$h2_source"
