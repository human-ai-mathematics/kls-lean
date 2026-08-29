#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_issue2_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_fixture_root="$h2_issue2_experiment_root/fixtures/actor_workspace"

mkdir -p "$h2_state_root"
if [[ -e "$h2_actor_root" ]]; then
  rm -rf "$h2_actor_root"
fi
mkdir -p "$h2_actor_root"
cp "$h2_fixture_root/AGENTS.md" "$h2_actor_root/AGENTS.md"
cp "$h2_fixture_root/TASK.md" "$h2_actor_root/TASK.md"
cp "$h2_fixture_root/CandidateStage1A.lean.initial" \
  "$h2_actor_root/CandidateStage1A.lean"
chmod u+rw "$h2_actor_root"/*

printf '%s\n' "$h2_actor_root"
