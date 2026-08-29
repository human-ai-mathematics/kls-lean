#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_actor_root="${1:?usage: verify_actor_workspace.sh ACTOR_ROOT}"
h2_actor_root="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$h2_actor_root")"
h2_fixture_root="$h2_issue2_experiment_root/fixtures/actor_workspace"

if [[ "$h2_actor_root" == "$h2_issue2_repo_root" ||
      "$h2_actor_root/" == "$h2_issue2_repo_root/"* ]]; then
  echo "actor workspace must be outside the repository" >&2
  exit 1
fi

h2_expected=$'AGENTS.md\nCandidateStage1A.lean\nTASK.md'
h2_actual="$(find "$h2_actor_root" -mindepth 1 -maxdepth 1 -print | \
  sed "s#^$h2_actor_root/##" | LC_ALL=C sort)"
if [[ "$h2_actual" != "$h2_expected" ]]; then
  echo "actor-visible file set drifted" >&2
  diff -u <(printf '%s\n' "$h2_expected") <(printf '%s\n' "$h2_actual") || true
  exit 1
fi
if find "$h2_actor_root" -type l -print -quit | grep -q .; then
  echo "actor workspace must not contain symlinks" >&2
  exit 1
fi

cmp "$h2_fixture_root/AGENTS.md" "$h2_actor_root/AGENTS.md"
cmp "$h2_fixture_root/TASK.md" "$h2_actor_root/TASK.md"
cmp "$h2_issue2_experiment_root/inputs/issue2_stage_1a_basic_vocabulary.md" \
  "$h2_actor_root/TASK.md"
echo "actor-visible files: AGENTS.md, CandidateStage1A.lean, TASK.md"
