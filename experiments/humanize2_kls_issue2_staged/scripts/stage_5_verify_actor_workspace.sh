#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_5_common.sh"

h2_actor_root="${1:?usage: stage_5_verify_actor_workspace.sh ACTOR_ROOT}"
h2_actor_root="$(h2_stage5_realpath "$h2_actor_root")"
h2_fixture_root="$h2_stage5_experiment_root/fixtures/stage_5_actor_workspace"

if [[ "$h2_actor_root" == "$h2_stage5_repo_root" ||
      "$h2_actor_root/" == "$h2_stage5_repo_root/"* ]]; then
  echo "actor workspace must be outside the repository" >&2
  exit 1
fi

h2_expected=$'AGENTS.md\nAcceptedStage1A.lean\nAcceptedStage1A.olean\nAcceptedStage1B.lean\nAcceptedStage1B.olean\nAcceptedStage2A.lean\nAcceptedStage2A.olean\nAcceptedStage2B.lean\nAcceptedStage2B.olean\nAcceptedStage3.lean\nAcceptedStage3.olean\nAcceptedStage4A.lean\nAcceptedStage4A.olean\nAcceptedStage4B.lean\nAcceptedStage4B.olean\nCandidateStage5.lean\nTASK.md'
h2_actual="$(find "$h2_actor_root" -mindepth 1 -maxdepth 1 -print | \
  sed "s#^$h2_actor_root/##" | LC_ALL=C sort)"
if [[ "$h2_actual" != "$h2_expected" ]]; then
  echo "Stage 5 actor-visible file set drifted" >&2
  diff -u <(printf '%s\n' "$h2_expected") <(printf '%s\n' "$h2_actual") || true
  exit 1
fi
if find "$h2_actor_root" -type l -print -quit | grep -q .; then
  echo "Stage 5 actor workspace must not contain symlinks" >&2
  exit 1
fi

cmp "$h2_fixture_root/AGENTS.md" "$h2_actor_root/AGENTS.md"
cmp "$h2_stage5_experiment_root/inputs/issue2_stage_5_final_assembly.md" \
  "$h2_actor_root/TASK.md"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage1A.lean" \
  "$h2_actor_root/AcceptedStage1A.lean"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage1B.lean" \
  "$h2_actor_root/AcceptedStage1B.lean"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage2A.lean" \
  "$h2_actor_root/AcceptedStage2A.lean"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage2B.lean" \
  "$h2_actor_root/AcceptedStage2B.lean"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage3.lean" \
  "$h2_actor_root/AcceptedStage3.lean"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage4A.lean" \
  "$h2_actor_root/AcceptedStage4A.lean"
cmp "$h2_stage5_experiment_root/accepted/AcceptedStage4B.lean" \
  "$h2_actor_root/AcceptedStage4B.lean"

if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage1A.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage1a_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage1A.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage1a_olean_sha256" ]]; then
  echo "accepted Stage 1A dependency hash drifted" >&2
  exit 1
fi
if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage1B.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage1b_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage1B.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage1b_olean_sha256" ]]; then
  echo "accepted Stage 1B dependency hash drifted" >&2
  exit 1
fi
if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage2A.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage2a_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage2A.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage2a_olean_sha256" ]]; then
  echo "accepted Stage 2A dependency hash drifted" >&2
  exit 1
fi
if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage2B.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage2b_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage2B.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage2b_olean_sha256" ]]; then
  echo "accepted Stage 2B dependency hash drifted" >&2
  exit 1
fi
if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage3.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage3_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage3.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage3_olean_sha256" ]]; then
  echo "accepted Stage 3 dependency hash drifted" >&2
  exit 1
fi
if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage4A.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage4a_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage4A.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage4a_olean_sha256" ]]; then
  echo "accepted Stage 4A dependency hash drifted" >&2
  exit 1
fi
if [[ "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage4B.lean" | awk '{print $1}')" != \
      "$h2_stage5_stage4b_source_sha256" ||
      "$(h2_stage5_sha256 "$h2_actor_root/AcceptedStage4B.olean" | awk '{print $1}')" != \
      "$h2_stage5_stage4b_olean_sha256" ]]; then
  echo "accepted Stage 4B dependency hash drifted" >&2
  exit 1
fi

python3 - "$h2_actor_root" <<'PY'
import stat
import sys
from pathlib import Path

root = Path(sys.argv[1])
if stat.S_IMODE(root.stat().st_mode) & 0o222:
    raise SystemExit("actor workspace directory must be physically non-writable")
for name in (
    "AGENTS.md",
    "TASK.md",
    "AcceptedStage1A.lean",
    "AcceptedStage1A.olean",
    "AcceptedStage1B.lean",
    "AcceptedStage1B.olean",
    "AcceptedStage2A.lean",
    "AcceptedStage2A.olean",
    "AcceptedStage2B.lean",
    "AcceptedStage2B.olean",
    "AcceptedStage3.lean",
    "AcceptedStage3.olean",
    "AcceptedStage4A.lean",
    "AcceptedStage4A.olean",
    "AcceptedStage4B.lean",
    "AcceptedStage4B.olean",
):
    if stat.S_IMODE((root / name).stat().st_mode) & 0o222:
        raise SystemExit(f"immutable actor artifact is writable: {name}")
candidate_mode = stat.S_IMODE((root / "CandidateStage5.lean").stat().st_mode)
if not candidate_mode & stat.S_IWUSR or candidate_mode & (stat.S_IWGRP | stat.S_IWOTH):
    raise SystemExit("candidate must be writable only by its owner")
PY

echo "actor-visible files: AGENTS.md, AcceptedStage1A.lean, AcceptedStage1A.olean, AcceptedStage1B.lean, AcceptedStage1B.olean, AcceptedStage2A.lean, AcceptedStage2A.olean, AcceptedStage2B.lean, AcceptedStage2B.olean, AcceptedStage3.lean, AcceptedStage3.olean, AcceptedStage4A.lean, AcceptedStage4A.olean, AcceptedStage4B.lean, AcceptedStage4B.olean, CandidateStage5.lean, TASK.md"
echo "accepted Stage 1A/1B/2A/2B/3/4A/4B source and compiled dependencies match their immutable hashes"
