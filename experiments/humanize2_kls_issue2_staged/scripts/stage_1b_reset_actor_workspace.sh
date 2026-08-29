#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_1b_common.sh"

h2_state_root="$(h2_stage1b_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_build_root="$h2_state_root/accepted-build"
h2_audit_root="$h2_state_root/audit"
h2_fixture_root="$h2_stage1b_experiment_root/fixtures/stage_1b_actor_workspace"
h2_accepted_source="$h2_stage1b_experiment_root/accepted/AcceptedStage1A.lean"
h2_candidate="$h2_actor_root/CandidateStage1B.lean"

mkdir -p "$h2_state_root" "$h2_audit_root"
for h2_reset_target in "$h2_actor_root" "$h2_build_root"; do
  if [[ -e "$h2_reset_target" ]]; then
    case "$(h2_stage1b_realpath "$h2_reset_target")" in
      "$h2_state_root/actor-workspace"|"$h2_state_root/accepted-build") ;;
      *) echo "refusing unexpected Stage 1B reset target: $h2_reset_target" >&2; exit 1 ;;
    esac
    chmod -R u+rwX "$h2_reset_target"
    rm -rf "$h2_reset_target"
  fi
done

cd "$h2_stage1b_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/accepted/stage_1a.sha256
if [[ "$(<formalization/lean-toolchain)" != "$h2_stage1b_lean_toolchain" ]]; then
  echo "refusing to compile the accepted dependency with an unpinned Lean toolchain" >&2
  exit 1
fi

mkdir -p "$h2_build_root"
cp "$h2_accepted_source" "$h2_build_root/AcceptedStage1A.lean"
(
  cd "$h2_build_root"
  LEAN_PATH="$(h2_stage1b_mathlib_lean_path)" \
    "$(h2_stage1b_lean_bin)" -o AcceptedStage1A.olean AcceptedStage1A.lean
  shasum -a 256 -c "$h2_stage1b_experiment_root/accepted/AcceptedStage1A.olean.sha256"
)

mkdir -p "$h2_actor_root"
cp "$h2_fixture_root/AGENTS.md" "$h2_actor_root/AGENTS.md"
cp "$h2_stage1b_experiment_root/inputs/issue2_stage_1b_foundational_lemmas.md" \
  "$h2_actor_root/TASK.md"
cp "$h2_build_root/AcceptedStage1A.lean" "$h2_actor_root/AcceptedStage1A.lean"
cp "$h2_build_root/AcceptedStage1A.olean" "$h2_actor_root/AcceptedStage1A.olean"
cp "$h2_fixture_root/CandidateStage1B.lean.initial" "$h2_candidate"

chmod 0444 \
  "$h2_actor_root/AGENTS.md" \
  "$h2_actor_root/TASK.md" \
  "$h2_actor_root/AcceptedStage1A.lean" \
  "$h2_actor_root/AcceptedStage1A.olean"
chmod 0644 "$h2_candidate"
chmod 0555 "$h2_actor_root"

python3 - "$h2_actor_root" "$h2_audit_root/stage1b-workspace-baseline.json" <<'PY'
from __future__ import annotations

import hashlib
import json
import os
import stat
import sys
from pathlib import Path

root = Path(sys.argv[1])
output = Path(sys.argv[2])
entries = {}
for path in sorted(root.iterdir(), key=lambda item: item.name):
    data = path.read_bytes()
    entries[path.name] = {
        "sha256": hashlib.sha256(data).hexdigest(),
        "mode": stat.S_IMODE(path.stat().st_mode),
        "size": len(data),
    }
payload = {
    "actor_root": os.path.realpath(root),
    "directory_mode": stat.S_IMODE(root.stat().st_mode),
    "entries": entries,
}
output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
PY

printf '%s\n' "$h2_actor_root"
