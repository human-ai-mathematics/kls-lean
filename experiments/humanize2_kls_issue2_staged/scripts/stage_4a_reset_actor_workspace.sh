#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_4a_common.sh"

h2_state_root="$(h2_stage4a_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_build_root="$h2_state_root/accepted-build"
h2_audit_root="$h2_state_root/audit"
h2_fixture_root="$h2_stage4a_experiment_root/fixtures/stage_4a_actor_workspace"
h2_candidate="$h2_actor_root/CandidateStage4A.lean"

mkdir -p "$h2_state_root" "$h2_audit_root"
for h2_reset_target in "$h2_actor_root" "$h2_build_root"; do
  if [[ -e "$h2_reset_target" ]]; then
    case "$(h2_stage4a_realpath "$h2_reset_target")" in
      "$h2_state_root/actor-workspace"|"$h2_state_root/accepted-build") ;;
      *) echo "refusing unexpected Stage 4A reset target: $h2_reset_target" >&2; exit 1 ;;
    esac
    chmod -R u+rwX "$h2_reset_target"
    rm -rf "$h2_reset_target"
  fi
done

cd "$h2_stage4a_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/accepted/stage_1a.sha256
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/accepted/stage_1b.sha256
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/accepted/stage_2a.sha256
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/accepted/stage_2b.sha256
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/accepted/stage_3.sha256
if [[ "$(<formalization/lean-toolchain)" != "$h2_stage4a_lean_toolchain" ]]; then
  echo "refusing to compile accepted dependencies with an unpinned Lean toolchain" >&2
  exit 1
fi

mkdir -p "$h2_build_root"
cp "$h2_stage4a_experiment_root/accepted/AcceptedStage1A.lean" "$h2_build_root/AcceptedStage1A.lean"
cp "$h2_stage4a_experiment_root/accepted/AcceptedStage1B.lean" "$h2_build_root/AcceptedStage1B.lean"
cp "$h2_stage4a_experiment_root/accepted/AcceptedStage2A.lean" "$h2_build_root/AcceptedStage2A.lean"
cp "$h2_stage4a_experiment_root/accepted/AcceptedStage2B.lean" "$h2_build_root/AcceptedStage2B.lean"
cp "$h2_stage4a_experiment_root/accepted/AcceptedStage3.lean" "$h2_build_root/AcceptedStage3.lean"
(
  cd "$h2_build_root"
  h2_mathlib_path="$(h2_stage4a_mathlib_lean_path)"
  h2_lean_bin="$(h2_stage4a_lean_bin)"
  LEAN_PATH="$h2_mathlib_path" "$h2_lean_bin" -o AcceptedStage1A.olean AcceptedStage1A.lean
  shasum -a 256 -c "$h2_stage4a_experiment_root/accepted/AcceptedStage1A.olean.sha256"
  LEAN_PATH="$h2_build_root:$h2_mathlib_path" \
    "$h2_lean_bin" -o AcceptedStage1B.olean AcceptedStage1B.lean
  shasum -a 256 -c "$h2_stage4a_experiment_root/accepted/AcceptedStage1B.olean.sha256"
  LEAN_PATH="$h2_build_root:$h2_mathlib_path" \
    "$h2_lean_bin" -o AcceptedStage2A.olean AcceptedStage2A.lean
  shasum -a 256 -c "$h2_stage4a_experiment_root/accepted/AcceptedStage2A.olean.sha256"
  LEAN_PATH="$h2_build_root:$h2_mathlib_path" \
    "$h2_lean_bin" -o AcceptedStage2B.olean AcceptedStage2B.lean
  shasum -a 256 -c "$h2_stage4a_experiment_root/accepted/AcceptedStage2B.olean.sha256"
  LEAN_PATH="$h2_build_root:$h2_mathlib_path" \
    "$h2_lean_bin" -o AcceptedStage3.olean AcceptedStage3.lean
  shasum -a 256 -c "$h2_stage4a_experiment_root/accepted/AcceptedStage3.olean.sha256"
)

mkdir -p "$h2_actor_root"
cp "$h2_fixture_root/AGENTS.md" "$h2_actor_root/AGENTS.md"
cp "$h2_stage4a_experiment_root/inputs/issue2_stage_4a_centered_covariance.md" \
  "$h2_actor_root/TASK.md"
cp "$h2_build_root/AcceptedStage1A.lean" "$h2_actor_root/AcceptedStage1A.lean"
cp "$h2_build_root/AcceptedStage1A.olean" "$h2_actor_root/AcceptedStage1A.olean"
cp "$h2_build_root/AcceptedStage1B.lean" "$h2_actor_root/AcceptedStage1B.lean"
cp "$h2_build_root/AcceptedStage1B.olean" "$h2_actor_root/AcceptedStage1B.olean"
cp "$h2_build_root/AcceptedStage2A.lean" "$h2_actor_root/AcceptedStage2A.lean"
cp "$h2_build_root/AcceptedStage2A.olean" "$h2_actor_root/AcceptedStage2A.olean"
cp "$h2_build_root/AcceptedStage2B.lean" "$h2_actor_root/AcceptedStage2B.lean"
cp "$h2_build_root/AcceptedStage2B.olean" "$h2_actor_root/AcceptedStage2B.olean"
cp "$h2_build_root/AcceptedStage3.lean" "$h2_actor_root/AcceptedStage3.lean"
cp "$h2_build_root/AcceptedStage3.olean" "$h2_actor_root/AcceptedStage3.olean"
cp "$h2_fixture_root/CandidateStage4A.lean.initial" "$h2_candidate"

chmod 0444 \
  "$h2_actor_root/AGENTS.md" \
  "$h2_actor_root/TASK.md" \
  "$h2_actor_root/AcceptedStage1A.lean" \
  "$h2_actor_root/AcceptedStage1A.olean" \
  "$h2_actor_root/AcceptedStage1B.lean" \
  "$h2_actor_root/AcceptedStage1B.olean" \
  "$h2_actor_root/AcceptedStage2A.lean" \
  "$h2_actor_root/AcceptedStage2A.olean" \
  "$h2_actor_root/AcceptedStage2B.lean" \
  "$h2_actor_root/AcceptedStage2B.olean" \
  "$h2_actor_root/AcceptedStage3.lean" \
  "$h2_actor_root/AcceptedStage3.olean"
chmod 0644 "$h2_candidate"
chmod 0555 "$h2_actor_root"

python3 - "$h2_actor_root" "$h2_audit_root/stage4a-workspace-baseline.json" <<'PY'
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
for item in sorted(root.iterdir(), key=lambda entry: entry.name):
    data = item.read_bytes()
    entries[item.name] = {
        "sha256": hashlib.sha256(data).hexdigest(),
        "mode": stat.S_IMODE(item.stat().st_mode),
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
