#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

h2_state_root="$(h2_require_external_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_reviewer_codex_home="$h2_state_root/reviewer-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_reviewer_runtime_tmp="$h2_state_root/reviewer-runtime-tmp"
h2_config="$h2_proof_experiment_root/configs/codex-isolated.toml"
h2_template="$h2_proof_experiment_root/configs/actor-seatbelt.sb.in"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_state_parent="$(dirname "$h2_state_root")"
h2_lean_bin_path="$(h2_lean_bin)"
h2_toolchain_root="$(cd "$(dirname "$h2_lean_bin_path")/.." && pwd)"
h2_user_home="$(python3 -c 'from pathlib import Path; print(Path.home())')"
h2_codex_path="$(realpath "$(command -v codex)")"
case "$h2_codex_path" in
  /Applications/*.app/*) h2_codex_app_root="${h2_codex_path%%.app/*}.app" ;;
  *) h2_codex_app_root="$(dirname "$h2_codex_path")" ;;
esac

mkdir -p \
  "$h2_actor_codex_home" \
  "$h2_reviewer_codex_home" \
  "$h2_actor_runtime_tmp" \
  "$h2_reviewer_runtime_tmp"
cp "$h2_config" "$h2_actor_codex_home/config.toml"
cp "$h2_config" "$h2_reviewer_codex_home/config.toml"
python3 - \
  "$h2_template" \
  "$h2_seatbelt" \
  "$h2_state_parent" \
  "$h2_state_root" \
  "$h2_user_home" \
  "$h2_codex_app_root" \
  "$h2_actor_root" \
  "$h2_toolchain_root" \
  "$h2_actor_codex_home" \
  "$h2_actor_runtime_tmp" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1])
destination = Path(sys.argv[2])
values = {
    "__STATE_PARENT__": sys.argv[3],
    "__STATE_ROOT__": sys.argv[4],
    "__USER_HOME__": sys.argv[5],
    "__CODEX_APP_ROOT__": sys.argv[6],
    "__ACTOR_ROOT__": sys.argv[7],
    "__LEAN_TOOLCHAIN_ROOT__": sys.argv[8],
    "__ACTOR_CODEX_HOME__": sys.argv[9],
    "__ACTOR_RUNTIME_TMP__": sys.argv[10],
}
text = source.read_text(encoding="utf-8")
for key, value in values.items():
    if key not in text:
        raise SystemExit(f"Seatbelt template is missing {key}")
    text = text.replace(key, value.replace('"', '\\"'))
rendered = text
destination.write_text(rendered, encoding="utf-8")
PY

if rg -n '__[A-Z0-9_]+__' "$h2_seatbelt"; then
  echo "rendered Seatbelt profile contains a placeholder" >&2
  exit 1
fi
echo "rendered deny-default actor Seatbelt profile for Lean toolchain $h2_toolchain_root"
