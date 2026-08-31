#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/stage_2a_common.sh"

h2_state_root="$(h2_stage2a_require_state_root)"
h2_actor_root="$h2_state_root/actor-workspace"
h2_actor_codex_home="$h2_state_root/actor-codex-home"
h2_actor_runtime_tmp="$h2_state_root/actor-runtime-tmp"
h2_config="$h2_stage2a_experiment_root/configs/stage_2a_codex-isolated.toml"
h2_template="$h2_stage2a_experiment_root/configs/stage_2a_actor-seatbelt.sb.in"
h2_seatbelt="$h2_state_root/actor-seatbelt.sb"
h2_state_parent="$(dirname "$h2_state_root")"
h2_lean_bin_path="$(h2_stage2a_lean_bin)"
h2_toolchain_root="$(cd "$(dirname "$h2_lean_bin_path")/.." && pwd)"
h2_user_home="$(python3 -c 'from pathlib import Path; print(Path.home())')"
h2_codex_path="$(realpath "$(command -v codex)")"
case "$h2_codex_path" in
  /Applications/*.app/*) h2_codex_app_root="${h2_codex_path%%.app/*}.app" ;;
  *) h2_codex_app_root="$(dirname "$h2_codex_path")" ;;
esac
h2_upstream_lean_path="$(h2_stage2a_mathlib_lean_path)"

mkdir -p "$h2_actor_codex_home" "$h2_actor_runtime_tmp"
cp "$h2_config" "$h2_actor_codex_home/config.toml"
H2_UPSTREAM_LEAN_PATH="$h2_upstream_lean_path" python3 - \
  "$h2_template" \
  "$h2_seatbelt" \
  "$h2_state_parent" \
  "$h2_state_root" \
  "$h2_user_home" \
  "$h2_codex_app_root" \
  "$h2_codex_path" \
  "$h2_actor_root" \
  "$h2_actor_root/CandidateStage2A.lean" \
  "$h2_toolchain_root" \
  "$h2_actor_codex_home" \
  "$h2_actor_runtime_tmp" <<'PY'
from pathlib import Path
import os
import sys


def quoted(value: str) -> str:
    return value.replace("\\", "\\\\").replace('"', '\\"')


source = Path(sys.argv[1])
destination = Path(sys.argv[2])
values = {
    "__STATE_PARENT__": sys.argv[3],
    "__STATE_ROOT__": sys.argv[4],
    "__USER_HOME__": sys.argv[5],
    "__CODEX_APP_ROOT__": sys.argv[6],
    "__CODEX_EXECUTABLE__": sys.argv[7],
    "__ACTOR_ROOT__": sys.argv[8],
    "__CANDIDATE__": sys.argv[9],
    "__LEAN_TOOLCHAIN_ROOT__": sys.argv[10],
    "__ACTOR_CODEX_HOME__": sys.argv[11],
    "__ACTOR_RUNTIME_TMP__": sys.argv[12],
}
components = [
    os.path.realpath(value)
    for value in os.environ["H2_UPSTREAM_LEAN_PATH"].split(os.pathsep)
    if value
]
if not components:
    raise SystemExit("no upstream Lean import roots were supplied")

metadata: set[str] = set()
for component in components:
    held = Path(component)
    for parent in held.parents:
        value = os.fspath(parent)
        if value == "/":
            break
        metadata.add(value)

metadata_rules = "\n".join(
    f'  (literal "{quoted(value)}")'
    for value in sorted(metadata)
    if value not in {"/private", "/private/tmp", "/Users", values["__USER_HOME__"]}
)
read_rules = "\n".join(
    f'  (subpath "{quoted(value)}")' for value in sorted(set(components))
)

text = source.read_text(encoding="utf-8")
for key, value in values.items():
    if key not in text:
        raise SystemExit(f"Seatbelt template is missing {key}")
    text = text.replace(key, quoted(value))
for key, value in {
    "__UPSTREAM_METADATA_RULES__": metadata_rules,
    "__UPSTREAM_READ_RULES__": read_rules,
}.items():
    if key not in text:
        raise SystemExit(f"Seatbelt template is missing {key}")
    text = text.replace(key, value)
destination.write_text(text, encoding="utf-8")
PY

if rg -n '__[A-Z0-9_]+__' "$h2_seatbelt"; then
  echo "rendered Stage 2A Seatbelt profile contains a placeholder" >&2
  exit 1
fi
echo "rendered Stage 2A deny-default actor profile"
echo "actor workspace root: $h2_actor_root"
echo "only mutable actor path: $h2_actor_root/CandidateStage2A.lean"
echo "approved upstream Lean roots:"
h2_stage2a_lean_path_components | sed 's/^/  /'
