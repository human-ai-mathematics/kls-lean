#!/usr/bin/env bash
set -euo pipefail

: "${HUMANIZE_HOME:?Set HUMANIZE_HOME to an isolated directory outside the repository}"

h2_hmz_bin="${HMZ_BIN:-hmz}"
h2_flowverse_name="humanize2-baseline-flowverse"
h2_flowverse_url="https://github.com/humanfia/flowverse.git"
h2_flowverse_commit="22de7178543140edaaaef2bea351b51ac29e6f04"
h2_flowverse_dir="$HUMANIZE_HOME/flowverses/$h2_flowverse_name"

if ! "$h2_hmz_bin" flowverses list -q | grep -Fxq "$h2_flowverse_name"; then
  "$h2_hmz_bin" flowverses add "$h2_flowverse_url" "$h2_flowverse_name"
fi

h2_actual_url="$(git -C "$h2_flowverse_dir" config --get remote.origin.url)"
if [[ "$h2_actual_url" != "$h2_flowverse_url" ]]; then
  echo "unexpected flowverse origin: $h2_actual_url" >&2
  exit 1
fi

git -C "$h2_flowverse_dir" fetch origin "$h2_flowverse_commit"
git -C "$h2_flowverse_dir" checkout --detach "$h2_flowverse_commit"

h2_actual_commit="$(git -C "$h2_flowverse_dir" rev-parse HEAD)"
if [[ "$h2_actual_commit" != "$h2_flowverse_commit" ]]; then
  echo "flowverse pin failed: expected $h2_flowverse_commit, got $h2_actual_commit" >&2
  exit 1
fi

echo "pinned $h2_flowverse_name at $h2_actual_commit"
