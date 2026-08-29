#!/usr/bin/env bash

h2_issue2_script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
h2_issue2_experiment_root="$(cd "$h2_issue2_script_dir/.." && pwd)"
h2_issue2_repo_root="$(git -C "$h2_issue2_experiment_root" rev-parse --show-toplevel)"
h2_issue2_humanize_commit="e8bcede84d4b3365378e04f9c80d0fd397903c30"

h2_issue2_require_state_root() {
  local h2_state_root="${H2_ISSUE2_STAGE1A_STATE_ROOT:?Set H2_ISSUE2_STAGE1A_STATE_ROOT to a dedicated absolute path below /private/tmp}"
  if [[ "$h2_state_root" != /* ]]; then
    echo "H2_ISSUE2_STAGE1A_STATE_ROOT must be absolute" >&2
    return 1
  fi
  h2_state_root="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$h2_state_root")"
  if [[ "$h2_state_root" == "/" ||
        "$h2_state_root" == "/tmp" ||
        "$h2_state_root" == "/private/tmp" ||
        "$h2_state_root" == "$h2_issue2_repo_root" ||
        "$h2_state_root/" == "$h2_issue2_repo_root/"* ]]; then
    echo "state root must be a dedicated path outside the repository" >&2
    return 1
  fi
  if [[ "$(uname -s)" != "Darwin" || "$h2_state_root/" != "/private/tmp/"* ]]; then
    echo "Stage 1A requires macOS and a dedicated state root below /private/tmp" >&2
    return 1
  fi
  printf '%s\n' "$h2_state_root"
}

h2_issue2_lean_bin() {
  (
    cd "$h2_issue2_repo_root/formalization"
    elan which lean
  )
}

h2_issue2_kls_build_root() {
  python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' \
    "$h2_issue2_repo_root/formalization/.lake/build/lib/lean"
}

h2_issue2_baseline_formalization_root() {
  local h2_build_root
  h2_build_root="$(h2_issue2_kls_build_root)"
  cd "$h2_build_root/../../../.." && pwd
}

h2_issue2_main_checkout() {
  local h2_checkout="${H2_ISSUE2_MAIN_CHECKOUT:-}"
  if [[ -z "$h2_checkout" ]]; then
    h2_checkout="$(git -C "$h2_issue2_repo_root" worktree list --porcelain | \
      awk '/^worktree / { sub(/^worktree /, ""); print; exit }')"
  fi
  python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$h2_checkout"
}

h2_issue2_mathlib_lean_path() {
  local h2_full_path
  local h2_kls_build
  local h2_component
  local -a h2_allowed=()
  local -a h2_components=()
  h2_kls_build="$(h2_issue2_kls_build_root)"
  h2_full_path="$(cd "$h2_issue2_repo_root/formalization" && lake env printenv LEAN_PATH)"
  IFS=: read -r -a h2_components <<<"$h2_full_path"
  for h2_component in "${h2_components[@]}"; do
    [[ -n "$h2_component" ]] || continue
    h2_component="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$h2_component")"
    if [[ "$h2_component" == "$h2_kls_build" ]]; then
      continue
    fi
    if [[ "$h2_component" == "$h2_issue2_repo_root" ||
          "$h2_component/" == "$h2_issue2_repo_root/"* ]]; then
      echo "refusing repository-local Lean import path: $h2_component" >&2
      return 1
    fi
    # Lake may retain an unused dependency entry whose build directory does not exist. Lean itself
    # ignores such entries; omit them from the actor environment instead of exporting a stale path.
    [[ -d "$h2_component" ]] || continue
    if [[ -e "$h2_component/FunctionalInequalities/Basic.olean" ]]; then
      echo "refusing a Lean import root containing compiled KLS artifacts: $h2_component" >&2
      return 1
    fi
    h2_allowed+=("$h2_component")
  done
  if [[ "${#h2_allowed[@]}" -eq 0 ]]; then
    echo "no upstream Mathlib import paths found" >&2
    return 1
  fi
  local IFS=:
  printf '%s\n' "${h2_allowed[*]}"
}

h2_issue2_lean_path_components() {
  local h2_lean_path
  local h2_component
  local -a h2_components=()
  h2_lean_path="$(h2_issue2_mathlib_lean_path)"
  IFS=: read -r -a h2_components <<<"$h2_lean_path"
  for h2_component in "${h2_components[@]}"; do
    [[ -n "$h2_component" ]] || continue
    printf '%s\n' "$h2_component"
  done
}

h2_issue2_sha256() {
  shasum -a 256 "$@"
}
