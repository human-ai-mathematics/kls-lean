#!/usr/bin/env bash

h2_stage2b_script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
h2_stage2b_experiment_root="$(cd "$h2_stage2b_script_dir/.." && pwd)"
h2_stage2b_repo_root="$(git -C "$h2_stage2b_experiment_root" rev-parse --show-toplevel)"
h2_stage2b_humanize_commit="e8bcede84d4b3365378e04f9c80d0fd397903c30"
h2_stage2b_stage1a_source_sha256="9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6"
h2_stage2b_stage1a_olean_sha256="212cd1f5a0c20d2f3974c5948ea4c26550409a5b3b7b47a4b65e1e9cdf65a3a0"
h2_stage2b_stage1b_source_sha256="027e69674f78eb735b380b18beaf43e55779e0634d7222f46681f1bae30b752d"
h2_stage2b_stage1b_olean_sha256="a90bd82e8b5655cb9f46e488696e8f6808a8ba003ac4d6bffd4b5cbc71605692"
h2_stage2b_stage2a_source_sha256="83847c7ef06cd6045a1d5d5a8595f3fb645be28e8af4c71d3e577187fb0ad586"
h2_stage2b_stage2a_olean_sha256="e2581fe4fcd46cd98353e47874bfb32d1ae5400c5cbae115c165b8f8ae0fce8f"
h2_stage2b_lean_toolchain="leanprover/lean4:v4.33.0"

h2_stage2b_realpath() {
  python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$1"
}

h2_stage2b_require_state_root() {
  local h2_state_root="${H2_ISSUE2_STAGE2B_STATE_ROOT:?Set H2_ISSUE2_STAGE2B_STATE_ROOT to a dedicated absolute path below /private/tmp}"
  local h2_forbidden_root
  if [[ "$h2_state_root" != /* ]]; then
    echo "H2_ISSUE2_STAGE2B_STATE_ROOT must be absolute" >&2
    return 1
  fi
  h2_state_root="$(h2_stage2b_realpath "$h2_state_root")"
  if [[ "$h2_state_root" == "/" ||
        "$h2_state_root" == "/tmp" ||
        "$h2_state_root" == "/private/tmp" ||
        "$h2_state_root" == "$h2_stage2b_repo_root" ||
        "$h2_state_root/" == "$h2_stage2b_repo_root/"* ]]; then
    echo "Stage 2B state root must be a dedicated path outside the repository" >&2
    return 1
  fi
  for h2_forbidden_root in \
    /private/tmp/humanize2-kls-issue2-stage1a \
    /private/tmp/humanize2-kls-issue2-stage1b \
    /private/tmp/humanize2-kls-issue2-stage1b-run2 \
    /private/tmp/humanize2-kls-issue2-stage1b-run3 \
    /private/tmp/humanize2-kls-issue2-stage2a \
    /private/tmp/humanize2-kls-issue2-stage2a-run1; do
    if [[ "$h2_state_root" == "$(h2_stage2b_realpath "$h2_forbidden_root")" ]]; then
      echo "Stage 2B state root must be separate from every historical Stage 1A/1B/2A root" >&2
      return 1
    fi
  done
  if [[ "$(uname -s)" != "Darwin" || "$h2_state_root/" != "/private/tmp/"* ]]; then
    echo "Stage 2B requires macOS and a dedicated state root below /private/tmp" >&2
    return 1
  fi
  printf '%s\n' "$h2_state_root"
}

h2_stage2b_lean_bin() {
  (
    cd "$h2_stage2b_repo_root/formalization"
    elan which lean
  )
}

h2_stage2b_kls_build_root() {
  h2_stage2b_realpath "$h2_stage2b_repo_root/formalization/.lake/build/lib/lean"
}

h2_stage2b_baseline_formalization_root() {
  local h2_build_root
  h2_build_root="$(h2_stage2b_kls_build_root)"
  cd "$h2_build_root/../../../.." && pwd
}

h2_stage2b_main_checkout() {
  local h2_checkout="${H2_ISSUE2_MAIN_CHECKOUT:-}"
  if [[ -z "$h2_checkout" ]]; then
    h2_checkout="$(git -C "$h2_stage2b_repo_root" worktree list --porcelain | \
      awk '/^worktree / { sub(/^worktree /, ""); print; exit }')"
  fi
  h2_stage2b_realpath "$h2_checkout"
}

h2_stage2b_mathlib_lean_path() {
  local h2_full_path
  local h2_kls_build
  local h2_component
  local -a h2_allowed=()
  local -a h2_components=()
  h2_kls_build="$(h2_stage2b_kls_build_root)"
  h2_full_path="$(cd "$h2_stage2b_repo_root/formalization" && lake env printenv LEAN_PATH)"
  IFS=: read -r -a h2_components <<<"$h2_full_path"
  for h2_component in "${h2_components[@]}"; do
    [[ -n "$h2_component" ]] || continue
    h2_component="$(h2_stage2b_realpath "$h2_component")"
    if [[ "$h2_component" == "$h2_kls_build" ]]; then
      continue
    fi
    if [[ "$h2_component" == "$h2_stage2b_repo_root" ||
          "$h2_component/" == "$h2_stage2b_repo_root/"* ]]; then
      echo "refusing repository-local Lean import path: $h2_component" >&2
      return 1
    fi
    [[ -d "$h2_component" ]] || continue
    if [[ -e "$h2_component/FunctionalInequalities/Basic.olean" ||
          -e "$h2_component/FunctionalInequalities/Poincare.olean" ]]; then
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

h2_stage2b_actor_lean_path() {
  local h2_actor_root="${1:?actor root required}"
  printf '%s:%s\n' "$h2_actor_root" "$(h2_stage2b_mathlib_lean_path)"
}

h2_stage2b_lean_path_components() {
  local h2_lean_path
  local h2_component
  local -a h2_components=()
  h2_lean_path="$(h2_stage2b_mathlib_lean_path)"
  IFS=: read -r -a h2_components <<<"$h2_lean_path"
  for h2_component in "${h2_components[@]}"; do
    [[ -n "$h2_component" ]] || continue
    printf '%s\n' "$h2_component"
  done
}

h2_stage2b_sha256() {
  shasum -a 256 "$@"
}
