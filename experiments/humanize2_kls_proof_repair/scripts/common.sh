#!/usr/bin/env bash

h2_proof_script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
h2_proof_experiment_root="$(cd "$h2_proof_script_dir/.." && pwd)"
h2_proof_repo_root="$(git -C "$h2_proof_experiment_root" rev-parse --show-toplevel)"

h2_require_external_state_root() {
  local h2_state_root="${H2_PROOF_STATE_ROOT:?Set H2_PROOF_STATE_ROOT to an absolute directory outside the repository}"
  if [[ "$h2_state_root" != /* ]]; then
    echo "H2_PROOF_STATE_ROOT must be absolute" >&2
    return 1
  fi
  h2_state_root="$(python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$h2_state_root")"
  if [[ "$h2_state_root" == "/" ||
        "$h2_state_root" == "/tmp" ||
        "$h2_state_root" == "/private/tmp" ||
        "$h2_state_root" == "$h2_proof_repo_root" ||
        "$h2_state_root/" == "$h2_proof_repo_root/"* ]]; then
    echo "H2_PROOF_STATE_ROOT must be a dedicated path outside the repository" >&2
    return 1
  fi
  if [[ "$(uname -s)" != "Darwin" || "$h2_state_root/" != "/private/tmp/"* ]]; then
    echo "this Seatbelt experiment requires macOS and a dedicated state root below /private/tmp" >&2
    return 1
  fi
  printf '%s\n' "$h2_state_root"
}

h2_lean_bin() {
  if [[ -n "${H2_PROOF_LEAN_BIN:-}" ]]; then
    realpath "$H2_PROOF_LEAN_BIN"
    return
  fi
  (
    cd "$h2_proof_repo_root/formalization"
    elan which lean
  )
}

h2_sha256() {
  shasum -a 256 "$@"
}
