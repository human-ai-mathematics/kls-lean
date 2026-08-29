#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
"$h2_repo_root/experiments/humanize2_baseline/scripts/verify_lean_add_zero.sh"
"$h2_repo_root/experiments/humanize2_baseline/scripts/verify_lean_actor_reviewer.sh"
