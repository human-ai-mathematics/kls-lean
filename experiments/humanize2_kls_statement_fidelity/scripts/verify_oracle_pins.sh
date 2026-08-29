#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
cd "$h2_repo_root"
shasum -a 256 -c \
  experiments/humanize2_kls_statement_fidelity/oracle/reference.sha256
