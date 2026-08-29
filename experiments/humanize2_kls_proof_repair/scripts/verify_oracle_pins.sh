#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

cd "$h2_proof_repo_root"
shasum -a 256 -c experiments/humanize2_kls_proof_repair/oracle/reference.sha256
