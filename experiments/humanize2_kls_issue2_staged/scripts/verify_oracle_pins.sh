#!/usr/bin/env bash
set -euo pipefail

source "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/common.sh"

cd "$h2_issue2_repo_root"
shasum -a 256 -c experiments/humanize2_kls_issue2_staged/oracle/stage_1a_reference.sha256
echo "Stage 1A hidden human oracle pin matches"
