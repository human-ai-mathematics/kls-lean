#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
cp \
  "$h2_repo_root/experiments/humanize2_baseline/fixtures/python/calculator.py.initial" \
  "$h2_repo_root/experiments/humanize2_baseline/python_demo/calculator.py"
