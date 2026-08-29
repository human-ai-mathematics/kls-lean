#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
cd "$h2_repo_root"
python3 -m unittest discover \
  -s experiments/humanize2_baseline/python_demo \
  -p 'test_*.py'
