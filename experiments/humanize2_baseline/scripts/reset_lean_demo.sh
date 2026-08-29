#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
cp \
  "$h2_repo_root/experiments/humanize2_baseline/fixtures/lean/AddZeroTest.lean.initial" \
  "$h2_repo_root/experiments/humanize2_baseline/lean_demo/AddZeroTest.lean"
cp \
  "$h2_repo_root/experiments/humanize2_baseline/fixtures/lean/ActorReviewerTest.lean.initial" \
  "$h2_repo_root/experiments/humanize2_baseline/lean_demo/ActorReviewerTest.lean"
