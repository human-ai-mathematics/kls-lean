#!/usr/bin/env bash
set -euo pipefail

h2_repo_root="$(git rev-parse --show-toplevel)"
cd "$h2_repo_root/formalization"
lake env lean ../experiments/humanize2_baseline/lean_demo/AddZeroTest.lean
lake env lean ../experiments/humanize2_baseline/lean_demo/ActorReviewerTest.lean

