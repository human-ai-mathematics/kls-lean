# Separate the Issue #2 closeout submission

**Date:** 2026-09-03 (Asia/Shanghai)

## Scope

Submit the CI closeout for Issue #2 as its own reviewable change. The native Lean proof
(`d3faf51`) and certification harness (`40703c2`) are already on `origin/main`. The closeout
branch `codex/issue2-ci-closeout` adds the CI workflow, its documentation, and these acceptance
records. The workflow implementation is the already validated commit `36ac48c`.

The ledger retains its single proved `lem:linear-test-lower` node. Its checker, 13 tests, Lake
configuration, existing Lean definitions, and proof files match `origin/main`. The separate
tensorization draft retains the lifecycle extension and declaration skeleton for later review.

## Validation

The isolated worktree uses a separate project build directory and shares only the pinned
third-party package cache with the original checkout. All project modules were compiled for
the Issue #2 branch. The three required commands passed:

```text
python3 research/check_ledger.py
1 ledger(s), 1 nodes. 0 error(s).

python3 -m unittest discover -s research/tests -p 'test_*.py'
Ran 13 tests in 0.052s
OK

cd formalization && lake build
Build completed successfully (2946 jobs).
```

The original successful remote CI execution is recorded in `2026-09-03-issue2-ci.md`. The
dedicated closeout PR must also pass its own CI before submission is reported complete.

## Mathematical boundary

This submission adds no mathematical statements, proof terms, placeholders, or Mathlib
dependencies. Issue #2 continues to certify the same linear-test lower bound with the same
moment assumptions and manuscript normalization.
