# Restore the Issue #2 Lean design documentation

**Date:** 2026-09-02

**Type:** repository documentation

## Rationale

The intentionally minimal Issue #2 `main` branch retained the Lean sources, build pins, and
root-level certificate but omitted the two documents that explain how to reproduce the build and
how the implementation corresponds to the mathematical statement. Restore `LEAN_DESIGN.md` and
`formalization/README.md` so the repository documents its pinned toolchain, module boundary,
semantic choices, theorem scope, dimension-zero convention, and relevant Mathlib API limitations.

The restored text is based on the previously reviewed documentation, but is made self-contained
for the current minimal repository and updated to the final native API. In particular it uses the
`Poincare` and `Covariance` namespaces, records `Poincare.Holds` as a structure, and uses
`Covariance.lambdaMax` without asserting eigenvalue attainment outside nontrivial finite
dimension. No Lean source, mathematical statement, ledger, manuscript, proof, or experiment
artifact is changed.

## Files

- `LEAN_DESIGN.md`
- `formalization/README.md`
- this append-only decision record

## Validation

```text
$ cd formalization && lake build
Build completed successfully (2946 jobs).

$ git diff --check
[no output; exit 0]

$ stale-name audit of LEAN_DESIGN.md and formalization/README.md
[no matches; confirming zero retired API names]
```

At this documentation-restoration step, before the follow-up Issue #2 certification harness, the
branch contained no ledger or `research/check_ledger.py`; therefore no ledger was edited by this
change. The later, separately validated harness is owned by
`2026-09-02-complete-issue2-acceptance-harness.md`.
