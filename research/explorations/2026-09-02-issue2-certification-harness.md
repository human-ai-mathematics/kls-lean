# Issue #2 Lean certification harness

**Date:** 2026-09-02

**Scope:** repository certification and documentation for `lem:linear-test-lower`; no new
mathematical claim.

## Target

Complete the repository-facing acceptance path for Issue #2 after the native Lean proof was
finished: connect the exact node to its Lean certificate, make `checked_by: lean` mechanically
meaningful, and retain a dependency-free checker with focused regression tests.

## Design findings

- The certificate is already a default Lake target through the `Issue2Solutions` library, so one
  `lake build` checks both the reusable library and the node-specific theorem.
- The ledger needs only the Issue #2 node in this deliberately minimal repository. Restoring the
  unrelated historical KLS and A-series control plane would expand the pull request beyond its
  mathematical scope.
- The ledger uses JSON syntax, a valid YAML 1.2 subset, so the exact acceptance command works with
  Python's standard library and does not silently depend on a locally installed PyYAML package.
- Static certification checks verify the certificate path, node token, absence of Lean escape
  tokens, and inclusion in a default Lake target. Compilation remains a separate mandatory gate.

## Mathematical and Mathlib boundary

The formalized claim and Mathlib-specific choices are documented in `LEAN_DESIGN.md`. In
particular, the implementation uses centered `covarianceBilin`, states `MemLp id 2 μ` explicitly,
and names the extended spectral supremum `Covariance.lambdaMax` because eigenvalue attainment is
proved only in nontrivial finite dimension. No Sobolev-domain equivalence, Gaussian equality,
mode-indicator argument, or KLS upper bound is added here.

## Outcome

The ledger node now declares `lean_solution: solutions/LemLinearTestLower.lean` and
`checked_by: lean`. The checker and its regression tests provide the repository-level connection;
the Lean build remains the proof-validation command.
