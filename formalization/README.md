# Lean formalization

This directory is the reproducible Lean/Mathlib project for the machine-checked Issue #2
linear-test lower bound and Issue #6 two-factor Poincaré tensorization bound. It contains the
reusable Poincaré API and the proofs packaged by `../solutions/LemLinearTestLower.lean` and
`../solutions/LemPoincareTensorization.lean`.

## Pinned versions

- Lean: `leanprover/lean4:v4.33.0` (see `lean-toolchain`)
- Mathlib: tag `v4.33.0`, resolved by `lake-manifest.json` to commit
  `db584cd6d46c92f209a44c0f1c829460d327499d`

Elan reads `lean-toolchain` automatically. From a clean checkout, install
[Elan](https://github.com/leanprover/elan) if necessary, then run:

```bash
cd formalization
lake build
```

Lake downloads the pinned Mathlib dependency on the first build. The local `.lake/` directory is
ignored, while `lake-manifest.json` is committed as the dependency lock file. The default build
compiles the reusable library and both repository-root certificates. Their proofs and local
imports must pass the repository's forbidden-token and transitive axiom checks.

`../.github/workflows/lean.yml` runs the ledger checker, its standard-library Python tests, and
this default build on pushes and pull requests. The official `leanprover/lean-action@v1` reads
the pinned toolchain in this directory and runs `lake exe cache get` before `lake build`.

## Updating dependencies

Choose a compatible Lean/Mathlib release, change both `lean-toolchain` and the `rev` in
`lakefile.toml`, then regenerate and verify the lock file:

```bash
cd formalization
lake update
lake build
```

Commit `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together. Do not replace a
release pin with an unpinned branch.

## Module boundary

- `FunctionalInequalities/Basic.lean` defines `Poincare.Admissible`, `Poincare.energy`, the
  `Poincare.Holds` structure, and the `ENNReal`-valued `Poincare.constant`.
- `FunctionalInequalities/Poincare.lean` defines `Poincare.linearTest`, `Poincare.rayleigh`,
  `Covariance.operator`, `Covariance.rayleighMax`, `Covariance.lambdaMax`, and their fixed and
  optimal lower bounds.
- `FunctionalInequalities/Project/LinearTestLower.lean` packages the exact finite-dimensional
  probability statement for Issue #2.
- `../solutions/LemLinearTestLower.lean` is the thin Issue #2 certificate compiled by the default
  build.
- `FunctionalInequalities/ProductGeometry.lean`, `ProductAdmissible.lean`, and
  `ProductVariance.lean` prove the Hilbert-product gradient identities, a.e. section
  admissibility, and L2/Fubini variance bounds used in tensorization.
- `FunctionalInequalities/Tensorization.lean` proves the fixed-constant product inequality with
  `max C C'` and the corresponding optimal-constant bound in `ENNReal`, including infinity.
- `FunctionalInequalities/Project/PoincareTensorization.lean` packages both conclusions and
  specializes them to Euclidean factors of arbitrary natural-number dimensions, including zero.
- `../solutions/LemPoincareTensorization.lean` is the thin tensorization certificate compiled by
  the default build.

Both ledger nodes are `proved` with `checked_by: lean`. Tensorization uses
`WithLp 2 (E × F)` and the transported product measure, with the existing `Poincare.Admissible`
class of globally smooth real-valued L2 tests with integrable squared gradient. Equivalence with
closed Dirichlet or Sobolev domains is outside this result.

The reviewed signatures and human acceptance are recorded in
`../research/decisions/2026-09-03-tensorization-freeze.md`. Source correspondence, semantic
review, local validation, and the publication/CI status are tracked in
`../research/explorations/2026-09-03-tensorization-acceptance.md`.
The detailed BGL/manuscript correspondence is in
`../research/explorations/2026-09-03-tensorization-source-alignment.md`.

The mathematical choices, theorem scope, dimension-zero convention, and relevant Mathlib API
limitations are documented in `../LEAN_DESIGN.md`. The repository-level `checked_by: lean`
binding and its validation command are documented in `../solutions/README.md` and
`../research/ledger-schema.md`.
