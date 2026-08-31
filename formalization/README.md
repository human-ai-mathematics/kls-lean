# Lean formalization

This directory is the reproducible Lean/mathlib project for the repository's
machine-checked functional-inequality results. It contains the reusable Poincaré
API and the complete Lean certificate for the linear-test lower bound in Issue #2.
The default build includes `../solutions/LemLinearTestLower.lean`.

## Pinned versions

- Lean: `leanprover/lean4:v4.33.0` (see `lean-toolchain`)
- mathlib: tag `v4.33.0`, resolved by `lake-manifest.json` to commit
  `db584cd6d46c92f209a44c0f1c829460d327499d`

Elan reads `lean-toolchain` automatically. From a clean checkout, install
[Elan](https://github.com/leanprover/elan) if necessary, then run:

```bash
cd formalization
lake build
```

Lake downloads the pinned mathlib dependency on the first build. The local
`.lake/` directory is intentionally ignored; `lake-manifest.json` is committed
and is the dependency lock file. The default build compiles both the reusable
library and the repository-root certificate
`solutions/LemLinearTestLower.lean`. This is also the exact command that CI
should run from a clean checkout.

## Updating dependencies

Choose a compatible Lean/mathlib release, change both `lean-toolchain` and the
`rev` in `lakefile.toml`, and then regenerate and verify the lock file:

```bash
cd formalization
lake update
lake build
```

Commit the three pinning files together: `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.  Do not replace a release pin with an unpinned branch.

## Module boundary

Reusable definitions and theorems live under `FunctionalInequalities/`:

- `FunctionalInequalities/Basic.lean` defines the smooth finite-energy `L²`
  test core, canonical gradient Dirichlet energy, its Fréchet-derivative norm
  identity, the fixed-constant predicate `HasPoincare`, and the `ENNReal`-valued
  `optimalPoincareConstant` (including the no-finite-constant case `⊤`).
- `FunctionalInequalities/Poincare.lean` defines linear tests, the extended
  Rayleigh quotient, the centered covariance operator, its supremal Rayleigh
  value, the finite-dimensional eigenvalue bridge, and the fixed/optimal
  covariance lower bounds.
- `FunctionalInequalities/Project/LinearTestLower.lean` packages the reusable
  API into the exact finite-dimensional probability statement of
  `lem:linear-test-lower`.
- `../solutions/LemLinearTestLower.lean` is the thin node-specific certificate.

The design choices, theorem scope, and current limitations are recorded in
`../LEAN_DESIGN.md`.
