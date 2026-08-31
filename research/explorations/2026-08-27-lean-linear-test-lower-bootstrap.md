# Lean linear-test lower bound: API audit and project bootstrap

**Date:** 2026-08-27 (Asia/Taipei)

**Branch:** `codex/issue-2-linear-test-lower`

**Ledger node:** `lem:linear-test-lower`

**Scope:** Phase A and the smallest Phase B bootstrap; no ledger edit and no claim of Lean
certification.

## Repository audit

The node `lem:linear-test-lower` is already `status: proved` and `checked_by: agent`, backed by
the intact shared natural-language dossier `solutions/glm-linear-baselines.tex`.  This session did
not alter that dossier or `research/ledger.yaml`.  The checker currently accepts
`checked_by: lean` as a certification value but has no `lean_solution:` path validation yet; that
integration remains Phase F work and must not be activated before the complete theorem compiles.

The theorem to be matched includes a probability measure on a finite-dimensional real Euclidean
space, finite covariance, the optimal Poincare constant in $[0,+\infty]$, and the centered
covariance maximum.  Proving only a fixed-$C$ Rayleigh inequality will not match the ledger node.

## Reproducible pin

The host already had Lean `v4.33.0`.  The official mathlib tag `v4.33.0` resolves to
`db584cd6d46c92f209a44c0f1c829460d327499d`.  The new `formalization/` project pins both releases,
tracks the generated `lake-manifest.json`, ignores only the local `.lake/` build/dependency tree,
and builds from the root module with:

```bash
cd formalization
lake build
```

The root module is intentionally only an import smoke test.  It does not define a Poincare
predicate and does not certify the target node.

## Mathlib v4.33.0 API findings

The two direct imports used by the bootstrap are:

```lean
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Probability.Moments.CovarianceBilin
```

An exact `#check` probe compiled for the following declarations:

- `MeasureTheory.MemLp`: use `MemLp id 2 μ` as the explicit finite-second-moment hypothesis.
- `ProbabilityTheory.variance` and `ProbabilityTheory.variance_eq_integral`: real-valued variance
  exists, but `variance` is defined as `evariance.toReal` and becomes zero outside $L^2$; proofs
  must carry `MemLp` rather than rely on this totalized behavior.
- `ProbabilityTheory.covarianceBilin`: the centered covariance is already available as a
  continuous bilinear form on a real Hilbert space.
- `ProbabilityTheory.covarianceBilin_self`: under completeness, finite measure, and
  `MemLp id 2 μ`, it identifies `covarianceBilin μ x x` with
  `Var[fun u => inner ℝ x u; μ]`.  This is the key bridge for linear tests.
- `ProbabilityTheory.covarianceOperator` and `covarianceOperator_inner`: despite the name, this
  operator is explicitly **uncentered**; its quadratic form is
  $\int\langle x,z\rangle\langle y,z\rangle\,d\mu(z)$.  It is not the covariance operator needed
  by the ledger theorem unless the measure is centered.
- `InnerProductSpace.continuousLinearMapOfBilin` and
  `continuousLinearMapOfBilin_apply`: these provide the Riesz representation needed to define a
  centered operator from `covarianceBilin μ` without introducing a coordinate matrix.
- `ContinuousLinearMap.hasFDerivAt`, `innerSL`, and `innerSL_apply_norm`: the projection
  $u\mapsto\langle x,u\rangle$ is the continuous linear map `innerSL ℝ x`, its Frechet derivative
  is itself, and its operator norm is `‖x‖`.
- `ContinuousLinearMap.rayleighQuotient` and `rayleighQuotient_le_norm`: mathlib packages the
  real Rayleigh quotient and its operator-norm upper bound.
- `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`: for a nontrivial
  finite-dimensional inner-product space, the supremum over nonzero Rayleigh quotients is an
  eigenvalue.  Its `[Nontrivial E]` hypothesis means the zero-dimensional case must be a separate
  branch or excluded explicitly.

This is materially newer than the prior `LEAN_DESIGN.md` audit: centered `covarianceBilin` now
exists in mathlib.  What is still missing is a ready-made centered covariance **operator** paired
with the exact maximum-eigenvalue statement needed here.

## Design consequences and still-open choices

1. Prefer an abstract finite-dimensional real Hilbert-space API and define the centered operator
   by applying `continuousLinearMapOfBilin` to `covarianceBilin μ`.  A coordinate matrix can be a
   later corollary if the ledger/manuscript audit demands coordinates.
2. Never reuse mathlib's `covarianceOperator` under the centered interpretation; doing so would
   prove the wrong theorem for measures with nonzero mean.
3. Define the admissible test-function contract so measurability, $L^2$ membership, Frechet
   differentiability, and energy integrability are visible.  The projection admissibility proof
   should be derived from `MemLp id 2 μ`.
4. The constant type remains undecided.  `ℝ` is convenient for fixed finite constants but cannot
   represent the dossier's $+\infty$ case.  `ℝ≥0∞` represents the optimal constant honestly but
   requires an explicit bridge from real variance/energy inequalities.  This trade-off must be
   settled before Phase C, not silently in the bootstrap.
5. The zero-dimensional case and inclusion of a root-level `solutions/*.lean` certificate in the
   default Lake target remain open integration questions.

## Rejected or failed approaches

- Rejected mathlib's `ProbabilityTheory.covarianceOperator` as the target covariance object
  because its source documentation and `covarianceOperator_inner` show that it is uncentered.
- Rejected treating `ProbabilityTheory.variance` as sufficient without an $L^2$ hypothesis,
  because infinite variance is totalized to zero.
- Rejected choosing `ℝ`, `ℝ≥0`, or `ℝ≥0∞` for the optimal constant during this bootstrap; doing so
  before the reusable admissibility/API design would prejudge the $+\infty$ semantics.
- The first `lakefile.toml` used a `[package]` table.  Lake 5 rejected it with
  `missing required key: name`; package keys must be top-level.
- The first root module placed its module doc comment before imports.  Lean 4.33 rejected the
  imports as not being at the beginning of the file; moving the imports first fixed the build.
- A cold Lake dependency clone was quiet and very large.  For this session only, the ignored
  package cache was seeded from a separately verified shallow checkout at the same commit; Lake
  then performed its own remote verification, generated the normal manifest, ran mathlib's
  post-update hook, and compiled successfully.  No local-path dependency or generated cache is
  committed.

## Validation in this session

- `lake env lean /private/tmp/kls-issue2-mathlib-api-probe.lean` — **passed**; all declarations
  listed above resolved with the recorded types.
- `cd formalization && lake build` — **passed** after the two bootstrap syntax fixes; 2,940 jobs
  completed.
- `python3 research/check_ledger.py` — **environment failure before validation**: the
  Homebrew-default Python 3.14 lacks PyYAML.
- `python3 -m unittest discover -s research/tests -p 'test_*.py'` — **environment failure before
  validation** for the same missing PyYAML dependency.
- `/usr/bin/python3 research/check_ledger.py` — **passed** with 2 ledgers, 172 nodes, 632 labels,
  0 errors, and 0 warnings; system Python has PyYAML 6.0.3.
- `/usr/bin/python3 -m unittest discover -s research/tests -p 'test_*.py'` — **passed**, all 23
  tests.
- The final staged `git diff --check` is recorded in the session-close commit/push report.

## Next exact proof action

In `FunctionalInequalities/Basic.lean`, settle the constant/energy codomains and define reusable
admissibility, Dirichlet energy, and `HasPoincare`.  Before proving any optimal-constant theorem,
compile a small centered-covariance operator definition and prove its quadratic-form identity via
`covarianceBilin_self`, including an explicit zero-dimensional case analysis.  Do not add a
node-specific certificate or change ledger certification until the fixed-$C$, Rayleigh maximum,
and optimal-constant layers all compile and are semantically audited.
