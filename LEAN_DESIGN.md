# Lean design: Poincaré linear-test certificate

This document records the implemented Lean architecture for Issue #2 and the semantic contract
behind ledger node `lem:linear-test-lower`. The machine proof is intentionally limited to this
elementary lower bound; Gaussian Poincaré, tensorization, log-Sobolev inequalities,
Bakry--Émery, Otto--Villani, and the KLS backbone remain separate work.

## Reproducible project

The independent project under `formalization/` pins Lean and mathlib to release `v4.33.0`.
`formalization/lake-manifest.json` resolves mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`. The required clean-checkout command is:

```bash
cd formalization
lake build
```

The default targets compile the reusable `FunctionalInequalities` library and the root-level
node certificate `solutions/LemLinearTestLower.lean` through the `Issue2Solutions` library.

## Source statement and natural-language proof

The manuscript convention is `modules/01-definitions.tex` (`def:poincare`), the labeled source
statement is `modules/02-results-toolkit.tex` (`rem:rayleigh-lower-only`), and the complete
natural-language proof is `solutions/glm-linear-baselines.tex`
(`lem:sol-linear-test-lower`). The existing independent review is
`research/reviews/2026-08-25-ab-inline-r2-audit.md`.

No research-level external theorem is needed for `lem:linear-test-lower`: its proof is the
definition of the Poincaré constant, the calculation for $f_v(x)=\langle v,x\rangle$, and finite-
dimensional Rayleigh--Ritz. The Bakry--Émery and Otto--Villani citations in the shared TeX dossier
belong to the separate GLM upper-bound theorem, not this node. Lean uses Mathlib's proved APIs for
variance, Fréchet derivatives and gradients, centered covariance bilinear forms, Riesz
representation, and finite-dimensional Rayleigh quotients.

## Semantic contract

`FunctionalInequalities.Basic` implements the manuscript normalization

$$
\operatorname{Var}_\mu(f)\le C\int \lVert\nabla f\rVert^2\,d\mu.
$$

The exact choices are:

- `IsAdmissible μ f` means globally smooth, in $L^2(\mu)$, and with integrable squared gradient.
  The finite-energy field prevents Lean's totalized real integral from silently assigning an
  unintended value to a nonintegrable energy. This is the conventional smooth finite-energy
  core; no equivalence with a closed Sobolev or spectral-gap domain is claimed here.
- `dirichletEnergy` is the real integral of the squared canonical gradient. A bridge theorem
  identifies it with the squared operator norm of the Fréchet derivative.
- `HasPoincare μ C` includes probability normalization, $0\le C$, and the fixed-$C$ inequality
  for every admissible test.
- `optimalPoincareConstant μ : ℝ≥0∞` is the infimum of all finite nonnegative valid constants.
  It is `⊤` exactly when no finite valid constant exists.
- `poincareRayleighQuotient μ f : ℝ≥0∞` divides only after mapping variance and energy into
  extended nonnegative reals. Consequently positive variance over zero energy is `⊤`, while
  `0 / 0 = 0`; no real-number division-by-zero convention leaks into the theorem. At positive
  energy it is proved equal to the manuscript's ordinary real quotient.

The ledger sentence says “any test function”; the machine theorem quantifies over every
`IsAdmissible` test, including constants. This is stronger and removes the natural-language
phrase “nonconstant,” which by itself would not imply positive Dirichlet energy for an arbitrary
measure.

## Centered covariance and largest eigenvalue

Mathlib's `ProbabilityTheory.covarianceOperator` is an uncentered second-moment operator, so it is
not the object in the manuscript. `centeredCovarianceOperator μ` is instead the Riesz operator of
Mathlib's centered `covarianceBilin μ`. Under `MemLp id 2 μ`, its quadratic form is proved equal
to the variance of the linear test.

`covarianceRayleighMax μ : ℝ` is the supremum of the operator Rayleigh quotient over nonzero
vectors. The formal API proves all of the identifications used informally:

1. it equals the supremum of $v^T\operatorname{Cov}_\mu v$ over the unit sphere;
2. it is nonnegative because the centered covariance form is positive semidefinite;
3. in a nontrivial finite-dimensional space it is an actual eigenvalue of the same centered
   covariance operator; and
4. `lambdaMaxCovariance μ : ℝ≥0∞` is its faithful extended-nonnegative representation, with
   `toReal` equal to `covarianceRayleighMax μ`.

For the zero-dimensional space, the nonzero-vector and unit-sphere index types are empty. The
chosen convention is an empty real supremum of `0`, hence `lambdaMaxCovariance μ = 0`. This makes
the theorem uniform in `D : ℕ`, including `D = 0`.

`MemLp id 2 μ` is the explicit finite-second-moment assumption. On a finite-dimensional Euclidean
space it is the coordinate-free form of finiteness of the covariance matrix. The certificate
states this assumption rather than hiding it behind an informal “finite covariance” phrase.

## Proof/module boundary

- `formalization/FunctionalInequalities/Basic.lean`: reusable admissibility, energy, fixed and
  optimal constants.
- `formalization/FunctionalInequalities/Poincare.lean`: extended Rayleigh quotient, linear-test
  calculus, centered covariance, eigenvalue bridge, and fixed/optimal bounds.
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`: exact project theorem.
- `solutions/LemLinearTestLower.lean`: node-specific certificate whose header names
  `lem:linear-test-lower`.

The checker accepts an explicit `lean_solution:` path under `solutions/`, verifies its `.lean`
suffix, existence, and node token, and retains the adjacent-file convention only for backward
compatibility. Compilation is enforced by `lake build`, whose default targets include the
certificate.

After the term-by-term semantic alignment recorded in
`research/reviews/2026-08-29-lean-linear-test-semantic-followup.md`, the sole ledger orchestrator
completed the metadata transition to `checked_by: lean` with
`lean_solution: solutions/LemLinearTestLower.lean`. The existing natural-language
`solution: solutions/glm-linear-baselines.tex` remains the analytic dossier. This certification
does not assert an equivalence between the selected smooth finite-energy core and a closed
Sobolev or spectral-gap definition.
