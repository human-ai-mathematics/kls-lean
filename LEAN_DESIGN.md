# Lean design: Poincaré linear-test certificate

This document records the implemented Lean architecture for Issue #2 and the semantic contract
behind its linear-test lower bound. The machine proof is intentionally limited to this elementary
lower bound; Gaussian Poincaré inequalities, tensorization, log-Sobolev inequalities,
Bakry--Émery, Otto--Villani, mode-indicator tests, and the KLS conjecture itself remain outside its
scope.

## Reproducible project

The project under `formalization/` pins Lean and Mathlib to release `v4.33.0`.
`formalization/lake-manifest.json` resolves Mathlib to commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. From the repository root, build it with:

```bash
cd formalization
lake build
```

The default targets compile the reusable `FunctionalInequalities` library and the root-level
certificate `solutions/LemLinearTestLower.lean` through the `Issue2Solutions` library.

## Formalized statement

The source is Definition 2.1 and the linear-test part of Remark 3.8 in `KLS.pdf`. For a probability
measure with finite second moment on a finite-dimensional real Hilbert space, the certificate
proves both

$$
R_\mu(f)\le C_P(\mu)
$$

for every admissible test and

$$
\lambda_{\max}(\operatorname{Cov}_\mu)\le C_P(\mu).
$$

The second conclusion is obtained from the first by testing with
$f_v(x)=\langle v,x\rangle$. The proof uses the definition of the optimal Poincaré constant,
the linear-test variance and energy identities, and finite-dimensional Rayleigh--Ritz.

## Semantic contract

`FunctionalInequalities.Basic` implements the manuscript normalization

$$
\operatorname{Var}_\mu(f)\le C\int \lVert\nabla f\rVert^2\,d\mu.
$$

The exact choices are:

- `Poincare.Admissible μ f` means that `f` is globally smooth, belongs to $L^2(\mu)$, and has
  integrable squared gradient. The finite-energy field prevents Lean's totalized real integral
  from silently assigning an unintended value to a nonintegrable energy. This is the smooth
  finite-energy core; no equivalence with a closed Sobolev or spectral-gap domain is claimed.
- `Poincare.energy μ f` is the real integral of the squared norm of Mathlib's canonical gradient.
  A bridge theorem identifies it with the squared operator norm of the Fréchet derivative.
- `Poincare.Holds μ C` is a `Prop`-valued structure containing probability normalization,
  nonnegativity of `C`, and the fixed-constant inequality for every admissible test.
- `Poincare.constant μ : ℝ≥0∞` is the infimum of all finite nonnegative constants satisfying
  `Poincare.Holds μ C`. It is `⊤` exactly when no finite valid constant exists.
- `Poincare.rayleigh μ f : ℝ≥0∞` divides only after mapping variance and energy into extended
  nonnegative reals. Thus positive variance over zero energy is `⊤`, while `0 / 0 = 0`. At
  positive energy it equals the ordinary real quotient from the manuscript.

The theorem quantifies over every `Poincare.Admissible` test, including constant functions. The
formal statement does not use “nonconstant” as a substitute for positive energy, since that
implication fails for an arbitrary measure.

## Centered covariance and the spectral supremum

Mathlib's `ProbabilityTheory.covarianceOperator` is an uncentered second-moment operator, so it is
not the covariance object used in the manuscript. `Covariance.operator μ` is instead the Riesz
operator associated with Mathlib's centered `covarianceBilin μ`. Under `MemLp id 2 μ`, its
quadratic form is the variance of the corresponding linear test.

Mathlib totalizes `covarianceBilin`; outside its square-integrability regime it does not express
the intended finite centered covariance. The certificate therefore states `MemLp id 2 μ`
explicitly rather than relying on the totalized value.

`Covariance.rayleighMax μ : ℝ` is the supremum of the covariance-operator Rayleigh quotient over
nonzero vectors. The formal API proves that:

1. it equals the supremum of $v^T\operatorname{Cov}_\mu v$ over the unit sphere;
2. it is nonnegative because the centered covariance form is positive semidefinite;
3. in a nontrivial finite-dimensional space it is attained and is an eigenvalue of the centered
   covariance operator; and
4. `Covariance.lambdaMax μ : ℝ≥0∞` is `ENNReal.ofReal (Covariance.rayleighMax μ)`, with `toReal`
   equal to `Covariance.rayleighMax μ`.

The name `lambdaMax` follows the manuscript's notation without asserting that the supremum is an
eigenvalue in every ambient space. In infinite dimension it need not be attained. In dimension
zero there are no nonzero vectors or eigenvectors; the empty Rayleigh supremum and `lambdaMax` are
defined to be `0`. This makes the certificate uniform in `D : ℕ`, including `D = 0`.

On a finite-dimensional Euclidean space, `MemLp id 2 μ` is the coordinate-free assumption of a
finite second moment that makes the centered covariance matrix finite.

## Proof and module boundary

- `formalization/FunctionalInequalities/Basic.lean`: admissibility, energy, fixed constants, and
  the optimal extended Poincaré constant.
- `formalization/FunctionalInequalities/Poincare.lean`: linear tests, extended Rayleigh quotients,
  centered covariance, the finite-dimensional eigenvalue bridge, and the fixed/optimal bounds.
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`: the project-level Issue #2
  theorem.
- `solutions/LemLinearTestLower.lean`: the thin node-specific certificate.

Compilation is enforced by `lake build`, whose default targets include the root-level certificate.
The certificate proves only the two lower-bound conclusions above and makes no claim about a
Poincaré upper bound, Gaussian equality, or the nonlinear parts of Remark 3.8.

## Repository certification

`research/a-series/ledger.yaml` connects `lem:linear-test-lower` to
`solutions/LemLinearTestLower.lean` with `checked_by: lean`. The dependency-free command

```bash
python3 research/check_ledger.py
```

checks that the certificate exists below `solutions/`, names the node, contains no Lean escape
tokens, and belongs to a default Lake target. Its focused regression tests run with:

```bash
python3 -m unittest discover -s research/tests -p 'test_*.py'
```

The checker establishes repository structure and provenance; `lake build` performs compilation,
and semantic agreement with the reference remains a separate review obligation.

`.github/workflows/lean.yml` runs these two Python commands and the default Lean build on every
push and pull request. It uses Python 3.12 without third-party packages and the official
`leanprover/lean-action@v1`, with `lake-package-directory: formalization`, an explicit build, and
`use-mathlib-cache: 'true'` (the action runs `lake exe cache get` before building).

## Contribution workflow (2026-09-03)

Work directly on `main`. Keep unfinished follow-up work as local, uncommitted changes and push
completed work directly to `origin/main` after its acceptance checks pass. Do not create feature
branches or pull requests for this workflow. Human statement review and the statement/proof role
separation still apply before proof work begins.
