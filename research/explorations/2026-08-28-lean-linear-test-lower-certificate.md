# Lean certificate for the linear-test Poincaré lower bound

**Date:** 2026-08-28 (Asia/Shanghai)

**Branch:** `codex/issue-2-linear-test-lower`

**Ledger node:** `lem:linear-test-lower`

**Scope:** Complete Lean implementation and node-specific certificate, with no ledger write. The
production ledger remains owned by its sole orchestrator.

## Statement and proof sources

The target is

$$
C_P(\mu)\ge \lambda_{\max}(\operatorname{Cov}_\mu)
$$

for a probability measure on a finite-dimensional real Euclidean space with finite second moment,
together with the general test-function Rayleigh lower bound. The repository sources are:

- `modules/01-definitions.tex`, `def:poincare`, for normalization;
- `modules/02-results-toolkit.tex`, `rem:rayleigh-lower-only`, for the manuscript statement;
- `solutions/glm-linear-baselines.tex`, `lem:sol-linear-test-lower`, for the complete
  natural-language proof; and
- `research/reviews/2026-08-25-ab-inline-r2-audit.md` for the prior independent analytic review.

The linear-test node itself uses no research-level imported theorem. The Bakry--Émery and
Otto--Villani citations in the shared dossier support the separate GLM upper-bound theorem. The
Lean proof relies on Mathlib's established variance, Fréchet derivative/gradient, centered
covariance bilinear form, Riesz representation, and finite-dimensional Rayleigh APIs.

## Semantic audit and repaired contract

Three distinctions had to be made explicit before compilation could count as certification.

First, the manuscript's smooth $L^2$ convention needs a finite-energy interpretation because
Mathlib's real integral is totalized on nonintegrable functions. `IsAdmissible μ f` therefore
requires global smoothness, `MemLp f 2 μ`, and integrability of
$x\mapsto\lVert\nabla f(x)\rVert^2$. `dirichletEnergy` uses the canonical Hilbert-space gradient,
and a bridge theorem proves equality with the Fréchet-derivative operator-norm formula. No
smooth-core/Sobolev-closure equivalence is claimed.

Second, the natural-language phrase “every admissible nonconstant test” does not by itself ensure
positive energy for an arbitrary measure. An early Lean statement used
`ENNReal.ofReal (variance / energy)` only under a positive-energy hypothesis. That is a correct
specialization but not the full extended-value statement. The final
`poincareRayleighQuotient` maps numerator and denominator separately to `ℝ≥0∞` before division.
Thus positive variance over zero energy is `⊤`, `0 / 0 = 0`, and every admissible test satisfies
the optimal-constant bound. A separate theorem recovers the ordinary real quotient whenever the
energy is positive.

Third, Mathlib's object named `covarianceOperator` is an uncentered second-moment operator. Using
it would make the formal theorem false as a translation of the manuscript. The final
`centeredCovarianceOperator` is the Riesz operator of `covarianceBilin`. Under `MemLp id 2 μ`, its
quadratic form is exactly the variance of the corresponding linear test.

The real `covarianceRayleighMax` is defined as the supremum of this operator's Rayleigh quotient
over nonzero vectors. The formal development proves that it equals the covariance quadratic-form
supremum over the unit sphere, is nonnegative, and is an actual eigenvalue in every nontrivial
finite-dimensional space. `lambdaMaxCovariance : ℝ≥0∞` is `ENNReal.ofReal` of this same real
quantity, with a proved `toReal` identity. In dimension zero the relevant index type is empty and
the chosen value is $0$.

The optimal constant is the `ℝ≥0∞` infimum of all finite nonnegative valid constants. Hence it is
`⊤` exactly when no finite Poincaré constant exists, and the proof does not pretend to instantiate
a real constant when $C_P(\mu)=+\infty$.

## Implemented modules

- `formalization/FunctionalInequalities/Poincare.lean` provides the reusable linear-test,
  extended Rayleigh, centered covariance, eigenvalue, and optimal-constant API.
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean` packages the exact
  finite-dimensional probability statement.
- `solutions/LemLinearTestLower.lean` is the thin certificate whose header names
  `lem:linear-test-lower`.
- The `Issue2Solutions` Lake library makes the root-level certificate part of the default
  `lake build` target.

The explicit finite-second-moment assumption is `MemLp id 2 μ`. In finite-dimensional Euclidean
space this is the coordinate-free version of finite covariance. The project theorem includes
`FiniteDimensional ℝ E`, `IsProbabilityMeasure μ`, the Borel structure, and this moment hypothesis
explicitly.

## Dead ends and Mathlib friction

- The first covariance representation took an `ENNReal` supremum directly over the unit sphere.
  It proved the numerical inequality, but the separate eigenvalue theorem referred to a real
  nonzero-vector supremum. An attempted proof equating the two nested supremum/coercion
  formulations exceeded one million heartbeats. Defining the real Rayleigh maximum first and
  mapping it once to `ENNReal` eliminated the duplicate semantic object.
- Suprema over nonzero vectors require explicit `Nonempty` evidence in the nontrivial branch.
  Dimension zero requires an explicit `IsEmpty` instance and `Real.iSup_of_isEmpty`; relying on
  typeclass inference obscured the boundary case.
- Moving the node certificate above `formalization/` required a second Lake library with
  `srcDir = ".."`; otherwise the default build could compile the reusable library while silently
  omitting the actual ledger artifact.

## Validation to date

The following checks passed on the pinned toolchain:

```text
cd formalization && lake build
Build completed successfully (2946 jobs).

uv run --with pyyaml python -m unittest discover -s research/tests -p 'test_*.py'
Ran 44 tests ... OK
```

An explicit `#print axioms` audit of the foundation, semantic bridge theorems, project theorem,
and node certificate reported only Lean/Mathlib's standard `propext`, `Classical.choice`, and
`Quot.sound`. A repository search found no `sorry`, `admit`, or custom `axiom` in the implemented
modules, and `git diff --check` passed.

## Remaining certification boundary

This branch does not edit `research/a-series/ledger.yaml`. The intended sole-orchestrator change
is to retain `solution: solutions/glm-linear-baselines.tex`, set `checked_by: lean`, and add
`lean_solution: solutions/LemLinearTestLower.lean` after review of this semantic correspondence.
Structural checker success is necessary but does not replace that semantic review.
