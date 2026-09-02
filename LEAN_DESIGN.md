# Lean design: Poincaré certificates

This document records the implemented Lean architecture for Issue #2 and the semantic contract
behind its linear-test lower bound. The machine proof is intentionally limited to this elementary
lower bound; Gaussian Poincaré inequalities, tensorization, log-Sobolev inequalities,
Bakry--Émery, Otto--Villani, mode-indicator tests, and the KLS conjecture itself remain outside its
scope.

## Tensorization design and candidate statements (2026-09-03)

Status: **drafted**, awaiting human review. Codex owns the statements and compilable skeletons;
a separate proof agent works only after a human freezes the public signatures. Every new theorem
and proposition-valued instance ends with `sorry`. Compiling these modules does not prove them.

The binary Hilbert product is `WithLp 2 (E × F)`, using Mathlib's
`Analysis.InnerProductSpace.ProdL2`. Ordinary `E × F` has the maximum norm, which is not the
Hilbert product norm. No global or local replacement of its norm/inner-product instances is
permitted. The measurable structure is Mathlib's transported structure from
`Analysis.Normed.Lp.MeasurableSpace`.

Define `Poincare.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)`. This is the same product
probability law expressed on the Hilbert product, not a change of normalization. Use the
measurable equivalence `MeasurableEquiv.toLp 2 (E × F)` to transport integrability, variance,
and integrals. Its continuous linear counterpart is `WithLp.prodContinuousLinearEquiv`.

After auditing the pinned Mathlib sources, propose the public signatures under these ambient
assumptions (real separable Hilbert spaces with their Borel sigma algebras; in particular all
finite-dimensional Euclidean factors are covered):

```lean
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

theorem Poincare.Holds.prod
    {μ : Measure E} {ν : Measure F} {C C' : ℝ}
    (hμ : Poincare.Holds μ C) (hν : Poincare.Holds ν C') :
    Poincare.Holds (Poincare.prodMeasure μ ν) (max C C') := sorry

theorem Poincare.constant_prod_le
    {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Poincare.constant (Poincare.prodMeasure μ ν) ≤
      max (Poincare.constant μ) (Poincare.constant ν) := sorry
```

`Holds` already carries probability normalization and nonnegative constants. The candidate ledger
statement is: for Borel probability measures on real separable Hilbert spaces, if the smooth
L2 finite-energy Poincaré inequalities hold with constants C and C', the Hilbert product law
satisfies the same inequality with max(C,C'); consequently its extended optimal constant is at
most max(C_P(mu),C_P(nu)), including infinite constants. The normalization remains
`Var(f) ≤ C ∫ ‖gradient f‖²`.

The proof architecture does not differentiate an integral. Smoothness restricts to every
section, but the L2 and finite-energy fields restrict only to almost every section. For example,
with `ν = δ₀` and `f(x,y) = y² exp(x²)`, the product test and its gradient vanish on the support,
whereas a section at `y ≠ 0` need not be L2 for a Gaussian first factor. Thus the section lemmas
must be a.e. statements. This clarifies the intermediate proof obligation before freezing; no
every-section hypothesis is added to `Admissible` or to either tensorization theorem.

The future proof phase should prove the gradient projections and their squared-norm sum first,
then a.e. admissibility of
sections. Assemble the bound through the two-factor variance inequality
`Var(f) ≤ ∫ Var(f(·,y)) dν + ∫ Var(f(x,·)) dμ`, using Fubini and L2 estimates. Every use of a real
integral retains explicit integrability evidence. Finally take infima over both finite valid
constants in `ENNReal`; no attainment or finiteness of the optimal constants is assumed.

The existing `Admissible`, `energy`, `Holds`, and `constant` definitions remain the semantic
contract. See `research/decisions/2026-09-03-hilbert-product-tensorization.md` for the audit and
global encoding decision. The statement/proof role boundary is
recorded in `research/decisions/2026-09-03-statement-proof-separation.md`. This section proposes
a specification for human freezing; it does not freeze or certify it.

## Reproducible project

The project under `formalization/` pins Lean and Mathlib to release `v4.33.0`.
`formalization/lake-manifest.json` resolves Mathlib to commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. From the repository root, build it with:

```bash
cd formalization
lake build
```

The default targets compile the reusable `FunctionalInequalities` library, the root-level proved
certificate `solutions/LemLinearTestLower.lean`, and the drafted statement entry point
`solutions/LemPoincareTensorization.lean` through the `Issue2Solutions` library.

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
- `formalization/FunctionalInequalities/ProductGeometry.lean`: transported product law and draft
  smoothness/gradient statements.
- `formalization/FunctionalInequalities/ProductVariance.lean`: draft L2/Fubini variance statements.
- `formalization/FunctionalInequalities/ProductAdmissible.lean`: draft finite-energy and a.e.
  admissibility statements.
- `formalization/FunctionalInequalities/Tensorization.lean`: the two candidate public theorems.
- `solutions/LemPoincareTensorization.lean`: the draft node entry point, importing and naming the
  public declarations without a proof wrapper.

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

The tensorization node is `status: drafted` with `checked_by: null`. The lifecycle and checker
rules are specified in `research/ledger-schema.md`. Drafted/frozen declarations may contain
`sorry` and must still compile in the default build. Only proved nodes may claim
`checked_by: lean`; their entry points and local imports undergo the static escape-token check.

`.github/workflows/lean.yml` runs these two Python commands and the default Lean build on every
push and pull request. It uses Python 3.12 without third-party packages and the official
`leanprover/lean-action@v1`, with `lake-package-directory: formalization`, an explicit build, and
`use-mathlib-cache: 'true'` (the action runs `lake exe cache get` before building).
