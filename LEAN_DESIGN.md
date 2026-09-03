# Lean design: Poincaré certificates

This document records the implemented Lean architecture and semantic contracts for the Issue #2
linear-test lower bound, Issue #6 two-factor Poincaré tensorization, and Issue #7 finite-product
tensorization with optimal-constant equality. Gaussian
Poincaré inequalities, log-Sobolev inequalities, Bakry--Émery, Otto--Villani, mode-indicator tests,
and the KLS conjecture itself remain outside the certified scope.

## Tensorization design and accepted statements (2026-09-03)

The tensorization proofs are complete, and the node is recorded as **proved** with
`checked_by: lean`. The user's acceptance, complete public signatures, and ledger statement are
recorded in `research/decisions/2026-09-03-tensorization-freeze.md`. Source correspondence,
semantic review, and validation evidence are recorded in
`research/explorations/2026-09-03-tensorization-acceptance.md`. That record distinguishes local
verification from CI for the final published commit.

The binary Hilbert product is `WithLp 2 (E × F)`, using Mathlib's
`Analysis.InnerProductSpace.ProdL2`. Ordinary `E × F` has the maximum norm, which is not the
Hilbert product norm. No global or local replacement of its norm/inner-product instances is
permitted. The measurable structure is Mathlib's transported structure from
`Analysis.Normed.Lp.MeasurableSpace`.

Define `Poincare.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)`. This is the same product
probability law expressed on the Hilbert product, not a change of normalization. Use the
measurable equivalence `MeasurableEquiv.toLp 2 (E × F)` to transport integrability, variance,
and integrals. Its continuous linear counterpart is `WithLp.prodContinuousLinearEquiv`.

The public results apply under these ambient assumptions: real separable Hilbert spaces with
their Borel sigma algebras, including finite-dimensional Euclidean factors of any natural-number
dimension. Their use has the following form; the complete elaborated signatures are in the
freeze record:

```lean
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

example
    {μ : Measure E} {ν : Measure F} {C C' : ℝ}
    (hμ : Poincare.Holds μ C) (hν : Poincare.Holds ν C') :
    Poincare.Holds (Poincare.prodMeasure μ ν) (max C C') :=
  Poincare.Holds.prod hμ hν

example
    {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Poincare.constant (Poincare.prodMeasure μ ν) ≤
      max (Poincare.constant μ) (Poincare.constant ν) :=
  Poincare.constant_prod_le
```

`Holds` already carries probability normalization and nonnegative constants. The accepted ledger
statement is: for Borel probability measures on real separable Hilbert spaces, if the smooth
L2 finite-energy Poincaré inequalities hold with constants C and C', the Hilbert product law
satisfies the same inequality with max(C,C'); consequently its extended optimal constant is at
most max(C_P(mu),C_P(nu)), including infinite constants. The normalization remains
`Var(f) ≤ C ∫ ‖gradient f‖²`.

The proof architecture does not differentiate an integral. Smoothness restricts to every
section, but the L2 and finite-energy fields restrict only to almost every section. For example,
with `ν = δ₀` and `f(x,y) = y² exp(x²)`, the product test and its gradient vanish on the support,
whereas a section at `y ≠ 0` need not be L2 for a Gaussian first factor. Thus the section lemmas
are a.e. statements. Neither `Admissible` nor either tensorization theorem requires every section
to be admissible.

The proof establishes the gradient projections and their squared-norm sum, then a.e.
admissibility of sections. It assembles the bound through the two-factor variance inequality
`Var(f) ≤ ∫ Var(f(·,y)) dν + ∫ Var(f(x,·)) dμ`, using Fubini and L2 estimates. Every use of a real
integral retains explicit integrability evidence. The optimal-constant argument uses finite
valid constants strictly below a hypothetical counterexample to the infimum bound in `ENNReal`;
no attainment or finiteness of the optimal constants is assumed.

The existing `Admissible`, `energy`, `Holds`, and `constant` definitions remain the semantic
contract. In particular, this theorem concerns globally smooth real-valued L2 tests with finite
gradient energy. It does not identify that test class with a closed Dirichlet domain, a Sobolev
space, or all locally Lipschitz tests for arbitrary Borel measures. The source comparison with
BGL Proposition 4.3.1 and the use in the manuscript's `prop:products` are recorded in
`research/explorations/2026-09-03-tensorization-source-alignment.md`. The finite-product extension
is described below as an accepted Lean certificate; the further inputs to the product-case
KLS result remain follow-up work.

The initial encoding audit and statement/proof ownership decision remain in
`research/decisions/2026-09-03-hilbert-product-tensorization.md` and
`research/decisions/2026-09-03-statement-proof-separation.md`. Those historical records describe
the earlier draft stage; the freeze and acceptance records document the current state.

## Reproducible project

The project under `formalization/` pins Lean and Mathlib to release `v4.33.0`.
`formalization/lake-manifest.json` resolves Mathlib to commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. From the repository root, build it with:

```bash
cd formalization
lake build
```

The default targets compile the reusable `FunctionalInequalities` library and the three
root-level certificates: `solutions/LemLinearTestLower.lean`,
`solutions/LemPoincareTensorization.lean`, and
`solutions/LemPoincareFiniteTensorization.lean`.

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

`FunctionalInequalities.Poincare.Basic` implements the manuscript normalization

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

The name `lambdaMax` follows the manuscript's notation. The current Lean eigenvalue theorem is
limited to nontrivial finite-dimensional spaces; the infinite-dimensional covariance compactness
argument has not been formalized. Mathematically, finite second moment makes a Hilbert probability's
centered covariance positive and trace-class: apply
[Blanchard--Bousquet--Zwald, Theorem 2.1](https://doc.ml.tu-berlin.de/publications/publications/BlaBouZwa06.pdf#page=8)
to the centered random vector. Compact self-adjoint spectral theory then gives attainment of its
Rayleigh maximum on any nontrivial Hilbert space, including when the covariance is zero.
In dimension zero there are no nonzero vectors or eigenvectors; the empty Rayleigh supremum and
`lambdaMax` are defined to be `0`. This makes the certificate uniform in `D : ℕ`, including `D = 0`.

On a finite-dimensional Euclidean space, `MemLp id 2 μ` is the coordinate-free assumption of a
finite second moment that makes the centered covariance matrix finite.

## Proof and module boundary

- `formalization/FunctionalInequalities/Poincare/Basic.lean`: admissibility, energy, fixed constants, and
  the optimal extended Poincaré constant.
- `formalization/FunctionalInequalities/Poincare/LinearTest.lean`: linear tests, extended Rayleigh quotients,
  centered covariance, the finite-dimensional eigenvalue bridge, and the fixed/optimal bounds.
- `solutions/LemLinearTestLower.lean`: the sole Issue #2 certificate, directly combining the
  reusable Rayleigh and covariance lower bounds.
- `formalization/FunctionalInequalities/Poincare/Product/Geometry.lean`: transported product law and proved
  smoothness/gradient identities.
- `formalization/FunctionalInequalities/Poincare/Product/Variance.lean`: L2/Fubini variance decomposition
  and the two-factor variance inequality.
- `formalization/FunctionalInequalities/Poincare/Product/Admissible.lean`: finite-energy bounds and a.e.
  admissibility of sections.
- `formalization/FunctionalInequalities/Poincare/Product/Tensorization.lean`: the two proved public theorems.
- `solutions/LemPoincareTensorization.lean`: the sole Issue #6 certificate, directly combining
  both product bounds, with a typed Euclidean application check including dimension zero.
- `formalization/FunctionalInequalities/Poincare/Transport.lean`: measure-preserving coordinate
  lifts and exact transport under real linear isometry equivalences.
- `formalization/FunctionalInequalities/Poincare/Product/Reverse.lean`: binary coordinate reverse
  bounds and optimal-constant equality.
- `formalization/FunctionalInequalities/Poincare/FiniteProduct/Geometry.lean`: the dependent
  `PiLp 2` product law, coordinate projections, reindexing, and Option splitting.
- `formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean`: finite
  fixed-constant tensorization, reverse bounds, optimal equality, and boundary consequences.
- `solutions/LemPoincareFiniteTensorization.lean`: the sole Issue #7 certificate, retaining the
  45 public interface checks plus eight Euclidean families and six boundary applications.

Compilation is enforced by `lake build`, whose default targets include all three root-level
certificates. The linear-test certificate covers the two lower-bound conclusions above; the
two tensorization certificates cover the binary and finite product results. None proves Gaussian
equality or the nonlinear parts of Remark 3.8.

## Repository certification

`research/a-series/ledger.yaml` connects `lem:linear-test-lower`,
`lem:poincare-tensorization`, and `lem:poincare-finite-tensorization` to their respective files
under `solutions/`, all with
`status: proved` and `checked_by: lean`. The dependency-free command

```bash
python3 research/check_ledger.py
```

checks that each certificate exists below `solutions/`, names its node, contains no Lean escape
tokens in itself or its local imports, and belongs to a default Lake target. Its focused
regression tests run with:

```bash
python3 -m unittest discover -s research/tests -p 'test_*.py'
```

The checker establishes repository structure and provenance; `lake build` performs compilation,
and semantic agreement with the reference remains a separate review obligation.

The lifecycle and checker rules are specified in `research/ledger-schema.md`. Future
drafted/frozen declarations may contain placeholders and must still compile in the default
build. Only proved nodes may claim `checked_by: lean`; their entry points and local imports
undergo the static escape-token check. Human review and signature preservation are documented
separately because the metadata checker validates the current state rather than approval history.

`.github/workflows/lean.yml` runs these two Python commands and the default Lean build on every
push and pull request. It uses Python 3.12 without third-party packages and the official
`leanprover/lean-action@v1`, with `lake-package-directory: formalization`, an explicit build, and
`use-mathlib-cache: 'true'` (the action runs `lake exe cache get` before building).

## Contribution workflow (2026-09-03)

Work directly on `main`. Keep unfinished follow-up work as local, uncommitted changes and push
completed work directly to `origin/main` after its acceptance checks pass. Do not create feature
branches or pull requests for this workflow. Human statement review and the statement/proof role
separation still apply before proof work begins.

## Finite tensorization acceptance (2026-09-03; Issue #7)

The node `lem:poincare-finite-tensorization` is **proved** with `checked_by: lean`; the two
existing nodes retain their proved status and certificate signatures. Issue #7 adds
binary coordinate reverse bounds and optimal equality, dependent finite-product upper bounds,
and `constant (piMeasure μ) = ⨆ i, constant (μ i)` in `ENNReal`.

The finite Hilbert carrier is `PiLp 2 E`; its law is
`piMeasure μ := (Measure.pi μ).map (WithLp.toLp 2)`. Every factor is a Borel probability on a
complete real inner product space with second-countable topology. The finite fixed-constant
interface uses `C : ι → NNReal` and casts `Finset.univ.sup C` to `ℝ` for `Holds`. There is no
index nonempty assumption: empty products have fixed and optimal constant zero. Singleton
families, zero-dimensional factors and infinite optimal constants are included, without moment,
density, positive-dimension, finite-constant or attainment assumptions. Binary reverse bounds
explicitly assume probability of each factor separately.

The accepted modules are `Poincare/Transport`, `Poincare/Product/Reverse`,
`Poincare/FiniteProduct/Geometry`, and `Poincare/FiniteProduct/Tensorization`.
Their 45 retained public declarations have library implementations, recorded in
`research/explorations/2026-09-03-finite-tensorization-proofs.md`.
`solutions/LemPoincareFiniteTensorization.lean` contains the sole node certificate in the existing
`Issue2Solutions` default target. It also prints the 45 reusable public signatures and checks
eight Euclidean statement families and six concrete boundary applications through typed uses of
the general API. The eight former specialization wrappers and their duplicate obligations remain
removed. No proof placeholders remain in the current default build.

The `Project/` layer has been removed. Each proved node has one certificate directly combining
library results; Euclidean specializations are checked without another named forwarding theorem.
The reusable mathematics, frozen binary signatures, both retained certificate signatures, and
ledger statements remain unchanged. See `formalization/README.md` for the current source map.

The accepted signatures are preserved in
`research/decisions/2026-09-03-finite-tensorization-freeze.md`; final semantic and structural
acceptance is recorded in
`research/explorations/2026-09-03-finite-tensorization-acceptance.md`. The earlier review package is
`research/explorations/2026-09-03-certificate-deduplication.md`, including all 45 public
signatures and the full Euclidean check source. The original 53-name candidate remains in
`research/decisions/2026-09-03-finite-tensorization-candidate.md` as history. The source/API audit
and proof route remain in `research/explorations/2026-09-03-finite-tensorization-design.md`.
BGL supplies the upper-bound source correspondence and its finite iteration; coordinate lifting
independently supplies the reverse direction. No Dirichlet or Sobolev domain equivalence is
claimed. The publication commit and matching CI result are tracked in Issue #7 rather than
inferred from earlier local or remote runs.

The root `FunctionalInequalities.lean` aggregate imports the accepted
`Poincare/Product/Reverse` and `Poincare/FiniteProduct/Tensorization` modules. This finite-product
certificate is one component of the product-case KLS path; a one-dimensional log-concave bound
and Cheeger--Poincaré comparison remain separate obligations.

## Proposed next independent node

The next suggested task is the sharp one-dimensional Gaussian statement
`Poincare.constant (gaussianReal m v) = (v : ENNReal)`. Before opening or proving that node,
review the exact `Admissible` test class, Mathlib's `gaussianReal` variance parameter convention,
available Gaussian integration APIs, and a proof route for the upper bound, then obtain a human
freeze. This document does not claim that such an issue or proof already exists.
