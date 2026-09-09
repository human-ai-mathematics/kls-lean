# Lean design: Poincaré certificates

命名空间已表达的内容不再重复进声明短名；见[短名补充记录](research/decisions/2026-09-08-namespace-short-names.md)。
比较名称也只写一次共有操作，见[比较短名记录](research/decisions/2026-09-08-comparison-short-names.md)。

This document records the implemented Lean architecture and semantic contracts for the Issue #2
linear-test lower bound, Issue #6 two-factor Poincaré tensorization, Issue #7 finite-product
tensorization with optimal-constant equality, and the sharp one-dimensional Gaussian Poincaré
constant. Multivariate Gaussian and log-Sobolev inequalities, Bakry--Émery, Otto--Villani,
mode-indicator tests, and the KLS conjecture itself remain outside the certified scope.

The interfaces described here may evolve as proofs and downstream uses clarify the design.
There is no mandatory freeze before proof work or default promise of backward compatibility.
Proof certification refers to the current statement. Record mathematical scope changes and
migrate affected consumers; the [current lifecycle](research/ledger-schema.md#lifecycle) gives
the validation rules. Historical freeze records below preserve their reviewed snapshots.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](research/naming.md) and [the migration record](research/decisions/2026-09-08-mathematical-api-organization.md).

## Layered `L²` and energy foundation (2026-09-04)

Downstream applications and smoke tests may import `FunctionalInequalities.Poincare.Foundation`;
reusable library modules import only their exact direct dependencies. The accepted smooth-test API
below remains available for its existing certificates, but it is no longer the architectural base
for future KLS layers. The finite-dimensional comparison now proves equality of the two optimal constants.

The 12 comparison declarations in `Poincare.Relaxation`, `Energy.SmoothGradient.Intrinsic.Comparison`,
`Poincare.SmoothGradient.Comparison` and `Poincare.SmoothTest.Comparison` now have complete
proofs with unchanged signatures. Both ledger nodes are proved and exported by the foundation;
see the [comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md)
and [proof acceptance](research/decisions/2026-09-06-poincare-comparison-proofs.md).

The new dependency direction is:

```text
ProbabilityMeasure + intrinsic real L² variance + affine support coordinates
  → extended energy and its finite domain
  → concrete pre-energy + quadratic law + dense realization
  → sequential relaxation + l.s.c. + recovery + closed-quadratic structure
  → optional core-agreement / contraction / Dirichlet properties
  → finite-valued TestFamily on that domain
  → ENNReal Rayleigh supremum and Poincaré constant.
```

`Poincare.TestFamily.constant` is the supremum of extended Rayleigh quotients. Its checked boundary
semantics are `0 / 0 = 0`, positive variance divided by zero energy equals `⊤`, and a single such
test forces the optimal constant to be `⊤`. `Poincare.L2Energy.constant` applies this optimizer to
the finite domain of `Q : Lp ℝ 2 μ → ENNReal`; `finiteValue` requires a proof that `Q f ≠ ⊤`, so
infinite energy is never silently converted to zero.

`Energy.SmoothGradient.relaxation` realizes globally `C∞`, square-integrable,
finite-gradient tests in `L²` and sequentially relaxes their `NNReal` gradient integral on a
finite-dimensional real Hilbert space with Borel, second-countable measurable topology. In
Mathlib v4.33, ordinary infinite differentiability is `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` means the
strictly stronger analytic regularity and is not used by either live smooth-test frontend.

The following statements are now proved rather than assumed:

- compactly supported `C∞` tests give a dense realization;
- the concrete gradient pre-energy is quadratic;
- sequential relaxation is lower semicontinuous in every pseudometric ambient space and has
  recovery sequences at finite points, or at all points under dense realization;
- relaxation preserves the full extended parallelogram identity and nonzero quadratic
  homogeneity, hence the smooth-gradient relaxation is a densely defined `ClosedQuadratic`;
- continuous transformations satisfying the explicit test-level relaxed contraction bound
  contract the relaxation;
- the affine span of the support is the smallest closed affine subspace of full measure, and the
  original and intrinsic-coordinate real `L²` spaces are linearly isometrically equivalent;
  the intrinsic-affine smooth relaxation is therefore also `ClosedQuadratic`.

These theorems do not identify either relaxation with Cheeger energy `2 Ch`, prove the concrete
normal-contraction estimate required for `Dirichlet`, or show `AgreesOnTests`. For singular
measures, raw ambient gradients need not be constant on an `L²` fiber (`0` and `x ↦ x` already
differ under `δ₀`). This obstructs a raw-test core theorem, but it does not obstruct the closed
quadratic relaxation itself. The intrinsic affine reduction removes normal directions and gives
a canonical coordinate presentation; it does not by itself prove raw-test agreement for atomic
or other singular laws. Anisotropic energies will carry their metric/operator parameter
explicitly and will not reuse the unqualified canonical-energy name.

The complete current tree, quantified interface, nonclaims, build command, and migration order are
in [`formalization/FunctionalInequalities/Poincare/README.md`](formalization/FunctionalInequalities/Poincare/README.md).

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

Define `Poincare.SmoothTest.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)`. This is the same product
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
    (hμ : Poincare.SmoothTest.Holds μ C) (hν : Poincare.SmoothTest.Holds ν C') :
    Poincare.SmoothTest.Holds (Poincare.SmoothTest.prodMeasure μ ν) (max C C') :=
  Poincare.SmoothTest.Holds.prod hμ hν

example
    {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Poincare.SmoothTest.constant (Poincare.SmoothTest.prodMeasure μ ν) ≤
      max (Poincare.SmoothTest.constant μ) (Poincare.SmoothTest.constant ν) :=
  Poincare.SmoothTest.constant_prod_le
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

The default targets compile the reusable `FunctionalInequalities` library and all certificates
listed in [`solutions/README.md`](solutions/README.md). The six original entry points are
`solutions/LemLinearTestLower.lean`,
`solutions/LemPoincareTensorization.lean`,
`solutions/LemPoincareFiniteTensorization.lean`,
`solutions/LemPoincareGaussianOneDimensional.lean`,
`solutions/LemAmbientIntrinsicPoincareComparison.lean`, and
`solutions/LemLegacyRelaxedPoincareComparison.lean`. The certificate entry points belong to the
`Solutions` default target, together with `solutions/GaussianAxiomAudit.lean` and
`solutions/FoundationAxiomAudit.lean`. The `Examples` default target compiles the usage and boundary
examples in `examples/PoincareFoundation.lean`; the foundation guide explains their reading order.

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

`FunctionalInequalities.Poincare.SmoothTest.Basic` implements the manuscript normalization

$$
\operatorname{Var}_\mu(f)\le C\int \lVert\nabla f\rVert^2\,d\mu.
$$

The exact choices are:

- `Poincare.SmoothTest.Admissible μ f` means that `f` is globally smooth, belongs to $L^2(\mu)$, and has
  integrable squared gradient. The finite-energy field prevents Lean's totalized real integral
  from silently assigning an unintended value to a nonintegrable energy. This is the smooth
  finite-energy core; no equivalence with a closed Sobolev or spectral-gap domain is claimed.
- `Poincare.SmoothTest.energy μ f` is the real integral of the squared norm of Mathlib's canonical gradient.
  A bridge theorem identifies it with the squared operator norm of the Fréchet derivative.
- `Poincare.SmoothTest.Holds μ C` is a `Prop`-valued structure containing probability normalization,
  nonnegativity of `C`, and the fixed-constant inequality for every admissible test.
- `Poincare.SmoothTest.constant μ : ℝ≥0∞` is the infimum of all finite nonnegative constants satisfying
  `Poincare.SmoothTest.Holds μ C`. It is `⊤` exactly when no finite valid constant exists.
- `Poincare.SmoothTest.rayleigh μ f : ℝ≥0∞` divides only after mapping variance and energy into extended
  nonnegative reals. Thus positive variance over zero energy is `⊤`, while `0 / 0 = 0`. At
  positive energy it equals the ordinary real quotient from the manuscript.

The theorem quantifies over every `Poincare.SmoothTest.Admissible` test, including constant functions. The
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

- `formalization/FunctionalInequalities/Poincare/SmoothTest/Basic.lean`: admissibility, energy, fixed constants, and
  the optimal extended Poincaré constant.
- `formalization/FunctionalInequalities/Poincare/SmoothTest/Linear.lean`: linear tests, extended Rayleigh quotients,
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
- `formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean`: measure-preserving coordinate
  lifts and exact transport under real linear isometry equivalences.
- `formalization/FunctionalInequalities/Poincare/Product/Reverse.lean`: binary coordinate reverse
  bounds and optimal-constant equality.
- `formalization/FunctionalInequalities/Poincare/FiniteProduct/Geometry.lean`: the dependent
  `PiLp 2` product law, coordinate projections, reindexing, and Option splitting.
- `formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean`: finite
  fixed-constant tensorization, reverse bounds, optimal equality, and boundary consequences.
- `solutions/LemPoincareFiniteTensorization.lean`: the sole Issue #7 certificate, retaining the
  45 public interface checks plus eight Euclidean families and six boundary applications.
- `formalization/FunctionalInequalities/Poincare/Gaussian/Density.lean`: real Gaussian density
  differentiation, tail identities, and the density/integrability bridge.
- `formalization/FunctionalInequalities/Poincare/Gaussian/Hardy.lean`: finite-interval
  FTC--Cauchy, Tonelli rearrangements, and the left/right Gaussian energy estimates.
- `formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean`: the valid Gaussian
  Poincaré constant, the identity-test lower bound, and sharp optimal equality.
- `solutions/LemPoincareGaussianOneDimensional.lean`: the sole Gaussian node certificate,
  retaining all 20 public interface checks and seven typed boundary/normalization applications.
- `solutions/GaussianAxiomAudit.lean`: a default-build `#guard_msgs` check fixing the Gaussian
  certificate's transitive axiom set to `propext`, `Classical.choice`, and `Quot.sound`.

Compilation is enforced by `lake build`, whose default targets include all current root-level
certificates. Among the original certificates, the linear-test certificate covers the two lower-bound conclusions above; the
two tensorization certificates cover the binary and finite product results; the Gaussian
certificate covers its fixed and optimal real-line constants. None proves the nonlinear parts of
Remark 3.8 or a multivariate Gaussian theorem.

## Repository certification

`research/a-series/ledger.yaml` connects `lem:linear-test-lower`,
`lem:poincare-tensorization`, `lem:poincare-finite-tensorization`, and
`lem:poincare-gaussian-one-dimensional` to their respective files under `solutions/`, all with
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

The lifecycle and checker rules are specified in `research/ledger-schema.md`. New nodes may move
directly from `drafted` to `proved`; draft declarations may contain placeholders and must still
compile in the default build. The checker also accepts historical `frozen` snapshots as unproved
nodes. Only proved nodes may claim `checked_by: lean`; their entry points and local imports
undergo the static escape-token check. Semantic review and axiom inspection concern the current
statement and proof, without a separate mandatory freeze checkpoint. The metadata checker
validates the current state rather than approval history or signature stability.

`.github/workflows/lean.yml` runs these two Python commands and the default Lean build on every
push and pull request. It uses Python 3.12 without third-party packages and the official
`leanprover/lean-action@v1` to set up Lean in `formalization`. CI then enumerates the local
library and solution files' direct Mathlib imports, downloads those modules and their upstream
dependencies with `lake exe cache get`, and runs the complete default `lake build`. The action's
whole-`.lake` GitHub cache and unrestricted Mathlib fetch are disabled to avoid exhausting runner
disk space. `MATHLIB_NO_CACHE_ON_UPDATE=1` also prevents the dependency-update hook from fetching
all of Mathlib. This changes cache scope, not the compiled targets or proof checks.

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
`solutions/LemPoincareFiniteTensorization.lean` contains the sole node certificate in the
`Solutions` default target. It also prints the 45 reusable public signatures and checks
eight Euclidean statement families and six concrete boundary applications through typed uses of
the general API. The eight former specialization wrappers and their duplicate obligations remain
removed. No proof placeholders remain in the accepted finite-product modules or certificate.

The `Project/` layer has been removed. Each proved node has one certificate directly combining
library results; Euclidean specializations are checked without another named forwarding theorem.
The reusable mathematics, binary signatures reviewed at the time, both retained certificate
signatures, and ledger statements were unchanged by that migration. See `formalization/README.md`
for the current source map.

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
`Poincare/Product/Reverse`, `Poincare/FiniteProduct/Tensorization`, and
`Poincare/Gaussian/Real` modules. This finite-product
certificate is one component of the product-case KLS path; a one-dimensional log-concave bound
and Cheeger--Poincaré comparison remain separate obligations.

## Gaussian proof and acceptance (2026-09-04)

The node `lem:poincare-gaussian-one-dimensional` is **proved** with `checked_by: lean` after
human semantic and mathematical review. The two main interfaces assert, for every `m : ℝ` and
`v : NNReal`,
`Poincare.SmoothTest.Holds (gaussianReal m v) (v : ℝ)` and
`Poincare.SmoothTest.constant (gaussianReal m v) = (v : ENNReal)`. The test-domain definitions above are
used unchanged. The variance parameter v is the constant; v = 0 is the Dirac law at m.

The 20 declarations are all proved and split by responsibility. `Poincare/Gaussian/Density.lean`
contains 7 Mathlib-based density/calculus and integrability interfaces;
`Poincare/Gaussian/Hardy.lean` contains 9 interval, Tonelli and half-line energy interfaces; and
`Poincare/Gaussian/Real.lean` contains 4 fixed-upper-bound, identity-test-lower-bound and
sharp-constant interfaces. The right and left tail weights are v times the density, and the
half-line energy bounds add without an extra factor. Explicit density-weighted integrability
prevents real-integral totalization from replacing a necessary hypothesis. No global Lebesgue L²
condition on f′, test-function decay, or infimum-attainment assumption is added.
The two first-moment tail identities now quantify over every endpoint `t`; their former
endpoint-order premises were unused. Downstream half-line arguments obtain the required order
facts from their integration regions, so this is a strict API generalization rather than a
change of claim.

The manuscript's Gaussian covariance family supplies the positive centered one-dimensional
Poincaré claim. Arbitrary means, zero variance, the exact smooth finite-energy domain, and
the direct density route are local specifications; the source itself proves its upper bound
through Bakry–Émery and LSI. See the [source/API audit](research/explorations/2026-09-04-gaussian-poincare-design.md).

The proof first minimizes variance against the fixed center `f m`, applies FTC and
Cauchy--Schwarz on each finite interval, and uses nonnegative Tonelli plus the Gaussian
first-moment tails on the two half-lines. This yields the upper bound for positive variance;
the zero-variance case is proved separately from the Dirac-law identity. The identity test has
variance v and energy one and supplies the matching lower bound. Thus the result has neither a
missing factor nor an unstated positivity or boundary assumption.

The [reading guide](formalization/FunctionalInequalities/Poincare/Gaussian/README.md) gives the
mathematical meaning, proof flow, examples and file map. The earlier
[candidate package](research/decisions/2026-09-04-gaussian-poincare-candidate.md) and
[signature snapshot](research/explorations/2026-09-04-gaussian-poincare-signatures.txt) remain
append-only records of human statement review and do not override the current proved status.
`solutions/LemPoincareGaussianOneDimensional.lean` contains the single certificate
`Solutions.LemPoincareGaussianOneDimensional.certificate`, prints all 20 interfaces and checks
seven typed applications. It is compiled by the `Solutions` default target, and the root proved
aggregate exports `Poincare/Gaussian/Real`. The same default target compiles
`solutions/GaussianAxiomAudit.lean`, whose guarded output fixes the certificate's transitive
axiom set to `propext`, `Classical.choice`, and `Quot.sound`.

The review confirmed the exact source normalization and scope: arbitrary mean and zero variance
are local extensions, while the theorem concerns the existing globally smooth Gaussian-L²,
finite-gradient-energy domain only. It does not establish a closed Sobolev/spectral-gap domain
equivalence. The [Gaussian freeze](research/decisions/2026-09-04-gaussian-poincare-freeze.md)
records the approved contract; the
[acceptance record](research/explorations/2026-09-04-gaussian-poincare-acceptance.md) records the
proof closeout, final architecture and validation gates. Local certification is complete;
publication and remote CI status must still be reported from the actual final commit rather than
inferred from this review.

## Public naming

Use the mathematical object's namespace for its role: `Poincare.SmoothGradient.Intrinsic.constant`,
`Poincare.SmoothGradient.Ambient.constant`, and `Poincare.L2Energy.constant` distinguish the selected frontend,
ambient relaxation, and an optimizer parameterized by an energy. `Energy.SmoothGradient.Intrinsic.energy`
retains the intrinsic-affine construction in its definition. These names do not assert Cheeger
or Dirichlet identifications. Theorems on `KLS.LogConcave` support proof-receiver calls such as
`hμ.canonical_eq_literature`. Keep domain, integrability and boundary distinctions in theorem
names when they matter; see [the naming guide](research/naming.md).
