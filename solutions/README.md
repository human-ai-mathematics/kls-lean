# Lean statement entry points and certificates

This directory contains thin, node-specific Lean entry points. Reusable definitions and proofs
belong under `formalization/FunctionalInequalities/`; a file here only packages the exact theorem
surface associated with a repository ledger node.

For the selected KLS chain, start with [BKL Theorem 1.1 and KLS](#bkl-theorem-11-certificate-and-the-kls-target),
then its [Theorem 4.1](#bkl-theorem-41-certificate) and [compact Letwin](#letwin-compact-quadratic-form-certificate)
inputs. Exact paper coverage belongs to the [literature register](../research/progress/LITERATURE.md).

## Lean certification convention

A proved ledger node certified by Lean records:

```yaml
"lean_solution": "solutions/LemLinearTestLower.lean",
"status": "proved",
"checked_by": "lean"
```

The certificate must:

1. stay below `solutions/` and use the `.lean` suffix;
2. name the ledger node in its header;
3. contain no `sorry`, `admit`, `native_decide`, `axiom`, or `unsafe` escape, including its local imports;
4. be included in a default Lake target; and
5. compile through `cd formalization && lake build`.

`python3 research/check_ledger.py` enforces the structural and provenance requirements. The Lake
build performs the machine check. A green structural check alone does not establish semantic
agreement with the reference statement.

Certification applies to the current statement and proof, without freezing their public
interfaces. When interfaces change, migrate consumers and revalidate the affected certificates.
Changes to mathematical scope must be recorded and reflected in the ledger and Blueprint;
an unproved revision cannot retain Lean-certification claims.

Each proved node has exactly one named `certificate`, directly importing the reusable library.
The former `Project/` forwarding layer has been removed. Concrete specializations are checked
with typed `#check` applications rather than duplicate public theorems.

- `LemLinearTestLower.lean` directly combines `Poincare.SmoothTest.rayleigh_le_constant` and
  `Covariance.lambdaMax_le_constant` into the Issue #2 Euclidean statement, retaining the finite
  second-moment assumption and the zero-dimensional case.
- `LemPoincareTensorization.lean` directly combines `Poincare.SmoothTest.Holds.prod` and
  `Poincare.SmoothTest.constant_prod_le` into the Issue #6 Hilbert statement. A typed application checks
  Euclidean factors of arbitrary dimensions, including zero.
- `LemPoincareFiniteTensorization.lean` contains
  `Solutions.LemPoincareFiniteTensorization.certificate`, directly packaging the Issue #7
  binary reverse/equality, finite tensorization/equality, and boundary conclusions. Its API
  checks also retain the supporting transport interfaces.
- `LemPoincareGaussianOneDimensional.lean` contains
  `Solutions.LemPoincareGaussianOneDimensional.certificate`, directly packaging the valid
  fixed constant and sharp optimal-constant equality for every real mean and nonnegative
  variance. Its typed checks cover the standard, translated, and zero-variance laws.

These four nodes are recorded as `proved` with `checked_by: lean`.

The two comparison certificates, `LemAmbientIntrinsicPoincareComparison.lean` and
`LemLegacyRelaxedPoincareComparison.lean`, package five and seven proved comparisons respectively.
Their types preserve the reviewed generality, including empty test classes, zero-dimensional
support, zero finite constants and infinite optima. Gaussian transport through these bridges is
now proved. See the [comparison guide](../formalization/FunctionalInequalities/Poincare/Euclidean/README.md).

The `Solutions` default target builds all registered certificates plus `GaussianAxiomAudit.lean` and
`FoundationAxiomAudit.lean`. The latter guards 27 foundation and comparison declarations together
with the Dirac and normal-direction raw-energy obstructions; each new
certificate also has its own axiom guard. These checks require exactly `propext`, `Classical.choice`
and `Quot.sound`. Compiled user examples remain in
[`examples/PoincareFoundation.lean`](../examples/PoincareFoundation.lean) and
[`examples/ApiOrganization.lean`](../examples/ApiOrganization.lean).

## Analytic comparison certificates and definition checks

[`LemLogConcaveIntrinsicAbsoluteContinuity.lean`](LemLogConcaveIntrinsicAbsoluteContinuity.lean)
certifies intrinsic absolute continuity from the compact-set definition.
[`ThmSelectedLiteratureConstantEquivalence.lean`](ThmSelectedLiteratureConstantEquivalence.lean)
then certifies the general log-concave constant equality, including singular ambient laws and
zero-dimensional support. Both certificates and all new reusable declarations have default-build
axiom guards. Density and moment conclusions have their own certificate below.

[`ThmSmoothLipschitzConstantEquivalence.lean`](ThmSmoothLipschitzConstantEquivalence.lean)
packages eight proved interfaces from `Energy/LocalSlope/Gradient.lean` and
`Poincare/LocalSlope/SmoothTestComparison.lean`. The pointwise and almost-everywhere slope identities
feed energy/domain identification and the finite-constant and extended-optimum comparisons.
The final comparison assumes intrinsic absolute continuity. The node is
`proved / checked_by: lean`; all eight components and the certificate have default-build
transitive axiom guards.

[`LemCovarianceTestCoreDensity.lean`](LemCovarianceTestCoreDensity.lean) contains the certificate
for four proved approximation contracts: weighted compact-support cutoff, full-gradient
mollification, weighted L2 approximation, and interval-preserving bounded L1 smoothing. Its
certificate and four reusable declarations have default-build transitive axiom guards. The
node is `proved / checked_by: lean`.

`StatementChecks.lean` is a default-build target for the literal KLS proposition and its domain
and boundary encodings. It is not a ledger proof certificate. All registered mathematical certificates,
the twenty-five named definition sanity checks, the six conditional-fiber contracts and the five
affine covariance contracts have default-build transitive axiom guards. Existing
Dirac representative examples and Gaussian comparisons are reused. A concrete Gaussian literature
bound can now use a proof of the Gaussian law satisfying compact-set `KLS.LogConcave`
to apply the general comparison; that specialization is not added here. The [verification runner](../research/verify.py)
also audits the statement's local definition closure against its explicit golden,
checks complete axiom coverage and stores source-bound evidence. See the
[workflow guide](../research/verification.md).

New nodes may move directly from `drafted` to `proved`; no prior freeze is required. Drafts use
`checked_by: null` and meet the same path, header, and default Lake target requirements, while
placeholders remain permitted. Historical `frozen` snapshots are still accepted as unproved
nodes. Only proved nodes receive the escape-token check. See the
[lifecycle guide](../research/ledger-schema.md#lifecycle) for current certification and interface
change rules.

## Gaussian certificate

[`LemPoincareGaussianOneDimensional.lean`](LemPoincareGaussianOneDimensional.lean) certifies
`lem:poincare-gaussian-one-dimensional`: for every real mean `m` and variance `v : NNReal`,
`v` is a valid smooth-test Poincaré constant for `gaussianReal m v`, and its optimal
`ENNReal` constant equals `v`. This includes zero variance and the Dirac case.
Typed clients cover concrete and boundary cases without duplicate specialization theorems.

The [Gaussian guide](../formalization/FunctionalInequalities/Poincare/Gaussian/README.md)
explains the `Density` → `Hardy` → `Real` proof and its smooth L² finite-energy scope.

## Finite tensorization certificate

[`LemPoincareFiniteTensorization.lean`](LemPoincareFiniteTensorization.lean) certifies
`lem:poincare-finite-tensorization`: binary reverse bounds and equality, finite fixed-constant
tensorization and optimal equality, with the supporting coordinate/isometry transports.
Typed applications check Euclidean families and boundary cases; the certificate combines the
accepted conclusions without duplicate specialization declarations.

## Borell equivalence certificate and implemented definition checks

[`ThmCompactBorellLogconcavityEquivalence.lean`](ThmCompactBorellLogconcavityEquivalence.lean)
certifies `thm:compact-borell-logconcavity-equivalence`: compact-set log-concavity of a Borel
probability law on a finite-dimensional real normed space is equivalent to Bobkov's Borel/inner-measure
formulation, including singular laws, null sets, proper affine supports and dimension zero. Its
`certificate` wraps `KLS.LogConcave.borel_iff`; the certificate, the library theorem and the two
compactness/inner-regularity lemmas have default-build axiom guards. The node is
`proved / checked_by: lean`.

`StatementChecks.lean` contains twenty-five named, proved checks with standard-only axiom guards, plus
axiom guards for the six proved conditional-fiber contracts in `KLS/ConditionalFiber/Basic.lean`
(iterated base integral, a.e. finite conditional second moment, joint measurability, version
independence, representative independence and the L² identification). The definition node
`def:conditional-fiber-form` therefore carries `\leanok`; it is not a ledger theorem. The structural
lemma `lem:conditional-fiber-form` built on it is a separate proved ledger node (see below). The raw
Dirac obstruction has named library proofs and FoundationAxiomAudit guards, without a ledger entry.

The five affine covariance checks (`affine_constant_unfold`, `affine_test_fields`,
`affine_energy_integral`, `zero_dimension_affine_constant`, `ambient_dirac_affine_constant`) cover
`def:affine-poincare-constant`: the constant unfolds to the generic `L²` optimizer of the intrinsic
law at the sequential relaxation of the covariance pre-energy, the test class is exactly globally
Lipschitz, `L²` and integrable `⟪Σ ∇g, ∇g⟫`, the energy is that real integral without a factor
one half, and dimension zero (including a Dirac law in `ℝ`) gives constant zero. Axiom guards also
cover the four log-concave contracts in `KLS/LogConcave/Covariance.lean` and the
zero-dimensional theorem. The definition node carries `\leanok`; it is not a ledger theorem.

## Borell density representation certificate

[`ThmBorellLogconcaveDensity.lean`](ThmBorellLogconcaveDensity.lean) certifies
`thm:borell-logconcave-density`. Its sole `certificate` packages, for every log-concave law and
every Haar measure on the direction of its affine support: existence of an upper semicontinuous
log-concave density representative `KLS.IsBorellDensity` of the intrinsic law, positivity of every
such representative on the interior of the support, two-sided positive bounds on compact subsets of
that interior, the closed-convex-hull identity of the support, the null complement of the support
interior, an exponential moment and all-order moments. Typed applications cover the Euclidean
family including dimension zero. The certificate and nine reusable declarations have default-build
axiom guards. The node is `proved / checked_by: lean`.

## Covariance-core closure certificate

[`LemCovarianceCoreClosure.lean`](LemCovarianceCoreClosure.lean) certifies
`lem:covariance-core-closure`. For a full-dimensional log-concave law `ν` on a finite-dimensional
Euclidean space, any Haar measure and any continuous linear `B`, its sole `certificate` packages:
the weighted gradient operator `g ↦ B ∘ ∇g` on globally Lipschitz `L²(ν)` tests is densely defined
and closable; every core between the smooth compactly supported classes and the full domain (in
particular `ℝ + C_c^∞`) has the same closure; and the sequential relaxation of `‖B ∇g‖²` equals
`‖T̄ f‖²` on the domain of the closure and `⊤` outside it. Typed applications cover the intrinsic
law of every log-concave law on `EuclideanSpace ℝ (Fin n)`, dimension zero (zero operator, full
domain) and the identity with `Energy.CovarianceGradient.Intrinsic.energy` for every square root `B` of the intrinsic
covariance. The certificate and eleven reusable declarations carry default-build axiom guards.

## Affine covariance closed-form certificate

[`ThmAffineCovarianceRelaxationClosed.lean`](ThmAffineCovarianceRelaxationClosed.lean) certifies
`thm:affine-covariance-relaxation-closed`. For every log-concave law its sole `certificate`
packages: dense realization of the affine covariance pre-energy; `Energy.CovarianceGradient.Intrinsic.energy μ` is a
closed quadratic form; the globally Lipschitz tests are a sequential core (raw energy preserved);
translating the intrinsic law by any vector preserves the covariance operator and gives an `L²`
isometry preserving variance, relaxation and optimal constant; and for a square root `B` of the
intrinsic covariance the affine relaxation is the squared-norm energy of the closure of `B ∇` on the
core `ℝ + C_c^∞`, with `Poincare.CovarianceGradient.Intrinsic.constant μ` its optimal constant. Typed applications cover
every `EuclideanSpace ℝ (Fin n)` and dimension zero. The certificate and ten reusable declarations
carry default-build axiom guards.

## Affine constant translation-invariance certificate

[`LemAffinePoincareTranslationInvariance.lean`](LemAffinePoincareTranslationInvariance.lean)
certifies `lem:affine-poincare-translation-invariance`. For every log-concave law `μ` and every
ambient vector `b` its sole `certificate` packages: the translate `Probability.translateLaw μ b`
is log-concave; its ambient covariance operator and the direction of its affine support are those of
`μ`; a linear isometric equivalence of the two intrinsic `L²` spaces preserves variance and
intertwines the affine covariance relaxations; `Poincare.CovarianceGradient.Intrinsic.constant` is unchanged; `μ` has a
finite ambient second moment; and translating by the negative barycenter gives zero mean. Typed
applications cover centering on every `EuclideanSpace ℝ (Fin n)` and dimension zero. The certificate
and twelve reusable declarations carry default-build axiom guards.

## Affine and isotropic reduction certificate

[`ThmAffineIsotropicReduction.lean`](ThmAffineIsotropicReduction.lean) certifies
`thm:affine-isotropic-reduction`. For every finite `K` its sole `certificate` packages the pairwise
equivalences of `KLS.IsotropicBound K` (isotropic log-concave laws have literature constant at most
`K`), `KLS.CovarianceBound K` (log-concave laws have literature constant at most `K ‖Cov‖`) and
`KLS.AffineBound K` (log-concave laws have affine covariance constant at most `K`), each quantified
over every finite-dimensional Euclidean space of a fixed universe, and the implication from the affine
bound in universe zero to `KLS.Conjecture`. Typed applications cover the covariance-normalized bound
on every `EuclideanSpace ℝ (Fin n)` and dimension zero. The certificate and fifteen reusable
declarations carry default-build axiom guards.

## Smooth-gradient Dirichlet certificate

[`ThmSmoothGradientRelaxationDirichlet.lean`](ThmSmoothGradientRelaxationDirichlet.lean) certifies
`thm:smooth-gradient-relaxation-dirichlet`. For every Borel probability law on a finite-dimensional
Euclidean space its sole `certificate` packages: the smooth-gradient relaxation is Markovian (every
normal contraction of an `L²` class does not increase the relaxed energy), it is a Dirichlet energy,
and the intrinsic-affine relaxation on the ambient `L²` is a Dirichlet energy. Typed applications
cover the contraction inequality on every `EuclideanSpace ℝ (Fin n)`, dimension zero and the Dirac
law on `ℝ`. The certificate and eleven reusable declarations carry default-build axiom guards.

## One-dimensional log-concave Poincaré certificate

[`ThmOneDimensionalLogConcavePoincare.lean`](ThmOneDimensionalLogConcavePoincare.lean) certifies
`thm:one-dimensional-logconcave-poincare`. For every compact-set log-concave law `ν` on `ℝ` its sole
`certificate` packages `Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (4 * variance id ν)`
and the extended-variance form `≤ 4 * evariance id ν`; the zero-variance case is the one-point
affine support, where the constant is `0`. Typed applications cover finiteness of the literature
constant, Bobkov's constant `12` as a corollary, the Dirac law at the origin (log-concave by
`KLS.logConcave_dirac`, constant `≤ 0`), and the smooth-test inequality with constant `4 · Var` for
laws with interior support. The certificate and twenty-two reusable declarations carry
default-build axiom guards.

## Raw/sequential-core agreement certificate

[`ThmSmoothGradientRawCoreAgreementDensity.lean`](ThmSmoothGradientRawCoreAgreementDensity.lean)
certifies `thm:smooth-gradient-raw-core-agreement-density`. For every probability law on a
finite-dimensional inner-product space with a local density (`Energy.SmoothGradient.LocalDensity`:
open carrier, density positive almost everywhere with locally essentially bounded reciprocal) its
sole `certificate` packages agreement of the smooth-gradient pre-energy with its relaxation on every
smooth test and the sequential-core property. Typed applications cover the intrinsic law named by
the Blueprint, the Euclidean family, and the consequence that two smooth tests with the same `L²`
class have the same raw energy. The certificate and eleven reusable declarations carry default-build
axiom guards.

## Closed conditional-fiber form certificate

[`LemConditionalFiberForm.lean`](LemConditionalFiberForm.lean) certifies
`lem:conditional-fiber-form`. For every Borel probability law `μ` on a finite-dimensional
inner-product space and every probability law `ρ` on its unit sphere its sole `certificate`
packages: `Energy.Dirichlet μ (KLS.ConditionalFiber.functional μ ρ)`, the conditional-fiber form
as a densely defined closed quadratic Markovian energy on `L²(μ)`; the jump representation of the
fiber energy on nondegenerate fibers (squared two-point differences against `μ_{θ,z} ⊗ μ_{θ,z}`
over `2 Var(T)`); the swap invariance of every two-point measure (reversibility); and the bound
`d L²` for globally `L`-Lipschitz tests. Typed applications cover the Blueprint scope (log-concave
law, finite second moment, admissible frame, none of which the theorem uses), dense domain and lower
semicontinuity on `EuclideanSpace ℝ (Fin (n + 1))`, the Markov inequality, the smooth compactly
supported core inside the finite domain, and the empty sphere of dimension zero. The certificate and
eleven reusable declarations carry default-build axiom guards.

## Conditional-fiber energy comparison certificate

[`LemConditionalFiberEnergyComparison.lean`](LemConditionalFiberEnergyComparison.lean) certifies
`lem:conditional-fiber-energy-comparison`. For a law `μ ≪ m` (any additive Haar measure), an
admissible frame `ρ` and a finite `κ` with `KLS.ConditionalFiber.FiberBound μ ρ κ` (the literature
Poincaré constant of almost every nondegenerate conditional fiber is at most `κ · eVar[T]`), its
sole `certificate` packages: every literature test (`Energy.LocalSlope.Admissible μ f`) has
conditional-fiber energy at most `κ` times its finite local-slope energy, and every form-gap bound
`Var_μ ≤ C · D_{μ,ρ}` on the maximal finite domain `domain μ ρ` gives
`Poincare.LocalSlope.Intrinsic.constant μ ≤ κ C`. Typed applications display the Blueprint scope
(log-concave law, finite second moment, neither used), the gradient form `κ ∫‖∇f‖² dμ` of the
bound, membership of every finite-energy test in `domain μ ρ`, the Euclidean family with Lebesgue
measure as the Haar reference, and the empty sphere of dimension zero. The certificate and the two
library theorems carry default-build axiom guards. No value of `κ`, no fiber log-concavity and no
Poincaré inequality for `μ` is claimed; `cor:conditional-fiber-twelve-bound` is a separate node.

## Log-concave conditional fibers certificate

[`CorConditionalFiberTwelveBound.lean`](CorConditionalFiberTwelveBound.lean) certifies
`cor:conditional-fiber-twelve-bound`. For a compact-set log-concave law `μ ≪ m` (any additive Haar
measure) and an admissible frame `ρ`, its sole `certificate` packages the four steps of the
Blueprint proof: base-law almost every conditional kernel `kernel μ ρ b` is a compact-set
log-concave law on `ℝ`; `KLS.ConditionalFiber.FiberBound μ ρ 4`; every literature test
(`Energy.LocalSlope.Admissible μ f`) has conditional-fiber energy at most `4` times its finite
local-slope energy; and every form-gap bound `Var_μ ≤ C · D_{μ,ρ}` on `domain μ ρ` gives
`Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 C`. Typed applications display the gradient form
`4 ∫‖∇f‖² dμ`, the literature constant `12` as the immediate weakening, membership of every
finite-energy test in `domain μ ρ`, the corollary as an instance of the parameterized comparison,
the Euclidean family with Lebesgue measure as the Haar reference, and the empty sphere of dimension
zero. The certificate and two library theorems carry default-build axiom guards. No frame bound, no
Poincaré inequality for `μ` and no KLS statement is claimed; `q:conditional-fiber-frame` is open.

## Cheeger identification certificate (absolutely continuous scope)

[`CorAbsolutelyContinuousRelaxationTwoCheeger.lean`](CorAbsolutelyContinuousRelaxationTwoCheeger.lean)
certifies `cor:absolutely-continuous-relaxation-two-cheeger`. For a Borel probability law `μ` whose
intrinsic law is absolutely continuous with respect to an additive Haar measure `m` on the
direction space of its affine support, its sole `certificate` packages: the smooth-gradient
relaxation of the intrinsic law equals the relaxed squared local slope, and for every `f ∈ L²(μ)`
the selected canonical energy satisfies `𝓔^can_μ f = 2 · Ch_μ f`. Typed applications display the
log-concave case (hypothesis discharged by `intrinsic_absolutelyContinuous`), the convention
`2 · Ch = LocalSlope.relaxation`, the unconditional inequality
`LocalSlope.relaxation ≤ SmoothGradient.relaxation`, the vanishing of the Cheeger energy on a
one-point space, and the Euclidean family with the canonical Haar measure. The certificate and two
library theorems carry default-build axiom guards. The singular case
`thm:smooth-gradient-relaxation-two-cheeger` is **not** claimed; no Poincaré inequality, constant
finiteness or Cheeger--Buser comparison follows.

## Ambient/intrinsic covariance certificate

[`LemAmbientIntrinsicCovariance.lean`](LemAmbientIntrinsicCovariance.lean) certifies
`lem:ambient-intrinsic-covariance`. Under an explicit finite second moment, its sole `certificate`
packages: the ambient covariance operator annihilates the orthogonal complement of the
affine-support direction, restricts on that direction to the covariance operator of the intrinsic
law, has the same operator norm, the intrinsic covariance is positive definite, and a
zero-dimensional direction gives zero operators. Typed applications cover the Euclidean family
including dimension zero. The certificate and nine reusable declarations in
`Probability/Covariance/Intrinsic.lean` have default-build axiom guards. The node is
`proved / checked_by: lean`.

## Cheeger-infimum equality certificate

[`LemRelativePerimeterCheegerInfimum.lean`](LemRelativePerimeterCheegerInfimum.lean) certifies
`lem:relative-perimeter-cheeger-infimum`. For every probability law with a Borell density relative to
Lebesgue measure on a finite-dimensional real inner-product space, its sole `certificate` states that
the Minkowski Cheeger infimum over Borel sets of intermediate mass equals the relative-perimeter
Cheeger infimum over smooth domains, both `⊤` when no admissible set exists; `intrinsic` gives the
log-concave affine-support form `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν`, the two isoperimetric
clauses of `thm:klartag-density-frontend-identification`. Lean is stronger than the Blueprint's
full-dimensional log-concave hypothesis. The one-sided comparisons, dimension zero and the Euclidean
family are exercised; four axiom guards. The node is `proved / checked_by: lean`.

## Cheeger identification certificate (every Borel law)

[`ThmSmoothGradientRelaxationTwoCheeger.lean`](ThmSmoothGradientRelaxationTwoCheeger.lean) certifies
`thm:smooth-gradient-relaxation-two-cheeger`. For **every** Borel probability law on a
finite-dimensional real inner-product space — no absolute continuity, density, positive dimension or
log-concavity — its sole `certificate` packages the equality of the smooth-gradient and local-slope
relaxations of the intrinsic law and the identity `𝓔^can_μ = 2 Ch_μ` on ambient real `L²(μ)`, with
`⊤` allowed on both sides; `conventions_agree` records that the asymptotic-Lipschitz convention relaxes
to the same functional. The absolutely continuous certificate is recovered without its hypothesis,
the coordinate form, dimension zero and the Euclidean family are exercised; four axiom guards. The node
is `proved / checked_by: lean`.

## Relaxed Minkowski content certificate (paper target)

[`ThmRelaxedMinkowskiContentPerimeter.lean`](ThmRelaxedMinkowskiContentPerimeter.lean) certifies
`thm:relaxed-minkowski-content-perimeter`, Theorem 3.6 of Ambrosio–Di Marino–Gigli
(arXiv:1603.08412v1) against the paper's own Definition 3.3. For a Borel measure on a metric space
that is finite on bounded Borel sets and a measurable set of finite mass, the relaxed lower Minkowski
content equals the infimum of liminf slope integrals over globally Lipschitz approximants converging
in `L¹`; `upper` gives the same for the relaxed upper content. The certificate composes two existing
library identities. Typed applications cover finite measures and Lebesgue measure on Euclidean
spaces; four axiom guards. It is the first paper-target certificate. Its scope review is in the
[target-scope reviews](../research/progress/target-reviews.md).

## Bakry–Émery Poincaré certificate (paper target)

[`ThmBakryEmeryPoincare.lean`](ThmBakryEmeryPoincare.lean) certifies `thm:bakry-emery-poincare`,
Corollary 4.8.2 of Bakry–Gentil–Ledoux (2014), in a reviewed stronger form. For
`ν = volume.tilted (-W)` on any finite-dimensional real inner product space, with `W` of class `C²`
and `∇∇W ≥ ρ Id`, `ρ > 0`, the literature Poincaré constant satisfies `C_P(ν) ≤ 1/ρ`; `smoothTest`
gives `Var_ν(f) ≤ ρ⁻¹ ∫ ‖∇f‖² dν` on smooth tests. The book assumes `ℝⁿ`, smooth `W` and
`∫ e^{-W} = 1`. `gaussian` constructs the scaled Gaussian law as a probability measure and applies
both statements with every hypothesis discharged, so the hypotheses are satisfiable in every
dimension, including zero; three axiom guards. It is the second paper-target certificate. Its scope review is in the
[target-scope reviews](../research/progress/target-reviews.md).

## Bizeul–Klartag–Lehec Theorem 3.1 certificate

[`ThmBklTaylorCriterion.lean`](ThmBklTaylorCriterion.lean) certifies `thm:bkl-taylor-criterion`,
Theorem 3.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), in the source form: there is a universal
`K` with `C_P(μ) ≤ K R²` for every regular potential on `ℝⁿ` (BKL (12)) whose law is centered with
`Cov ≤ Id` and every `R ≥ 1` satisfying the Taylor bound (29) in the Hilbert–Schmidt norm. The proof
goes through the operator domain of the heat-model generator and an approximate first
eigenfunction (the operator route, `research/audits/BKL/IterateRouteStatements.lean`); the library constant is
explicit but not part of the claim. `dimZero` and `gaussian` discharge every hypothesis in dimensions zero and one (the standard
Gaussian on `ℝ¹` satisfies (29) with `R = 8`); four axiom guards. This certificate covers the
supporting theorem. The main Theorem 1.1 has its own certificate below.

## Bizeul–Klartag–Lehec Proposition 7.1 certificate

[`PropBklSuspension.lean`](PropBklSuspension.lean) certifies `prop:bkl-suspension`, Proposition 7.1
of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), in the source form: for `d ≥ 2`, if the `(d+1)`-cumulant
bound `CumulantBound d b` holds for all isotropic log-concave laws, then every centered isotropic
regular log-concave law `μ` on `ℝⁿ` and every `f ∈ L²(μ)` satisfy
`‖T_d f‖²_HS ≤ 2 b (d!)⁻² ‖f‖₂²` (BKL (107)). The proof follows the paper's suspension: the joint
law of `(f(X), X)` with independent Laplace noise, its density (109), log-concavity (110),
isotropy, the mixed-cumulant identities (111)–(112), the Hilbert–Schmidt step, the `β → ∞` limit
and the affine-orthogonal decomposition.
`two` is the leading case `d = 2` with the constant `b/2`. This proposition retains the cumulant
bound as a premise; the separate, now-proved Theorem 4.1 supplies it in the final assembly.
Two axiom guards. Theorem 4.1 and the main Theorem 1.1 have their own certificates below.

## Letwin compact quadratic-form certificate

[`ThmLetwinCompactQuadraticBound.lean`](ThmLetwinCompactQuadraticBound.lean) certifies
`thm:letwin-compact-quadratic-bound`, the compact counterpart of Theorem 1.2 of Letwin
(arXiv:2607.24164v1), in the source form: for every `n > 0`, every compactly supported isotropic
log-concave probability measure `μ` on `EuclideanSpace ℝ (Fin n)` and every self-adjoint continuous
linear `M`, singular and indefinite ones included, `Var_μ ⟨M x, x⟩ ≤ 8 ∑ᵢⱼ ⟨M eᵢ, eⱼ⟩²` in the
standard orthonormal basis. `certificate` states this expanded form and `bound` the named predicate
`LetwinCompactBound`, the input of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 4.2; both are the
library theorem `letwinCompactBound`.
Two axiom guards. The noncompact Theorem 1.2 (every isotropic log-concave law) and the paper are not
covered. The subsequent certified cutoff localization, BKL Theorem 4.1 and KLS stages are described below.

## BKL cutoff energy certificate

[`LemBklCutoffEnergy.lean`](LemBklCutoffEnergy.lean) certifies `lem:bkl-cutoff-energy`, equation (95) of
Bizeul–Klartag–Lehec (arXiv:2610.05474v1, Sections 4–6) in finite-horizon cutoff form. The statement:
- **Quantifiers.** It holds for every d ≥ 1 (order m = d + 1) and every compactly supported isotropic log-concave
  probability measure on `EuclideanSpace ℝ (Fin n)`. It also holds for every unit u, ε > 0 and T ≥ 0, all sufficiently
  large cutoff radii R and every actual cutoff Eldan process.
- **Inequality.** `E_{d+1}(0) + ½ ∫∫₀ᵀ γ_R² E_{d+2} ≤ (d!)² 153^d + ε`.

`bound` is the named predicate `CutoffEnergyClaim 153 d`, given by the closed producer `cutoffEnergyClaim_153` of
[`KLS/BKL/CumulantBound.lean`](../formalization/FunctionalInequalities/KLS/BKL/CumulantBound.lean). It uses the actual compact constant-8 theorem
`letwinCompactBound`, and no inequality, induction step or Lyapunov estimate is assumed. Two axiom guards.

This is a restricted, different-route supporting certificate. The uncut Eldan process, its uniqueness and
non-explosion, and the literal stochastic identities (68)–(73) are not constructed. This certificate covers the
cutoff estimate; the following certificates establish BKL Theorems 4.1 and 1.1 and lead to KLS.

## BKL Theorem 4.1 certificate

[`ThmBklCumulantBound.lean`](ThmBklCumulantBound.lean) certifies `thm:bkl-cumulant-bound`, Theorem 4.1 of
Bizeul–Klartag–Lehec (arXiv:2610.05474v1), (65)–(66), in the source form. There is one universal K ≥ 1 such that,
for every order m = d + 1 ≥ 2 (the base m = 2 included), every dimension, every isotropic log-concave probability
measure on `EuclideanSpace ℝ (Fin n)` and every u, the bound
`Σ_J κ_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ K^d (d!)² ‖u‖²` holds.

There is no compactness, Letwin, moment, energy or induction premise. `bound` is the `CumulantBound` form, with the
witness K = 153, given by the closed producer `cumulantBound_153` of the same module. Two axiom guards.

The proof uses the cutoff energy induction of `lem:bkl-cutoff-energy`, with the actual compact constant-8 theorem,
and the compact-to-general passage `cumulantBound_of_compact`. It does not construct the uncut Eldan process or the
literal (68)–(73). This certificate does not cover BKL Theorem 1.1, KLS or the paper; see the next section.

## BKL Theorem 1.1 certificate and the KLS target

[`ThmBklPoincare.lean`](ThmBklPoincare.lean) certifies `thm:bkl-poincare`, Theorem 1.1 of Bizeul–Klartag–Lehec
(arXiv:2610.05474v1), p. 2, in the source form. There is one C > 0, chosen before every dimension and law, such that
every n ≥ 1 and every isotropic log-concave probability measure μ on `EuclideanSpace ℝ (Fin n)` have
`Poincare.LocalSlope.Intrinsic.constant μ ≤ C`.

There is no compactness, regularity or moment premise. `bound` is `KLS.IsotropicBound C` on every finite-dimensional
real inner product space. Two axiom guards.

The proof is the closed producer `KLS.BKL.Localization.theorem11`. It runs the p. 30 assembly (Theorem 3.1, Proposition
7.1, the regular approximation) on Theorem 4.1 from the cutoff route and the proved compact Letwin bound. The project
target `KLS.kls : KLS.Conjecture` follows through the affine/isotropic reduction with the same constant.

The independent client [`research/audits/BKL/KlsAudit.lean`](../research/audits/BKL/KlsAudit.lean) handwrites both
statements and consumes the actual `KLS.kls`. The paper is covered in the exact sense of its main theorem; the uncut
Eldan process and the literal (68)–(73) are not constructed.
