# Lean statement entry points and certificates

This directory contains thin, node-specific Lean entry points. Reusable definitions and proofs
belong under `formalization/FunctionalInequalities/`; a file here only packages the exact theorem
surface associated with a repository ledger node.

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

These four nodes are recorded as `proved` with `checked_by: lean`. The binary tensorization
freeze and acceptance records are `../research/decisions/2026-09-03-tensorization-freeze.md`
and `../research/explorations/2026-09-03-tensorization-acceptance.md`; the latter records
validation and the final publication/CI status.

The two comparison certificates, `LemAmbientIntrinsicPoincareComparison.lean` and
`LemLegacyRelaxedPoincareComparison.lean`, package five and seven proved comparisons respectively.
Their types preserve the reviewed generality, including empty test classes, zero-dimensional
support, zero finite constants and infinite optima. Gaussian transport through these bridges is
now proved. See the [comparison guide](../formalization/FunctionalInequalities/Poincare/Euclidean/README.md).

The `Solutions` default target builds all seventeen certificates plus `GaussianAxiomAudit.lean` and
`FoundationAxiomAudit.lean`. The latter guards 27 foundation and comparison declarations; each new
certificate also has its own axiom guard. These checks require exactly `propext`, `Classical.choice`
and `Quot.sound`. Compiled user examples remain in
[`examples/PoincareFoundation.lean`](../examples/PoincareFoundation.lean).

## Analytic comparison certificates and definition checks

[`LemLogConcaveIntrinsicAbsoluteContinuity.lean`](LemLogConcaveIntrinsicAbsoluteContinuity.lean)
certifies intrinsic absolute continuity from the compact-set definition.
[`ThmSelectedLiteratureConstantEquivalence.lean`](ThmSelectedLiteratureConstantEquivalence.lean)
then certifies the general log-concave constant equality, including singular ambient laws and
zero-dimensional support. Both certificates and all new reusable declarations have default-build
axiom guards. The full Borell density/moment theorem remains separate; read the
[general proof record](../research/decisions/2026-09-06-general-logconcave-comparison.md).

[`ThmSmoothLipschitzConstantEquivalence.lean`](ThmSmoothLipschitzConstantEquivalence.lean)
packages eight proved interfaces from `Energy/LocalSlope/Gradient.lean` and
`Poincare/LocalSlope/SmoothTestComparison.lean`. The pointwise and almost-everywhere slope identities
feed energy/domain identification and the finite-constant and extended-optimum comparisons.
The final comparison assumes intrinsic absolute continuity. The node is
`proved / checked_by: lean`; all eight components and the certificate have default-build
transitive axiom guards. Read the
[proof record](../research/decisions/2026-09-06-smooth-literature-proofs.md).

[`LemCovarianceTestCoreDensity.lean`](LemCovarianceTestCoreDensity.lean) contains the certificate
for four proved approximation contracts: weighted compact-support cutoff, full-gradient
mollification, weighted L2 approximation, and interval-preserving bounded L1 smoothing. Its
certificate and four reusable declarations have default-build transitive axiom guards. The
node is `proved / checked_by: lean`; see the
[acceptance record](../research/decisions/2026-09-06-weighted-approximation-acceptance.md).

`StatementChecks.lean` is a default-build target for the literal KLS proposition and its domain
and boundary encodings. It is not a ledger proof certificate. All seventeen mathematical certificates,
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

`LemPoincareGaussianOneDimensional.lean` is the default-build entry point for
`lem:poincare-gaussian-one-dimensional`, with `status: proved` and `checked_by: lean`.
It imports `Poincare/Gaussian/Real.lean` directly and contains the sole node certificate,
`Solutions.LemPoincareGaussianOneDimensional.certificate`. The certificate combines, for every
`m : ℝ` and `v : NNReal`, that `(v : ℝ)` is a valid constant for `gaussianReal m v` and that the
optimal `ENNReal` constant equals v. The file also prints the 20 proof-complete library interfaces.
Seven typed applications cover the standard Gaussian, mean 3/variance 4, arbitrary-mean zero
variance, and the existing Dirac-law identity; they introduce no duplicate public theorem.

The imported Gaussian library is split into `Density` (7 declarations), `Hardy` (9), and `Real`
(4): density calculus and integrability feed interval/Tonelli half-line estimates, which feed the
fixed and sharp constants. All 20 declarations are proved, and the certificate and its local
import closure contain no forbidden proof escapes. Human semantic and mathematical review
confirmed the variance normalization, the separate zero-variance Dirac case, and the precise
smooth L2 finite-energy scope. Use the
[reading guide](../formalization/FunctionalInequalities/Poincare/Gaussian/README.md) for the
current theorem and architecture. The
[candidate package](../research/decisions/2026-09-04-gaussian-poincare-candidate.md) and
[source audit](../research/explorations/2026-09-04-gaussian-poincare-design.md) remain historical
review/provenance records. The current approved contract and verification evidence are in the
[Gaussian freeze](../research/decisions/2026-09-04-gaussian-poincare-freeze.md) and
[Gaussian acceptance record](../research/explorations/2026-09-04-gaussian-poincare-acceptance.md).

## Finite tensorization certificate

Issue #7 and node `lem:poincare-finite-tensorization` use
`solutions/LemPoincareFiniteTensorization.lean`, with `status: proved` and `checked_by: lean`.
Its sole named certificate covers the ledger claim. The 45 `#check @...` statements retain
the reusable API surface; eight Euclidean statement families and six concrete boundary cases
are checked through typed applications of that API. These applications add no duplicate
specialization declarations. The deduplication review remains in
`../research/explorations/2026-09-03-certificate-deduplication.md`; the original 53-name candidate
is preserved as history in `../research/decisions/2026-09-03-finite-tensorization-candidate.md`.

The scope includes binary reverse bounds/equality, finite fixed-constant tensorization,
finite optimal equality, and the supporting coordinate/isometry transports. Their library
proofs are implemented, as recorded in
`../research/explorations/2026-09-03-finite-tensorization-proofs.md`. Application checks verify
how these declarations specialize; the certificate separately combines the accepted conclusions.

The user's confirmation and final semantic review complete the human acceptance recorded in
`../research/decisions/2026-09-03-finite-tensorization-freeze.md` and
`../research/explorations/2026-09-03-finite-tensorization-acceptance.md`. The final publication
SHA and matching CI result are tracked in
[Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7).
The existing #2 and #6 nodes retain their ledger claims, certificate signatures, and independent
checked import closures.
See `../formalization/README.md` for the current reusable module layout.

## Borell equivalence certificate and implemented definition checks

[`ThmCompactBorellLogconcavityEquivalence.lean`](ThmCompactBorellLogconcavityEquivalence.lean)
certifies `thm:compact-borell-logconcavity-equivalence`: compact-set log-concavity of a Borel
probability law on a finite-dimensional real normed space is equivalent to Bobkov's Borel/inner-measure
formulation, including singular laws, null sets, proper affine supports and dimension zero. Its
`certificate` wraps `KLS.LogConcave.borel_iff`; the certificate, the library theorem and the two
compactness/inner-regularity lemmas have default-build axiom guards. The node is
`proved / checked_by: lean`. Read the
[proof handoff](../research/decisions/2026-09-07-borell-equivalence-claude-handoff.md) and the
[completion record](../research/decisions/2026-09-07-borell-equivalence-and-conditional-fiber-proofs.md).

`StatementChecks.lean` contains twenty-five named, proved checks with standard-only axiom guards, plus
axiom guards for the six proved conditional-fiber contracts in `KLS/ConditionalFiber.lean`
(iterated base integral, a.e. finite conditional second moment, joint measurability, version
independence, representative independence and the L² identification). The definition node
`def:conditional-fiber-form` therefore carries `\leanok`; it is not a ledger theorem. The raw
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
axiom guards. The node is `proved / checked_by: lean`. Read the
[statement decision](../research/decisions/2026-09-07-borell-density-statements.md) and the
[proof record](../research/decisions/2026-09-07-borell-density-proofs.md).

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
Read [the record](../research/decisions/2026-09-08-covariance-core-closure.md).

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
carry default-build axiom guards. Read
[the record](../research/decisions/2026-09-08-affine-covariance-relaxation-closed.md).

## Affine constant translation-invariance certificate

[`LemAffinePoincareTranslationInvariance.lean`](LemAffinePoincareTranslationInvariance.lean)
certifies `lem:affine-poincare-translation-invariance`. For every log-concave law `μ` and every
ambient vector `b` its sole `certificate` packages: the translate `Probability.translateLaw μ b`
is log-concave; its ambient covariance operator and the direction of its affine support are those of
`μ`; a linear isometric equivalence of the two intrinsic `L²` spaces preserves variance and
intertwines the affine covariance relaxations; `Poincare.CovarianceGradient.Intrinsic.constant` is unchanged; `μ` has a
finite ambient second moment; and translating by the negative barycenter gives zero mean. Typed
applications cover centering on every `EuclideanSpace ℝ (Fin n)` and dimension zero. The certificate
and twelve reusable declarations carry default-build axiom guards. Read
[the record](../research/decisions/2026-09-08-affine-poincare-translation-invariance.md).

## Affine and isotropic reduction certificate

[`ThmAffineIsotropicReduction.lean`](ThmAffineIsotropicReduction.lean) certifies
`thm:affine-isotropic-reduction`. For every finite `K` its sole `certificate` packages the pairwise
equivalences of `KLS.IsotropicBound K` (isotropic log-concave laws have literature constant at most
`K`), `KLS.CovarianceBound K` (log-concave laws have literature constant at most `K ‖Cov‖`) and
`KLS.AffineBound K` (log-concave laws have affine covariance constant at most `K`), each quantified
over every finite-dimensional Euclidean space of a fixed universe, and the implication from the affine
bound in universe zero to `KLS.Conjecture`. Typed applications cover the covariance-normalized bound
on every `EuclideanSpace ℝ (Fin n)` and dimension zero. The certificate and fifteen reusable
declarations carry default-build axiom guards. Read
[the record](../research/decisions/2026-09-08-affine-isotropic-reduction.md).

## Ambient/intrinsic covariance certificate

[`LemAmbientIntrinsicCovariance.lean`](LemAmbientIntrinsicCovariance.lean) certifies
`lem:ambient-intrinsic-covariance`. Under an explicit finite second moment, its sole `certificate`
packages: the ambient covariance operator annihilates the orthogonal complement of the
affine-support direction, restricts on that direction to the covariance operator of the intrinsic
law, has the same operator norm, the intrinsic covariance is positive definite, and a
zero-dimensional direction gives zero operators. Typed applications cover the Euclidean family
including dimension zero. The certificate and nine reusable declarations in
`Probability/IntrinsicCovariance.lean` have default-build axiom guards. The node is
`proved / checked_by: lean`. Read the
[record](../research/decisions/2026-09-07-ambient-intrinsic-covariance.md).
