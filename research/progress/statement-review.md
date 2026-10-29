# Statement and text scope review

Certificate contracts reviewed 2026-10-19; current endpoint notes updated 2026-10-20.
This is a contract review of the 34 registered certificates, their owning
definitions, and the live README, handoff, solution guide, ledger and Blueprint descriptions.
The [target reviews](target-reviews.md) retain the detailed paper correspondence; the
[proof path](PROOF-PATH.md) separates the cutoff proof from the uncut source construction.

The review checks quantifier order, explicit and derived hypotheses, constants, normalization,
dimension restrictions, test domains and the distinction between a conditional interface and a
closed theorem. It does not independently reprove every auxiliary declaration or certify every
unmapped paper statement. Compilation, transitive axiom checks, statement snapshots and kernel
replay are separate checks with the snapshot scopes in the [verification guide](../verification.md).

## Main definitions and source correspondence

- `KLS.Conjecture` chooses one finite `NNReal` constant before every dimension and law. Its
  covariance-normalized conclusion retains finite second moment and includes dimension zero
  and singular affine supports. The closed producer supplies a positive constant; the target's
  allowance of zero does not weaken the claimed existence of a finite universal bound.
- `KLS.Isotropic` includes `MemLp id 2`, zero barycenter and identity centered covariance.
  The moment field prevents a totalized integral from standing in for integrability.
- `KLS.LogConcave` tests compact sets with `0 < t < 1`, avoiding endpoint conventions for null
  sets and `0^0`. The Borel formulation uses inner measure for possibly nonmeasurable affine
  combinations. The compact combination is compact
  in every real normed space. Finite-dimensional density representation is a separate theorem.
- `Poincare.LocalSlope.Intrinsic.constant` uses the intrinsic affine-support law and locally
  Lipschitz, square-integrable, finite-slope-energy tests. The energy has no factor `1/2`.
  Finite valid constants are `NNReal`; an empty class of finite bounds gives optimum `⊤`.
  Ambient gradients for a singular law must not be substituted for intrinsic gradients without
  the proved restriction/extension bridges.
- BKL [arXiv:2610.05474v1](https://arxiv.org/abs/2610.05474v1), pp. 2, 10, 18, 25 and 28–30:
  the Taylor coefficient has factor `1/d!`; the cumulant has no factorial normalization; the
  coordinate tensor norm is Hilbert–Schmidt. Theorem 4.1 uses `m = d + 1`, so `d ≥ 1` includes
  its base `m = 2`. The two existential conditional helpers start at `d ≥ 2`; the explicit-153
  helper and closed certificate include `d = 1`. The universal cumulant premise of Proposition
  7.1 ranges over all dimensions, including the suspension's larger dimension. The local
  `K = 153` follows from the proved generator constant `17`; it is not a numerical constant
  stated by the paper. Theorem 1.1 chooses its constant before all dimensions and measures.
- Letwin [arXiv:2607.24164v1](https://arxiv.org/abs/2607.24164v1), Theorem 1.2, p. 3:
  for isotropic laws, `2 E‖∇⟨Mx,x⟩‖² = 8‖M‖²_HS`. The local certificate retains compact support,
  `n > 0` and every self-adjoint `M`, including singular and indefinite operators. It does not
  certify the noncompact source theorem. The separate
  [`letwinQuadraticBound`](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean)
  now proves that theorem, with the same constant and no compact-support premise; the
  separate `thm:letwin-quadratic-bound` certificate registers that full statement. Theorem 1.1
  has the paper-target `thm:letwin-log-quarter` through the BKL alternative route; the original
  third-moment/traced Klartag route remains unformalized, and Proposition 2.8 remains partial
  for full-dimensional laws. The inspected BKL and Letwin PDF hashes match the
  pins in the [literature register](LITERATURE.md).
- ADMG [arXiv:1603.08412v1](https://arxiv.org/html/1603.08412v1), Definition 3.3 and Theorem 3.6:
  the left relaxation uses measurable set sequences; the right uses globally Lipschitz function
  sequences. Both use global indicator `L¹` convergence. The certificate retains finite target
  mass and a measure finite on bounded Borel sets. It neither assumes properness nor asserts
  equality of the unrelaxed content and perimeter of each individual set.
- BGL Corollary 4.8.2: the local certificate has `C²` potentials, normalized tilted probability
  laws and the bound `1/ρ`. Locally Lipschitz finite-energy tests include smooth finite-energy
  tests; they must not be described as a larger class than the book's completed form domain.
  The closed-gradient-domain inequality and its optimum comparison are separate proved
  interfaces, recorded in the [target review](target-reviews.md).

The cutoff-energy statement assumes an actual `IsEldanCutoff` process. This is not an unchecked
existence premise in the closed cumulant proof: `exists_brownianSetup` and
`exists_isEldanCutoff` supply the setup and process in `cumulantBoundCompact_of_cutoffEnergyClaim`.
That proof applies the claim at `T = 0` and sends the positive tolerance to zero. The finite
horizon, cutoff weight and tolerance must remain visible when describing the energy certificate.

## Registered certificate contracts

Each entry refers to the `certificate` in the linked solution, with separately named corollaries
distinguished where necessary. All entries retain their existing proved status; this review adds
no certificate and changes no Lean statement.

| Certificate | Checked contract and boundary |
| --- | --- |
| [Linear test lower bound](../../solutions/LemLinearTestLower.lean) | Probability, finite second moment, every `D ≥ 0`; extended Rayleigh bound and covariance lower bound for the smooth-test constant. |
| [Binary tensorization](../../solutions/LemPoincareTensorization.lean) | Separate probability laws on complete second-countable real Hilbert spaces; Hilbert product, `max` of valid constants and the optimum upper bound. No form-domain equivalence is asserted. |
| [Finite tensorization](../../solutions/LemPoincareFiniteTensorization.lean) | Finite Hilbert product, exact supremum of factor optima; empty and singleton products, zero-dimensional factors and infinite optima included. |
| [One-dimensional Gaussian](../../solutions/LemPoincareGaussianOneDimensional.lean) | Every mean and nonnegative variance; exact constant equals variance, including the Dirac case. |
| [Ambient/intrinsic comparison](../../solutions/LemAmbientIntrinsicPoincareComparison.lean) | Any finite-dimensional Borel probability law; smooth restriction/extension, relaxed energy and optimal constants agree. No density or moment hypothesis. |
| [Raw/relaxed comparison](../../solutions/LemLegacyRelaxedPoincareComparison.lean) | Arbitrary pre-energy on probability `L²`; raw-test bounds agree with finite-domain relaxed bounds. Subsequent clauses specialize to smooth gradients. |
| [Weighted test density](../../solutions/LemCovarianceTestCoreDensity.lean) | Absolute continuity, arbitrary Haar normalization and arbitrary linear weight; weighted `L²` approximation, compact Lipschitz and smooth stages, bounded `L¹` variant. |
| [Smooth/Lipschitz constants](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean) | Differentiability for the pointwise identity; absolute continuity for a.e. gradient, energy and constant identities. Intrinsic clauses retain intrinsic absolute continuity. |
| [Intrinsic absolute continuity](../../solutions/LemLogConcaveIntrinsicAbsoluteContinuity.lean) | Compact-set log-concavity implies intrinsic absolute continuity for every Haar reference measure; singular ambient laws included. |
| [Selected/literature constants](../../solutions/ThmSelectedLiteratureConstantEquivalence.lean) | Log-concave laws; equality of intrinsic smooth-gradient and local-slope optima, including infinite values. |
| [Compact/Borel log-concavity](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) | Finite-dimensional normed spaces, arbitrary probability law; Borel-set combinations use inner measure. |
| [Borell density](../../solutions/ThmBorellLogconcaveDensity.lean) | One existential density with interior positivity and compact two-sided bounds, plus support and moment conclusions. Properties for every supplied density are separate library theorems. |
| [Ambient/intrinsic covariance](../../solutions/LemAmbientIntrinsicCovariance.lean) | Finite second moment; covariance restriction, perpendicular kernel, equal norms, positive definite intrinsic covariance and the zero-support case. |
| [Weighted core closure](../../solutions/LemCovarianceCoreClosure.lean) | Full-dimensional log-concave law, arbitrary linear weight and Haar measure; density, closability, graph core, and relaxation on and off the closure domain. |
| [Closed affine relaxation](../../solutions/ThmAffineCovarianceRelaxationClosed.lean) | Intrinsic covariance energy of log-concave laws; dense closed quadratic form, sequential core, translation and closed-gradient realization. |
| [Affine translation](../../solutions/LemAffinePoincareTranslationInvariance.lean) | Log-concave law; translations, covariance, support direction, `L²` energy intertwining and constant invariance; second moment and centered translate are produced. |
| [Affine/isotropic reduction](../../solutions/ThmAffineIsotropicReduction.lean) | Fixed finite `K`; equivalence of isotropic, covariance and affine bounds in a fixed universe. The final clause implies the `Fin n` KLS target; this is not itself a producer of `K`. |
| [Dirichlet relaxation](../../solutions/ThmSmoothGradientRelaxationDirichlet.lean) | Any finite-dimensional Borel probability law; Markov property and ambient/intrinsic Dirichlet forms. No Poincaré bound follows from this certificate alone. |
| [One-dimensional log-concave bound](../../solutions/ThmOneDimensionalLogConcavePoincare.lean) | All log-concave laws on `ℝ`; constant at most `4 Var`, in real and extended forms. No density premise; Dirac laws included. |
| [Raw/core agreement](../../solutions/ThmSmoothGradientRawCoreAgreementDensity.lean) | Supplied local-density data; agreement on smooth tests and sequential core. This hypothesis is retained. |
| [Conditional-fiber form](../../solutions/LemConditionalFiberForm.lean) | Probability law and direction law; Dirichlet form, nondegenerate-fiber quotient, two-point symmetry and dimension-dependent Lipschitz bound. No admissible-frame or spectral-gap conclusion. |
| [Fiber energy comparison](../../solutions/LemConditionalFiberEnergyComparison.lean) | Admissible frame, absolute continuity and supplied finite fiber constant `κ`; energy comparison and transfer of a supplied form gap. |
| [Log-concave fiber bound](../../solutions/CorConditionalFiberTwelveBound.lean) | Log-concavity, absolute continuity and admissible frame; constant `4` (hence `12`), with no supplied global frame gap. Dimension zero admits no such frame. |
| [Absolutely continuous Cheeger case](../../solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean) | Intrinsic absolute continuity; smooth/local-slope relaxation equality and canonical energy `= 2 Ch`. The premise is retained in this certificate. |
| [Cheeger infima](../../solutions/LemRelativePerimeterCheegerInfimum.lean) | Supplied Borell density relative to volume; equality of Minkowski and smooth-relative-perimeter infima. Empty admissible classes give `⊤`. |
| [Unconditional Cheeger identification](../../solutions/ThmSmoothGradientRelaxationTwoCheeger.lean) | Every finite-dimensional Borel probability law, singular included; relaxed energies agree and canonical energy `= 2 Ch`. Separate `conventions_agree` identifies both Cheeger conventions. |
| [ADMG relaxation](../../solutions/ThmRelaxedMinkowskiContentPerimeter.lean) | Metric Borel space, measure finite on bounded Borel sets, measurable finite-mass target; equality of relaxation infima. |
| [Bakry–Émery](../../solutions/ThmBakryEmeryPoincare.lean) | Normalized tilted probability law, `C²` potential and Hessian `≥ ρ Id`, `ρ > 0`; literature optimum `≤ 1/ρ`. Gaussian witnesses discharge the hypotheses, including dimension zero. |
| [BKL suspension](../../solutions/PropBklSuspension.lean) | `d ≥ 2`, `b > 0`, universal cumulant premise; isotropic regular law and `L²` test; squared Taylor norm `≤ 2b/(d!)² · ‖f‖²`. |
| [BKL Taylor criterion](../../solutions/ThmBklTaylorCriterion.lean) | One universal positive constant; regular centered law with covariance `≤ Id`, `R ≥ 1` and all Taylor bounds; literature optimum `≤ K R²`. |
| [Compact Letwin](../../solutions/ThmLetwinCompactQuadraticBound.lean) | Positive dimension, compact isotropic log-concave law, arbitrary self-adjoint quadratic form; exact `8‖M‖²_HS`. |
| [Cutoff energy](../../solutions/LemBklCutoffEnergy.lean) | Every `d ≥ 1`, compact isotropic log-concave prior, unit direction, positive tolerance, finite horizon, sufficiently large radius and every actual cutoff process. |
| [BKL cumulants](../../solutions/ThmBklCumulantBound.lean) | One `K ≥ 1`, every order `m ≥ 2`, dimension and isotropic log-concave law; no compactness or conditional analytic premise. Explicit witness `153`. |
| [BKL Poincaré](../../solutions/ThmBklPoincare.lean) | One positive constant before every `n ≥ 1` and isotropic log-concave law. The producer on arbitrary finite-dimensional spaces and `KLS.kls` are separate named conclusions. |

## Corrections and unchanged boundaries

The review corrects the ADMG set/function distinction, the BGL test-domain comparison, the
Borell existential/universal attribution, stale claims that BKL and the unconditional Cheeger
identification lacked certificates, the source attribution of `153`, the displayed order range
of the conditional cumulant helpers, and retired module labels. Supporting Blueprint lemmas
now point to the completed results rather than making obsolete repository-wide non-claims.

No hypothesis, quantifier, constant, normalization, dimension range, Lean definition, theorem
type or proof is changed by these reviews. The compact Letwin certificate retains its compact
scope; the separate noncompact theorem is now proved. The uncut Eldan construction and literal
stochastic identities remain unformalized locally. The four exploratory routes keep
their mathematically open hypotheses and their existing status. A source-form conclusion
obtained by the cutoff route does not establish each intermediate statement of the uncut route.

The [public-interface review](public-interface-review.md) adds the exact OpenAI model and bridge,
the synchronized upstream regularization contracts and the maintainer's current review scope.
It separates reported personal review, Nicolas's limited inspection and agent/compiler checks.

## Module ownership and public-name migration

The following is the complete module map for this batch. Paths in the first column are retired;
all consumers import the destination directly. Both columns are relative to
`formalization/FunctionalInequalities/`. Module ownership changes retain the existing public
namespaces; they do not introduce forwarding modules or change mathematical scope.

| Retired module | Current owner |
| --- | --- |
| `KLS/Geometry/Coarea/Isoperimetry.lean` | [Analysis/Coarea/Isoperimetry.lean](../../formalization/FunctionalInequalities/Analysis/Coarea/Isoperimetry.lean) |
| `KLS/Geometry/Coarea/Lipschitz.lean` | [Analysis/Coarea/Lipschitz.lean](../../formalization/FunctionalInequalities/Analysis/Coarea/Lipschitz.lean) |
| `KLS/Geometry/Coarea/LocallyLipschitz.lean` | [Analysis/Coarea/LocallyLipschitz.lean](../../formalization/FunctionalInequalities/Analysis/Coarea/LocallyLipschitz.lean) |
| `KLS/Geometry/Coarea/Regular.lean` | [Analysis/Coarea/Regular.lean](../../formalization/FunctionalInequalities/Analysis/Coarea/Regular.lean) |
| `KLS/Geometry/Coarea/Smooth.lean` | [Analysis/Coarea/Smooth.lean](../../formalization/FunctionalInequalities/Analysis/Coarea/Smooth.lean) |
| `KLS/Geometry/Slice/Critical.lean` | [Analysis/Hausdorff/Slice/Critical.lean](../../formalization/FunctionalInequalities/Analysis/Hausdorff/Slice/Critical.lean) |
| `KLS/Geometry/Slice/Measurable.lean` | [Analysis/Hausdorff/Slice/Measurable.lean](../../formalization/FunctionalInequalities/Analysis/Hausdorff/Slice/Measurable.lean) |
| `KLS/Geometry/Slice/OpenMeasurable.lean` | [Analysis/Hausdorff/Slice/OpenMeasurable.lean](../../formalization/FunctionalInequalities/Analysis/Hausdorff/Slice/OpenMeasurable.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Approximation.lean` | [Analysis/MetricBV/Approximation.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Approximation.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Basic.lean` | [Analysis/MetricBV/Basic.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Basic.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Complement.lean` | [Analysis/MetricBV/Complement.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Complement.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Counterexample.lean` | [Analysis/MetricBV/Counterexample.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Counterexample.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Finite.lean` | [Analysis/MetricBV/Finite.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Finite.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Scaling.lean` | [Analysis/MetricBV/Scaling.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Scaling.lean) |
| `KLS/Geometry/Perimeter/MetricBV/Transport.lean` | [Analysis/MetricBV/Transport.lean](../../formalization/FunctionalInequalities/Analysis/MetricBV/Transport.lean) |
| `Poincare/Product/Variance.lean` | [Probability/Variance/Product.lean](../../formalization/FunctionalInequalities/Probability/Variance/Product.lean) |
| `KLS/Definitions.lean` | [Probability/LogConcave.lean](../../formalization/FunctionalInequalities/Probability/LogConcave.lean) |
| `KLS/BKL/Theorem41.lean` | [KLS/BKL/Cumulant/Induction.lean](../../formalization/FunctionalInequalities/KLS/BKL/Cumulant/Induction.lean) |
| `KLS/BKL/Proposition71.lean` | [KLS/BKL/TaylorBound.lean](../../formalization/FunctionalInequalities/KLS/BKL/TaylorBound.lean) |

Public-name changes are a separate migration. The namespace for each row is
`FunctionalInequalities.KLS.BKL.Localization`; no compatibility aliases are added.

| Previous name | Current name |
| --- | --- |
| `theorem41Compact` | `exists_cumulantBoundCompact_of_letwinCompact` |
| `theorem41` | `exists_cumulantBound_of_letwinCompact` |
| `theorem11` | `exists_isotropicBound` |

The source/type comparison retains hypotheses, parameter names and order, universes, visibility,
normalization and dimensional scope after this explicit name map. In particular, the two
existential cumulant interfaces still start at `d ≥ 2`; the separately certified explicit-153
endpoint includes the base `d = 1`. The generic MetricBV client is part of this migration;
separate KLS application and API-search usability changes are outside it.
