# Log-concave tools and representation theorems

This directory uses the compact-set definition of `KLS.LogConcave` from
[compact-set log-concavity](../../Probability/LogConcave.lean). Log-concave measures may be singular in the ambient
space. Intrinsic results use the direction space of the affine support and include dimension zero.
Each module's declarations and documentation specify its exact assumptions and mathematical sources.

## Reading order

| Module | Contents | Scope |
| --- | --- | --- |
| [Transport.lean](Transport.lean) | Affine-isometric transport, intrinsic coordinates, and support geometry | Proved |
| [Borel.lean](Borel.lean) | Equivalence of compact-set and Borel-set log-concavity | Proved; no density or second-moment premise |
| [Density/AbsoluteContinuity.lean](Density/AbsoluteContinuity.lean) | Small-ball estimates, intrinsic absolute continuity, and support-boundary results | Proved; does not construct a full log-concave density representative |
| [Density/BorellRepresentation/Intrinsic.lean](Density/BorellRepresentation/Intrinsic.lean) | Density representative, positivity in the interior, local bounds, and moments | Proved; packaged by `Solutions.ThmBorellLogconcaveDensity.certificate` |
| [Covariance.lean](Covariance.lean) | Well-definedness contract for the affine covariance pre-energy on log-concave laws: intrinsic second moments, a.e. differentiability of Lipschitz tests, and dependence of energy only on the L² class | Proved; contract for definition node `def:affine-poincare-constant`, without closedness or Poincaré conclusions |
| [WeightedGradient/Basic.lean](WeightedGradient/Basic.lean) | Dense definition and closability of the weighted gradient operator `g ↦ B∇g` for full-dimensional log-concave laws, equality of smooth-core closures, relaxation as the squared norm of the closure, and intrinsic-law versions | Proved; packaged by `Solutions.LemCovarianceCoreClosure.certificate`, without Poincaré, translation-invariance, or KLS conclusions |
| [WeightedGradient/Closure.lean](WeightedGradient/Closure.lean) | Closed gradient for arbitrary bounded linear weights, closedness, and dense domain; independent of semigroup generation | Proved |
| [WeightedGradient/Energy.lean](WeightedGradient/Energy.lean) | Identification of the squared norm of the closed unit-weight gradient with canonical/Cheeger energy | Proved |
| [Cheeger.lean](Cheeger.lean) | Log-concave specialization of Cheeger-energy identification via intrinsic absolute continuity | Proved; the general-law version is in Energy/Cheeger/Identification |
| [ClosedForm.lean](ClosedForm.lean) | Affine covariance relaxation is a closed quadratic form; tests form a sequential core; isometry and constant invariance under intrinsic-law translation; equality with the squared norm of the closed operator on the ℝ + C_c^∞ core (the CMH closed form) | Proved; packaged by `Solutions.ThmAffineCovarianceRelaxationClosed.certificate`, without a Poincaré inequality, ambient translation invariance, or KLS |
| [Translation.lean](Translation.lean) | Ambient translation preserves compact-set log-concavity; ambient second moments and barycenters of log-concave laws; translation by the negative barycenter gives a centered law | Proved; packaged with constant invariance from `Poincare/CovarianceGradient/Translation.lean` by `Solutions.LemAffinePoincareTranslationInvariance.certificate`, without a Poincaré inequality, isotropic reduction, or KLS |
| [Isotropic.lean](Isotropic.lean) | Continuous linear equivalences preserve log-concavity; pairwise equivalence of `IsotropicBound`, `CovarianceBound`, and `AffineBound`; centered and whitened isotropic laws; `AffineBound → Conjecture` | Proved; packaged by `Solutions.ThmAffineIsotropicReduction.certificate`, without asserting that any formulation holds for some K |
| [Line/Density.lean](Line/Density.lean) | Borell density structure `LineDensity` for real log-concave laws; the support interior is an interval carrying all mass; points with distribution value in (0,1) lie in that interior; chord lower bounds and extrapolation upper bounds for `log ρ`, and a supporting exponential at the median | Proved; no Poincaré conclusion |
| [Line/Hazard.lean](Line/Hazard.lean) | Four-point inequality `ρ a ρ e ≤ ρ b ρ c`; monotone hazard inequality `ρ x μ(Ioi y) ≤ ρ y μ(Ioi x)` and its reflection; median bounds `2ρ(m)(1−F) ≤ ρ`, `2ρ(m)F ≤ ρ`; supporting-line bound `ρ ≤ ρ(m) + k(F − 1/2)` | Proved; uses `Probability/Line/{Cdf,ExpIntegral}` |
| [Line/Hardy.lean](Line/Hardy.lean) | Integration-by-parts Hardy step on intervals; directed unions with rational endpoints on half-lines, with any interior anchor on the same side of the median (constant still `1/ρ(m)²`); smooth-test Poincaré inequality `SmoothTest.Holds ν (1/ρ(m))²` | Proved; constant expressed through median density, without variance |
| [Line/Variance.lean](Line/Variance.lean) | Monotonicity of `φ(F x) − (x − m)`; `∫(x−m)(F−1/2) dν ≥ 1/(12ρ(m))`; Bobkov variance bound `1/(12ρ(m)²) ≤ Var` | Proved; equality for the uniform law |
| [Line/Poincare.lean](Line/Poincare.lean) | Bobkov constant: `C_P^lit(ν) ≤ 12·Var_ν` (real and extended variance); zero constant for zero-dimensional affine support; `logConcave_dirac` | Proved independently of the constant-4 route; retained as a historical corollary |
| [Line/Isoperimetry.lean](Line/Isoperimetry.lean) | One-dimensional isoperimetry (2026-09-19): `LineDensity.mul_min_le_relativePerimeter` (`2ρ(m)·min(νU,1−νU) ≤ P_ρ(U)` for any smooth domain, without boundary discreteness), `two_mul_le_minkowskiConstant` (`2ρ(m) ≤ h_M`, via `h_M = h_S`), `le_two_mul` (`ρ ≤ 2ρ(m)`), `one_div_le_evariance` (`Var ≥ 1/(12M²)`), `interior_support_nonempty` |
| [Line/Buser.lean](Line/Buser.lean) | First stage of the Buser direction (2026-09-19): `evariance_le_smoothTest_constant` (linear test), `Isoperimetry.minkowskiConstant_map` (isometric transport), `LogConcave.inv_minkowskiConstant_sq_le` (`Ψ² ≤ 12·C_P^smooth` on the line), `LogConcave.inverseScale_sq_le_of_finrank_le_one` (`Ψ_KLS² ≤ 12·C_P^lit` for affine-support dimension `≤ 1`); `n ≥ 2` and constant `π` unproved at this stage |
| [Line/Profile.lean](Line/Profile.lean) | The mean lies in the support interior; supporting line `ρ ≤ A(1−F)+BF` (`A,B ≥ 0`); affine-model variance bound `1/(√A+√B)⁴ ≤ Var`; profile bound `F(1−F) ≤ σρ` | Proved; uses the affine quantile model in `Probability/Line/AffineProfile.lean` |
| [Line/SharpHardy.lean](Line/SharpHardy.lean) | Truncated test `clip a b f`, its centered version, and tail integral `G̃`; integration by parts `∫h² dμ = −∫_a^b f' G̃`; ground-state identity and boundary-term control; `∫_a^b G̃²ρ/W² ≤ 4∫h² dμ`; `Var(clip) ≤ 4·Var_ν·∫f'² dν` | Proved; `[a,b] ⊆ Ω` must straddle the median |
| [Line/SharpPoincare.lean](Line/SharpPoincare.lean) | Vanishing tails (anchored half-line Hardy bounds and absolute continuity of the integral); `(1+δ)` splitting; `SmoothTest.Holds ν (4·Var)`; `C_P^lit(ν) ≤ 4·Var_ν` (real and extended variance), with `12` as a corollary | Proved; packaged by `Solutions.ThmOneDimensionalLogConcavePoincare.certificate`; constant 4 is attained by the exponential law, without asserting a higher-dimensional result |
| [Line/OfDensity.lean](Line/OfDensity.lean) | Converse: a real probability law with a log-concave Lebesgue density is compact-set log-concave, `LineDensity.logConcave` | Proved using one-dimensional Prékopa–Leindler from `Probability/Line/BrunnMinkowski.lean`; converse to `LogConcave.exists_lineDensity` |

Local dependencies:

```text
Definitions → Transport → AbsoluteContinuity → BorellRepresentation → Covariance → Translation ─┐
            → Borel ─────────────────────────────┘                  → WeightedGradient → ClosedForm   → Isotropic
```

The local `Line/` chain is `Density → Hazard → {Hardy, Variance} → Poincare`. `Density` uses
`BorellRepresentation` and `Probability/Line/Cdf`; `Poincare` additionally uses `Poincare.lean`
(equality of smooth-test and literature constants) and `Isotropic` (full affine support implies
nonempty support interior).

`WeightedGradient` uses `Energy/WeightedGradient/{Basic,Closable,Core}`. Log-concavity supplies
only three premises: `ν ≪ Haar`, a null support boundary, and local domination of Haar by `ν`
on compact subsets of the support interior.

`Isotropic` also uses `Energy/CovarianceGradient/LinearEquiv` (transport under general linear
equivalences), `Probability/Covariance/Whitening` (self-adjoint inverse square root of positive
definite covariance), and `Poincare/LipschitzGradient/Comparison` (the bridge from unit-weight
Lipschitz-gradient relaxation to the literature constant). Log-concavity supplies log-concavity
of the image law, full support, and positive definite intrinsic covariance.

`Translation` also uses `Poincare/CovarianceGradient/Translation` (identification of translated
affine supports, directions, and intrinsic laws, and constant invariance for arbitrary Borel laws)
and affine-isometric transport from `Transport`. Log-concavity supplies only log-concavity of
the translated law and ambient second moments.

`Covariance` also uses `Energy/CovarianceGradient/Basic`, which defines the covariance-weighted
Lipschitz-gradient pre-energy for any probability law. Log-concavity supplies the contract's
premises: absolute continuity, a null support boundary, and moments.

`AbsoluteContinuity` also uses `Probability/Domination/Averages`. `BorellRepresentation` uses both
absolute continuity (to construct the density representative) and the Borel-set formulation
(for Borell's tail lemma and exponential moments).

## Imports and use

```lean
import FunctionalInequalities.KLS.LogConcave.Borel
import FunctionalInequalities.KLS.LogConcave.Density.AbsoluteContinuity

#check FunctionalInequalities.KLS.LogConcave.borel_iff
#check FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous
```

The literature Poincaré-constant comparison combines these tools in
[Poincare.lean](../../KLS/LogConcave/Poincare.lean). Existing declaration names are unchanged;
old module paths have no forwarding files; the
[generated module directory](../../../MODULES.md) lists current paths.

`Density/BorellRepresentation/` is divided into
[Basic](Density/BorellRepresentation/Basic.lean) (properties of density representatives),
[Moments](Density/BorellRepresentation/Moments.lean) (tails and moments),
[Construction](Density/BorellRepresentation/Construction.lean) (existence construction), and
[Intrinsic](Density/BorellRepresentation/Intrinsic.lean) (intrinsic interfaces).
