import FunctionalInequalities.Poincare.SmoothTest.Basic
import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.SmoothTest.Linear
import FunctionalInequalities.Poincare.Product.Tensorization
import FunctionalInequalities.Poincare.Product.Reverse
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
import FunctionalInequalities.Poincare.Gaussian.Real
import FunctionalInequalities.KLS.Statement
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.KLS.LogConcave.Borel
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.KLS.Geometry.PerimeterRecovery
import FunctionalInequalities.KLS.ConditionalFiber
import FunctionalInequalities.KLS.ConditionalFiber.Closed
import FunctionalInequalities.KLS.ConditionalFiber.EnergyComparison
import FunctionalInequalities.KLS.ConditionalFiber.SliceKernel
import FunctionalInequalities.Poincare.Euclidean.RawEnergyObstruction
import FunctionalInequalities.KLS.LogConcave.BorellRepresentation
import FunctionalInequalities.Probability.IntrinsicCovariance
import FunctionalInequalities.KLS.LogConcave.Covariance
import FunctionalInequalities.KLS.LogConcave.WeightedGradient
import FunctionalInequalities.KLS.LogConcave.ClosedForm
import FunctionalInequalities.KLS.LogConcave.Translation
import FunctionalInequalities.KLS.LogConcave.Isotropic
import FunctionalInequalities.KLS.LogConcave.Line.Poincare
import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare
import FunctionalInequalities.KLS.LogConcave.Line.OfDensity
import FunctionalInequalities.KLS.LogConcave.ConditionalFiber
import FunctionalInequalities.Probability.Line.BrunnMinkowski
import FunctionalInequalities.Probability.HaarLine
import FunctionalInequalities.Energy.LocalSlope.Relaxation
import FunctionalInequalities.Energy.Cheeger
import FunctionalInequalities.Analysis.Lipschitz.VectorCoarea
import FunctionalInequalities.Analysis.Lipschitz.Local
import FunctionalInequalities.Analysis.Sard.Sharp
import FunctionalInequalities.KLS.Geometry.CheegerEquality
import FunctionalInequalities.KLS.Geometry.CheegerInequality
import FunctionalInequalities.Energy.Euclidean.SlopeComparison
import FunctionalInequalities.Energy.Euclidean.SlopeRecovery
import FunctionalInequalities.Energy.Euclidean.SlopeDensity
import FunctionalInequalities.Energy.Cheeger.Identification
import FunctionalInequalities.KLS.LogConcave.Line.Buser

/-!
# Functional inequalities

Root module for functional-inequality definitions, proved results, and explicit draft statements.
The proved results include linear-test lower bounds, binary tensorization,
finite Hilbert-product optimal-constant equality, and the sharp one-dimensional Gaussian
Poincaré constant. It also exports the layered `L²`/extended-energy foundation for future
developments. Node certificates are compiled separately from `solutions/`.

The compact/Borel log-concavity equivalence, the six conditional-fiber contracts, the Borell
density-representative, local-bound and moment conclusions of
`KLS/LogConcave/BorellRepresentation.lean`, and the ambient/intrinsic covariance comparison are
proved. `Poincare.CovarianceGradient.Intrinsic.constant` implements the affine covariance Poincaré constant as a
definition, with its log-concave well-definedness contracts in
`KLS/LogConcave/Covariance.lean`. `KLS/LogConcave/WeightedGradient.lean` proves that the
weighted gradient operator of a full-dimensional log-concave law is densely defined and closable,
with smooth core and relaxation identified with its closure (`lem:covariance-core-closure`), and
`KLS/LogConcave/ClosedForm.lean` identifies the affine relaxation with the closed covariance
form of the CMH source (`thm:affine-covariance-relaxation-closed`), and
`KLS/LogConcave/Translation.lean` with `Poincare/CovarianceGradient/Translation.lean` prove that
ambient translation keeps log-concavity and the affine constant
(`lem:affine-poincare-translation-invariance`), and `KLS/LogConcave/Isotropic.lean` proves
the equivalence of the isotropic, covariance-normalized and affine KLS formulations for each fixed
`K` (`thm:affine-isotropic-reduction`); no statement that any of them holds for some `K`, and no
KLS proof, is included. `KLS/LogConcave/Line/SharpPoincare.lean` proves the sharp one-dimensional
bound `C_P^lit(ν) ≤ 4 Var_ν` for every log-concave law on the real line, zero variance included
(`thm:one-dimensional-logconcave-poincare`), through the distribution-function, hazard-rate, Hardy,
affine-profile and sharp-Hardy modules of `Probability/Line/` and `KLS/LogConcave/Line/`;
`KLS/LogConcave/Line/Poincare.lean` keeps the independent proof of Bobkov's constant `12`.
`KLS/ConditionalFiber/Closed.lean` proves that the conditional-fiber form is a Dirichlet energy on
`L²(μ)` for every Borel law and every direction law (`lem:conditional-fiber-form`), through the
two-point variance identity of `Probability/TwoPointVariance.lean`, and
`KLS/ConditionalFiber/EnergyComparison.lean` compares that energy with the local-slope gradient
energy under a fiber Poincaré input `κ` and transfers a form-gap bound `C` to
`C_P^lit(μ) ≤ κ C` (`lem:conditional-fiber-energy-comparison`).
`KLS/LogConcave/ConditionalFiber.lean` supplies that input for a full-dimensional log-concave law:
base-law almost every conditional fiber is log-concave on the line, hence `FiberBound μ ρ 4`,
`D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ` and `C_P^lit(μ) ≤ 4 C` (`cor:conditional-fiber-twelve-bound`). Its
analytic inputs are `Probability/HaarLine.lean` (Fubini splitting of a Haar measure along a line),
`KLS/ConditionalFiber/SliceKernel.lean` (the explicit slice kernel and its disintegration of the
joint law), and `Probability/Line/BrunnMinkowski.lean` with `KLS/LogConcave/Line/OfDensity.lean`
(one-dimensional Brunn--Minkowski and Prekopa--Leindler, hence compact-set log-concavity of a law
with a log-concave Lebesgue density).
`Energy/LocalSlope/Relaxation.lean` builds the asymptotic-Lipschitz constant beside the local
slope and the sequential `L²` relaxations of both, and `Energy/Cheeger.lean` defines the metric
Cheeger energy in the Blueprint's local-slope convention with its affine-support transport and
proves `𝓔^can_μ = 2 Ch_μ` whenever the intrinsic law is absolutely continuous with respect to a
Haar measure, hence for every log-concave law
(`cor:absolutely-continuous-relaxation-two-cheeger`). The singular case is closed by
`Energy/Euclidean/SlopeComparison.lean` (a smooth test's asymptotic Lipschitz constant is its
gradient norm, so the three relaxations are sandwiched for every Borel law),
`Energy/Euclidean/SlopeRecovery.lean` (mollification recovers globally Lipschitz tests by smooth
ones, with the cutoff tools that reduce admissible tests to them) and
`Energy/Euclidean/SlopeDensity.lean` (the local slope of a continuous function is Borel, a Lipschitz
test is patched by McShane extensions on finitely many compact cores of a slope-adapted Borel
partition, and so `SmoothGradient.relaxation ν ≤ LocalSlope.relaxation ν` for every Borel
probability law); `Energy/Cheeger/Identification.lean` then states the unconditional identity
`𝓔^can_μ = 2 Ch_μ` (`thm:smooth-gradient-relaxation-two-cheeger`) and the agreement of the two
Cheeger conventions for every Borel probability law, singular and zero-dimensional laws included;
the former work-in-progress module `Energy/WIP/Cheeger.lean` is deleted, and the repository has
no work-in-progress module left. Importing this aggregate certifies nothing by itself.

The imported modules record their sources beside the declarations: manuscript Definition 2.1
for the normalization, Remark 3.8 for the linear-test lower bound, BGL (2014), Proposition 4.3.1
for the binary fixed-constant upper bound, manuscript Theorem 3.4 for the finite-product identity,
and the manuscript Gaussian covariance family for the one-dimensional sharp constant. Their
comments also identify the local test-domain specifications, extended-real conventions, and
auxiliary results. `Poincare.Foundation` deliberately coexists with the accepted smooth-test API;
both now use ordinary `C∞` regularity. The foundation additionally exports sequential
lower-semicontinuity and recovery theorems, quadratic closure of dense pre-energies, the closed
smooth-gradient relaxation with its Dirichlet property, and intrinsic affine-support coordinates.
The absolute-continuity Cheeger identity and the density-based raw/core results above keep
their stated hypotheses; no unrestricted singular-law or spectral-gap identification is asserted.
`KLS/Geometry/PerimeterRecovery.lean` also exports the proved smooth recovery sequence for
finite relative perimeter, now linked by the corresponding Blueprint proof marker. This
auxiliary registration does not add a ledger certificate.

The proved comparison modules identify the ambient and intrinsic relaxations and the
finite-dimensional legacy optimum, so the accepted Gaussian bounds and constants can be
transported to the selected frontend through explicit equalities and fixed-constant equivalences.

`Analysis/Sard/Sharp.lean` proves the sharp finite-regularity Sard theorem `Analysis.sard` — the
critical values of a `C^n` real-valued function on an `n`-dimensional real normed space are
Lebesgue-null — by Morse's decomposition of an arbitrary set (`Analysis/Sard/{Chart,Disk,
MorseVanishing}.lean`), together with its consequence `Analysis.ae_forall_fderiv_ne_zero`; the
former work-in-progress module `KLS/WIP/AnalyticPrerequisites.lean` is deleted.
`Analysis/Lipschitz/VectorCoarea.lean` proves the codimension-`m` coarea formula for **globally
Lipschitz** maps (`Analysis.coarea_of_lipschitz`, the `C¹` pieces assembled componentwise from the
scalar ones), and `Analysis/Lipschitz/Local.lean` the **locally Lipschitz** version
(`Analysis.coarea_of_locallyLipschitz`), so the vector coarea chain `C¹ → Lipschitz → locally
Lipschitz` is level with the scalar one. None of this is a Sard theorem for vector-valued maps and
none of it is a ledger certificate.

`KLS/Geometry/CheegerEquality.lean` closes the log-concave Cheeger line's first node: the Minkowski
and smooth relative-perimeter Cheeger infima agree for every law with a Borell density
(`lem:relative-perimeter-cheeger-infimum`, `Isoperimetry.minkowskiConstant_eq_smoothConstant`), so the
affine-support isoperimetric constant of a log-concave law is its smooth relative-perimeter infimum
and the inverse scales agree (the two isoperimetric clauses of
`thm:klartag-density-frontend-identification`); the former work-in-progress module
`KLS/WIP/CheegerInfimum.lean` is deleted and the `KLS/WIP/` directory with it.

`KLS/Geometry/CheegerInequality.lean` (with the median lemma of `KLS/Geometry/Median.lean`) proves
the Cheeger half of the Cheeger–Buser comparison `thm:logconcave-cheeger-poincare-comparison`:
`C_P^smooth(ν) ≤ 4 / h_M(ν)²` for every Borel probability law and
`C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²` for every log-concave law
(`LogConcave.literatureConstant_le_four_mul_inverseScale_sq`); the Buser half is not proved.

`KLS/LogConcave/Line/Isoperimetry.lean` and `KLS/LogConcave/Line/Buser.lean` prove the **Buser half in
dimension one with the explicit constant `12`**: for a log-concave law on the line, `h_M ≥ 2ρ(m)` at a
median, `ρ ≤ 2ρ(m)`, and `Var ≥ 1/(12 ρ_max²)`, so `Ψ² ≤ 12 C_P^smooth(ν)`; transported to every
log-concave law whose affine support has dimension at most one, `Ψ_KLS(μ)² ≤ 12 C_P^lit(μ)`
(`LogConcave.inverseScale_sq_le_of_finrank_le_one`). The Buser half in dimension `n ≥ 2`, and the
constant `π`, are **not** proved.
-/
