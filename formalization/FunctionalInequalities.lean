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
(`cor:absolutely-continuous-relaxation-two-cheeger`); the singular case stays open in
`Energy/WIP/Cheeger.lean`, which this aggregate does not import. Importing this aggregate
certifies nothing by itself.

The imported modules record their sources beside the declarations: manuscript Definition 2.1
for the normalization, Remark 3.8 for the linear-test lower bound, BGL (2014), Proposition 4.3.1
for the binary fixed-constant upper bound, manuscript Theorem 3.4 for the finite-product identity,
and the manuscript Gaussian covariance family for the one-dimensional sharp constant. Their
comments also identify the local test-domain specifications, extended-real conventions, and
auxiliary results. `Poincare.Foundation` deliberately coexists with the accepted smooth-test API;
both now use ordinary `C∞` regularity. The foundation additionally exports sequential
lower-semicontinuity and recovery theorems, quadratic closure of dense pre-energies, the closed
smooth-gradient relaxation with its Dirichlet property, and intrinsic affine-support coordinates.
No Cheeger-energy, raw-test core, or spectral-gap identification is asserted by this aggregate.

The proved comparison modules identify the ambient and intrinsic relaxations and the
finite-dimensional legacy optimum, so the accepted Gaussian bounds and constants can be
transported to the selected frontend through explicit equalities and fixed-constant equivalences.
-/
