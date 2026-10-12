import FunctionalInequalities.L2.Duality
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Approximation
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Perimeter
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Correlation
import FunctionalInequalities.KLS.LogConcave.SmoothBuser
import FunctionalInequalities.Analysis.TestFunctionOrder
import FunctionalInequalities.Analysis.WaveSplitting.GeneratorBounds
import FunctionalInequalities.Analysis.WaveSplitting.Localization
import FunctionalInequalities.Analysis.WaveSplitting.FlowDerivative
import FunctionalInequalities.Analysis.WaveSplitting.Residual
import FunctionalInequalities.Analysis.WaveSplitting.WeightedEnergy
import FunctionalInequalities.Analysis.WaveSplitting.Compatibility
import FunctionalInequalities.Analysis.WaveSplitting.TimeAverage
import FunctionalInequalities.Analysis.WaveSplitting.AverageError
import FunctionalInequalities.Analysis.WaveSplitting.Potential
import FunctionalInequalities.Analysis.Semigroup.Exponential.Counterexample
import FunctionalInequalities.Analysis.Semigroup.Generated.Domain
import FunctionalInequalities.Analysis.Semigroup.Generated.FormDomain
import FunctionalInequalities.Analysis.Semigroup.Generated.Smoothing
import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
import FunctionalInequalities.Analysis.Semigroup.Generated.Curvature
import FunctionalInequalities.Analysis.Semigroup.Generated.Convergence
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain
import FunctionalInequalities.Poincare.SmoothTest.Basic
import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.SmoothTest.Linear
import FunctionalInequalities.Poincare.Product.Tensorization
import FunctionalInequalities.Poincare.Product.Reverse
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
import FunctionalInequalities.Poincare.Gaussian.Real
import FunctionalInequalities.KLS.Statement
import FunctionalInequalities.KLS.Target
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.KLS.LogConcave.WeakLimit
import FunctionalInequalities.KLS.LogConcave.Stein
import FunctionalInequalities.KLS.LogConcave.HessianStein
import FunctionalInequalities.Energy.DualNorm
import FunctionalInequalities.KLS.LogConcave.Borel
import FunctionalInequalities.KLS.LogConcave.Tail
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.KLS.Geometry.Perimeter.Recovery
import FunctionalInequalities.KLS.ConditionalFiber.Basic
import FunctionalInequalities.KLS.ConditionalFiber.Closed
import FunctionalInequalities.KLS.ConditionalFiber.EnergyComparison
import FunctionalInequalities.KLS.ConditionalFiber.SliceKernel
import FunctionalInequalities.Poincare.Euclidean.RawEnergyObstruction
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Intrinsic
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Hessian
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Posterior
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Growth
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Regular
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Buser
import FunctionalInequalities.Probability.Covariance.Intrinsic
import FunctionalInequalities.KLS.LogConcave.Covariance
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic
import FunctionalInequalities.KLS.LogConcave.ClosedForm
import FunctionalInequalities.KLS.LogConcave.Translation
import FunctionalInequalities.KLS.LogConcave.Isotropic
import FunctionalInequalities.KLS.LogConcave.Line.Poincare
import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare
import FunctionalInequalities.KLS.LogConcave.Line.OfDensity
import FunctionalInequalities.KLS.LogConcave.ConditionalFiber
import FunctionalInequalities.Probability.Line.BrunnMinkowski
import FunctionalInequalities.Probability.Line.Haar
import FunctionalInequalities.Probability.Line.GaussianProfile
import FunctionalInequalities.Probability.Quantile
import FunctionalInequalities.Energy.LocalSlope.Relaxation
import FunctionalInequalities.Energy.Cheeger.Basic
import FunctionalInequalities.KLS.LogConcave.Cheeger
import FunctionalInequalities.Analysis.Lipschitz.VectorCoarea
import FunctionalInequalities.Analysis.Lipschitz.Local
import FunctionalInequalities.Analysis.Sard.Sharp
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
import FunctionalInequalities.KLS.Geometry.Cheeger.LocalSlopeCoarea
import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski
import FunctionalInequalities.KLS.Geometry.Cheeger.BVIdentification
import FunctionalInequalities.KLS.Geometry.Perimeter.ConvexSupport
import FunctionalInequalities.KLS.Geometry.Perimeter.LocalLipschitzTests
import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation
import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski
import FunctionalInequalities.KLS.Geometry.Cheeger.UpperMinkowskiContent
import FunctionalInequalities.KLS.Geometry.Perimeter.UpperMinkowskiRecovery
import FunctionalInequalities.KLS.Geometry.Cheeger.Inequality
import FunctionalInequalities.KLS.Geometry.Cheeger.BuserProfile
import FunctionalInequalities.Energy.Euclidean.Slope.Comparison
import FunctionalInequalities.Energy.Euclidean.Slope.Recovery
import FunctionalInequalities.Energy.Euclidean.Slope.Density
import FunctionalInequalities.Energy.Euclidean.ZeroGradient
import FunctionalInequalities.Energy.Cheeger.Identification
import FunctionalInequalities.KLS.LogConcave.Line.Buser
import FunctionalInequalities.KLS.LogConcave.Line.DensityBound
import FunctionalInequalities.KLS.LogConcave.Line.CheegerVariance
import FunctionalInequalities.KLS.LogConcave.Line.Grunbaum
import FunctionalInequalities.Poincare.LocalSlope.Gradient
import FunctionalInequalities.Analysis.Semigroup.Resolvent.Form
import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic
import FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction
import FunctionalInequalities.Analysis.Semigroup.Exponential.Dissipation
import FunctionalInequalities.Analysis.Semigroup.AdjointComp
import FunctionalInequalities.Analysis.Semigroup.VonNeumann
import FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit
import FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation
import FunctionalInequalities.Analysis.Semigroup.Yosida.Laws
import FunctionalInequalities.Analysis.Semigroup.Exponential.Limit
import FunctionalInequalities.Analysis.Semigroup.Yosida.Limit
import FunctionalInequalities.Analysis.Semigroup.Generated.Basic
import FunctionalInequalities.Analysis.Semigroup.Generated.Laws
import FunctionalInequalities.Analysis.Semigroup.Exponential.MeanValue
import FunctionalInequalities.Analysis.Semigroup.Generated.Generator
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic
import FunctionalInequalities.Analysis.Semigroup.Generated.Markov
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Energy
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare
import FunctionalInequalities.Analysis.BakryEmery.Calculus
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.ConvexHessian
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessianCutoff
import FunctionalInequalities.Analysis.BakryEmery.Curvature
import FunctionalInequalities.Analysis.BakryEmery.Gamma
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
import FunctionalInequalities.Analysis.Semigroup.AdjointClosure
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator
import FunctionalInequalities.Analysis.BakryEmery.WeakGamma
import FunctionalInequalities.Analysis.BakryEmery.RegularizedNorm
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Integrated
import FunctionalInequalities.Energy.WeightedGradient.Leibniz
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Gamma
import FunctionalInequalities.L2.BoundedMultiplier
import FunctionalInequalities.L2.PositiveMap
import FunctionalInequalities.L2.Composition
import FunctionalInequalities.L2.Components
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel
import FunctionalInequalities.KLS.LogConcave.Density.Tilted
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore
import FunctionalInequalities.Analysis.Mollification
import FunctionalInequalities.Analysis.TemperateGrowth
import FunctionalInequalities.Analysis.Cutoff.Integrability
import FunctionalInequalities.Analysis.Cutoff.Conservativity
import FunctionalInequalities.Analysis.Cutoff.Profile
import FunctionalInequalities.Analysis.DiagonalSelector
import FunctionalInequalities.Analysis.IteratedDerivative.Log
import FunctionalInequalities.Analysis.IteratedDerivative.GradientJet
import FunctionalInequalities.Analysis.IteratedDerivative.Symmetry
import FunctionalInequalities.Analysis.IteratedDerivative.Bilinear
import FunctionalInequalities.Analysis.IteratedDerivative.InnerProduct
import FunctionalInequalities.Analysis.Matrix.Trace
import FunctionalInequalities.Analysis.Majorization
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range
import FunctionalInequalities.KLS.LogConcave.BrascampLieb
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GammaTwo
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.TestClass
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.FormRange
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.TestClassExtension
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ReversePoincare
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GaussianProfile
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SelfImprovement
import FunctionalInequalities.Analysis.Tensor.Symmetrization
import FunctionalInequalities.Analysis.Tensor.Coordinate
import FunctionalInequalities.Analysis.Tensor.Multilinear
import FunctionalInequalities.Analysis.Tensor.Coefficients
import FunctionalInequalities.Analysis.Semigroup.Generated.Inverse
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Temperate
import FunctionalInequalities.Analysis.Semigroup.Generated.ApproximateEigenvector
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ApproximateEigenfunction
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Tilt
import FunctionalInequalities.Analysis.Tensor.BasisChange
import FunctionalInequalities.Analysis.DyadicSummation
import FunctionalInequalities.KLS.BKL.PoissonIterate.Basic
import FunctionalInequalities.KLS.BKL.PoissonIterate.Domain
import FunctionalInequalities.KLS.BKL.PoissonIterate.Permutation
import FunctionalInequalities.KLS.BKL.PoissonIterate.Defect
import FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor
import FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry
import FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion
import FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative
import FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
import FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Tilt.Tensor
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor
import FunctionalInequalities.Analysis.BakryEmery.TensorEnergy
import FunctionalInequalities.KLS.LogConcave.Regular
import FunctionalInequalities.KLS.LogConcave.RegularAffine
import FunctionalInequalities.KLS.LogConcave.RegularIsotropic
import FunctionalInequalities.KLS.LogConcave.RegularIsometry
import FunctionalInequalities.KLS.LogConcave.RegularPoincare
import FunctionalInequalities.KLS.LogConcave.IsotropicReduction
import FunctionalInequalities.KLS.BKL.Suspension.Basic
import FunctionalInequalities.Probability.Line.Laplace
import FunctionalInequalities.Probability.Product
import FunctionalInequalities.Probability.QuadraticTilt
import FunctionalInequalities.Probability.Stein.Kernel
import FunctionalInequalities.Probability.Stein.DualBound
import FunctionalInequalities.Probability.Stein.HessianKernel
import FunctionalInequalities.Poincare.SmoothTest.WeakLimit
import FunctionalInequalities.KLS.BKL.Suspension.Law
import FunctionalInequalities.KLS.BKL.Suspension.Cumulant
import FunctionalInequalities.KLS.BKL.Suspension.Density
import FunctionalInequalities.KLS.BKL.Suspension.Moments
import FunctionalInequalities.KLS.BKL.Suspension.Derivatives
import FunctionalInequalities.KLS.BKL.Proposition71
import FunctionalInequalities.KLS.BKL.Reduction
import FunctionalInequalities.KLS.BKL.LocalThirdCumulant
import FunctionalInequalities.KLS.BKL.CompactReduction
import FunctionalInequalities.KLS.BKL.SecondCumulant
import FunctionalInequalities.Analysis.BakryEmery.Tilt.Local
import FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz
import FunctionalInequalities.KLS.BKL.CumulantEnvelope
import FunctionalInequalities.L2.AffineDecomposition
import FunctionalInequalities.L2.Pairing
import FunctionalInequalities.Probability.Posterior.Exponent
import FunctionalInequalities.Probability.Posterior.CompactPrior
import FunctionalInequalities.Probability.Posterior.Coercive
import FunctionalInequalities.Probability.Posterior.CompactQuadratic
import FunctionalInequalities.KLS.BKL.PosteriorResponse
import FunctionalInequalities.KLS.BKL.PosteriorCovariance
import FunctionalInequalities.KLS.IsotropicSupport
import FunctionalInequalities.Probability.Posterior.CompactDomain
import FunctionalInequalities.Probability.Posterior.Generator
import FunctionalInequalities.Probability.Posterior.JointRegularity
import FunctionalInequalities.Probability.Covariance.Positivity
import FunctionalInequalities.Probability.Covariance.CauchySchwarz
import FunctionalInequalities.Probability.Conditioning
import FunctionalInequalities.Probability.ConvexSupport
import FunctionalInequalities.Analysis.Convex.Legendre
import FunctionalInequalities.Analysis.Extremum
import FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment
import FunctionalInequalities.Analysis.Convex.LegendreVariation.Perturbation
import FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative
import FunctionalInequalities.Analysis.Convex.BoundedConjugate
import FunctionalInequalities.Analysis.Convex.AffineMaximum
import FunctionalInequalities.Analysis.Convex.PointwiseCompactness
import FunctionalInequalities.Analysis.Convex.RadialExtension
import FunctionalInequalities.Probability.MomentMeasure.Basic
import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
import FunctionalInequalities.Probability.MomentMeasure.Compactness
import FunctionalInequalities.Analysis.Convex.Affine
import FunctionalInequalities.Analysis.Convex.SupportingPlane
import FunctionalInequalities.Analysis.Convex.Coercivity
import FunctionalInequalities.KLS.CEK.Competitors
import FunctionalInequalities.KLS.CEK.VariationalMaximum
import FunctionalInequalities.KLS.CEK.BoundedPrimal
import FunctionalInequalities.Probability.MomentMeasure.Affine
import FunctionalInequalities.Probability.MomentMeasure.Baseline
import FunctionalInequalities.Probability.MomentMeasure.Coercivity
import FunctionalInequalities.Probability.MomentMeasure.Integrability
import FunctionalInequalities.Probability.MomentMeasure.Normalization
import FunctionalInequalities.Probability.MomentMeasure.Truncation
import FunctionalInequalities.Probability.CoordinateThirdMoment
import FunctionalInequalities.Analysis.Operator.Positive
import FunctionalInequalities.Analysis.Operator.InverseSqrt
import FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt
import FunctionalInequalities.Analysis.Matrix.Positivity
import FunctionalInequalities.Analysis.Matrix.Sign
import FunctionalInequalities.Analysis.Matrix.Integral
import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
import FunctionalInequalities.Analysis.Matrix.LogDet
import FunctionalInequalities.Analysis.Convex.Subgradient
import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
import FunctionalInequalities.Analysis.BakryEmery.InverseHessianEnergy
import FunctionalInequalities.Analysis.BakryEmery.HessianTrace
import FunctionalInequalities.Analysis.BakryEmery.UniformIntervalPotential
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.UniformIntervalClient
import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
import FunctionalInequalities.Analysis.Operator.Coordinates
import FunctionalInequalities.Analysis.RingInverseDerivative
import FunctionalInequalities.Analysis.Gronwall
import FunctionalInequalities.Probability.Diffusion.Generator
import FunctionalInequalities.Probability.Diffusion.Cutoff
import FunctionalInequalities.Probability.Diffusion.Setup
import FunctionalInequalities.Probability.Diffusion.Dynkin
import FunctionalInequalities.Probability.Posterior.LogPartition
import FunctionalInequalities.KLS.BKL.Localization.Standardization
import FunctionalInequalities.KLS.BKL.Localization.Coefficients
import FunctionalInequalities.KLS.BKL.Localization.Energy
import FunctionalInequalities.Probability.Diffusion.Existence
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation
import FunctionalInequalities.KLS.LogConcave.HminusOne
import FunctionalInequalities.Analysis.Matrix.Piola
import FunctionalInequalities.Analysis.Tensor.SlotAction
import FunctionalInequalities.KLS.CEK.PartitionVariation
import FunctionalInequalities.Analysis.Convex.SecondDifference
import FunctionalInequalities.Analysis.WeakDerivative
import FunctionalInequalities.KLS.CEK.MomentMap
import FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator
import FunctionalInequalities.Analysis.MollificationHessian
import FunctionalInequalities.KLS.BKL.Localization.NoiseBound
import FunctionalInequalities.KLS.BKL.Localization.Process
import FunctionalInequalities.Probability.Diffusion.Transport

/-!
# Functional inequalities

Root module for functional-inequality definitions, proved results, and explicit draft statements.
The proved results include linear-test lower bounds, binary tensorization,
finite Hilbert-product optimal-constant equality, and the sharp one-dimensional Gaussian
Poincaré constant. It also exports the layered `L²`/extended-energy foundation for future
developments. Node certificates are compiled separately from `solutions/`.

The compact/Borel log-concavity equivalence, the six conditional-fiber contracts, the Borell
density-representative, local-bound and moment conclusions of
`KLS/LogConcave/Density/BorellRepresentation/Intrinsic.lean`, and the ambient/intrinsic covariance comparison are
proved. `Poincare.CovarianceGradient.Intrinsic.constant` implements the affine covariance Poincaré constant as a
definition, with its log-concave well-definedness contracts in
`KLS/LogConcave/Covariance.lean`. `KLS/LogConcave/WeightedGradient/Basic.lean` proves that the
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
analytic inputs are `Probability/Line/Haar.lean` (Fubini splitting of a Haar measure along a line),
`KLS/ConditionalFiber/SliceKernel.lean` (the explicit slice kernel and its disintegration of the
joint law), and `Probability/Line/BrunnMinkowski.lean` with `KLS/LogConcave/Line/OfDensity.lean`
(one-dimensional Brunn--Minkowski and Prekopa--Leindler, hence compact-set log-concavity of a law
with a log-concave Lebesgue density).
`Energy/LocalSlope/Relaxation.lean` builds the asymptotic-Lipschitz constant beside the local
slope and the sequential `L²` relaxations of both, and `Energy/Cheeger/Basic.lean` defines the metric
Cheeger energy in the Blueprint's local-slope convention with its affine-support transport and
proves `𝓔^can_μ = 2 Ch_μ` whenever the intrinsic law is absolutely continuous with respect to a
Haar measure, hence for every log-concave law
(`cor:absolutely-continuous-relaxation-two-cheeger`). The singular case is closed by
`Energy/Euclidean/Slope/Comparison.lean` (a smooth test's asymptotic Lipschitz constant is its
gradient norm, so the three relaxations are sandwiched for every Borel law),
`Energy/Euclidean/Slope/Recovery.lean` (mollification recovers globally Lipschitz tests by smooth
ones, with the cutoff tools that reduce admissible tests to them) and
`Energy/Euclidean/Slope/Density.lean` (the local slope of a continuous function is Borel, a Lipschitz
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
`KLS/Geometry/Perimeter/Recovery.lean` also exports the proved smooth recovery sequence for
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

`KLS/Geometry/Cheeger/Equality.lean` closes the log-concave Cheeger line's first node: the Minkowski
and smooth relative-perimeter Cheeger infima agree for every law with a Borell density
(`lem:relative-perimeter-cheeger-infimum`, `Isoperimetry.minkowskiConstant_eq_smoothConstant`), so the
affine-support isoperimetric constant of a log-concave law is its smooth relative-perimeter infimum
and the inverse scales agree (the two isoperimetric clauses of
`thm:klartag-density-frontend-identification`); the former work-in-progress module
`KLS/WIP/CheegerInfimum.lean` is deleted and the `KLS/WIP/` directory with it.

`KLS/Geometry/Cheeger/Inequality.lean` (with the median lemma of `KLS/Geometry/Cheeger/Median.lean`) proves
the Cheeger half of the Cheeger–Buser comparison `thm:logconcave-cheeger-poincare-comparison`:
`C_P^smooth(ν) ≤ 4 / h_M(ν)²` for every Borel probability law and
`C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²` for every log-concave law
(`LogConcave.literatureConstant_le_four_mul_inverseScale_sq`). The pi-coefficient Buser half
is proved for smooth convex tilted full-dimensional laws at their exact extended literature
constant in `KLS/LogConcave/SmoothBuser.lean`; the arbitrary-law comparison remains open.

`KLS/LogConcave/Line/Isoperimetry.lean` and `KLS/LogConcave/Line/Buser.lean` prove the **Buser half in
dimension one with the explicit constant `12`**: for a log-concave law on the line, `h_M ≥ 2ρ(m)` at a
median, `ρ ≤ 2ρ(m)`, and `Var ≥ 1/(12 ρ_max²)`, so `Ψ² ≤ 12 C_P^smooth(ν)`; transported to every
log-concave law whose affine support has dimension at most one, `Ψ_KLS(μ)² ≤ 12 C_P^lit(μ)`
(`LogConcave.inverseScale_sq_le_of_finrank_le_one`). The Buser half in dimension `n ≥ 2`, and the
constant `π` for every finite-dimensional log-concave law, are **not** proved.
-/
