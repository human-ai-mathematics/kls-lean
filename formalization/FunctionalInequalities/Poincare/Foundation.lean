import FunctionalInequalities.Energy.ClosedQuadratic
import FunctionalInequalities.Energy.Comparison
import FunctionalInequalities.Energy.Dirichlet
import FunctionalInequalities.Energy.Euclidean.AffineComparison
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Basic
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Closable
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Core
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Isometry
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.LinearEquiv
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Operator
import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Translation
import FunctionalInequalities.Energy.Euclidean.IntrinsicAffine.Basic
import FunctionalInequalities.Energy.Euclidean.IntrinsicAffine.Closed
import FunctionalInequalities.Energy.Euclidean.SmoothGradient.Basic
import FunctionalInequalities.Energy.Euclidean.SmoothGradient.Closed
import FunctionalInequalities.Energy.Euclidean.SmoothGradient.Density
import FunctionalInequalities.Energy.Euclidean.SmoothGradient.Quadratic
import FunctionalInequalities.Energy.Euclidean.WeakDerivative
import FunctionalInequalities.Energy.FormCore
import FunctionalInequalities.Energy.Functional
import FunctionalInequalities.Energy.QuadraticPreEnergy
import FunctionalInequalities.Energy.Relaxation.Approximation
import FunctionalInequalities.Energy.Relaxation.Basic
import FunctionalInequalities.Energy.Relaxation.Contraction
import FunctionalInequalities.Energy.Relaxation.LinearPMap
import FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
import FunctionalInequalities.Energy.Relaxation.Quadratic
import FunctionalInequalities.Energy.Relaxation.Recovery
import FunctionalInequalities.L2.MeanVariance
import FunctionalInequalities.Poincare.Comparison
import FunctionalInequalities.Poincare.Euclidean.AffineComparison
import FunctionalInequalities.Poincare.Euclidean.AffineCovariance
import FunctionalInequalities.Poincare.Euclidean.AffineTranslation
import FunctionalInequalities.Poincare.Euclidean.LipschitzComparison
import FunctionalInequalities.Poincare.Euclidean.IntrinsicAffine
import FunctionalInequalities.Poincare.Euclidean.LegacyComparison
import FunctionalInequalities.Poincare.Euclidean.SmoothGradient
import FunctionalInequalities.Poincare.L2Comparison
import FunctionalInequalities.Poincare.L2Energy
import FunctionalInequalities.Poincare.Optimal
import FunctionalInequalities.Poincare.Relaxation
import FunctionalInequalities.Probability.AffineSupport
import FunctionalInequalities.Probability.Basic
import FunctionalInequalities.Probability.CovarianceSqrt
import FunctionalInequalities.Probability.CovarianceWhitening

/-!
# The foundation for Poincaré inequalities on real `L²`

This is the aggregate entry point for the new layered API:

* probability measures and intrinsic real `L²` variance;
* extended energies, form-core, closed-quadratic, and Dirichlet property layers;
* quadratic concrete pre-energies, sequential relaxation, lower semicontinuity, recovery
  sequences, and continuous contraction transfer;
* pure Rayleigh optimization and comparison;
* the bridge from finite `L²` energy domains to optimal Poincaré constants;
* the concrete `C∞` smooth-gradient realization, its quadratic and density theorems, and the
  closed-quadratic structure of its relaxation, named without assuming a Cheeger-energy theorem;
* the minimal closed full-measure affine carrier, its intrinsic probability law, and the
  linearly isometric equivalence between the ambient and intrinsic real `L²` spaces, including
  transport of the closed-quadratic relaxation;
* equality of ambient and intrinsic relaxations, preservation of arbitrary pre-energy Poincaré
  constants by relaxation, and equality with the finite-dimensional legacy smooth-test optimum.
* the globally Lipschitz covariance-weighted gradient pre-energy, its sequential relaxation on
  the intrinsic law, and the affine covariance Poincaré constant `Poincare.Affine.constant`, with
  transport of the covariance relaxation and its optimal constant along translations and linear
  isometric equivalences and general continuous linear equivalences, the whitening of a positive
  definite covariance, the ambient translation invariance of the affine constant, and the
  identification of the identity-weighted Lipschitz gradient relaxation constant with the legacy
  and literature constants; no Poincaré inequality is exported;
* the weighted gradient as a partially defined operator on `L²(ν)`, the generic identification of
  the sequential relaxation of `‖T f‖²` with `‖T̄ f‖²` for closable `T`, integration by parts for
  Lipschitz functions, and closability, dense domain and smooth core of the weighted gradient
  under absolute continuity, null support frontier and local domination of Haar measure.

The accepted legacy smooth-test theorems remain available from `Poincare.Basic` and its existing
downstream modules. Both concrete test layers use ordinary `C∞` regularity (`ContDiff ℝ ∞` in
Mathlib v4.33); this aggregate still does not identify their optimal constants with a Cheeger or
spectral-gap formulation.

## Reading and using this API

Start with `Poincare.L2Energy` for the inequality and optimal constant, then read
`Poincare.Euclidean.IntrinsicAffine` for the selected concrete energy. Read
`Energy.Relaxation.Basic` and `Energy.Relaxation.Quadratic` when the proof needs approximation or
closedness. `examples/PoincareFoundation.lean` at the repository root contains compiled applications
and boundary examples; the adjacent `README.md` explains their mathematical meaning and the source hierarchy.

This aggregate intentionally lists its exports explicitly. Applications can use this one import;
reusable library modules should import the subject modules they actually use.
-/
