import FunctionalInequalities.Energy.Form.ClosedQuadratic
import FunctionalInequalities.Energy.Form.Comparison
import FunctionalInequalities.Energy.Form.Dirichlet
import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison
import FunctionalInequalities.Energy.CovarianceGradient.Basic
import FunctionalInequalities.Energy.WeightedGradient.Closable
import FunctionalInequalities.Energy.WeightedGradient.Core
import FunctionalInequalities.Energy.CovarianceGradient.Isometry
import FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv
import FunctionalInequalities.Energy.WeightedGradient.Basic
import FunctionalInequalities.Energy.CovarianceGradient.Translation
import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
import FunctionalInequalities.Energy.SmoothGradient.Basic
import FunctionalInequalities.Energy.SmoothGradient.Closed
import FunctionalInequalities.Energy.SmoothGradient.Core
import FunctionalInequalities.Energy.SmoothGradient.Density
import FunctionalInequalities.Energy.SmoothGradient.Dirichlet
import FunctionalInequalities.Energy.SmoothGradient.NormalDirection
import FunctionalInequalities.Energy.SmoothGradient.Quadratic
import FunctionalInequalities.Energy.Euclidean.WeakDerivative
import FunctionalInequalities.Energy.Form.Core
import FunctionalInequalities.Energy.Form.Functional
import FunctionalInequalities.Energy.Form.QuadraticPreEnergy
import FunctionalInequalities.Energy.Relaxation.Approximation
import FunctionalInequalities.Energy.Relaxation.Basic
import FunctionalInequalities.Energy.Relaxation.Contraction
import FunctionalInequalities.Energy.Relaxation.LinearPMap
import FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
import FunctionalInequalities.Energy.Relaxation.Quadratic
import FunctionalInequalities.Energy.Relaxation.Recovery
import FunctionalInequalities.L2.MeanVariance
import FunctionalInequalities.Poincare.Comparison
import FunctionalInequalities.Poincare.SmoothGradient.Comparison
import FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
import FunctionalInequalities.Poincare.CovarianceGradient.Translation
import FunctionalInequalities.Poincare.LipschitzGradient.Comparison
import FunctionalInequalities.Poincare.SmoothGradient.Intrinsic
import FunctionalInequalities.Poincare.SmoothTest.Comparison
import FunctionalInequalities.Poincare.SmoothGradient.Ambient
import FunctionalInequalities.Poincare.L2.Comparison
import FunctionalInequalities.Poincare.L2.Energy
import FunctionalInequalities.Poincare.SmoothTest.Optimal
import FunctionalInequalities.Poincare.Relaxation
import FunctionalInequalities.Probability.AffineSupport
import FunctionalInequalities.Probability.Basic
import FunctionalInequalities.Probability.Covariance.Factorization
import FunctionalInequalities.Probability.Covariance.Whitening

/-!
# The foundation for Poincaré inequalities on real `L²`

This is the aggregate entry point for the new layered API:

* probability measures and intrinsic real `L²` variance;
* extended energies, form-core, closed-quadratic, and Dirichlet property layers;
* quadratic concrete pre-energies, sequential relaxation, lower semicontinuity, recovery
  sequences, and continuous contraction transfer;
* pure Rayleigh optimization and comparison;
* the bridge from finite `L²` energy domains to optimal Poincaré constants;
* the concrete `C∞` smooth-gradient realization, its quadratic and density theorems, the
  closed-quadratic structure of its relaxation and its Dirichlet property under normal
  contractions, named without assuming a Cheeger-energy theorem, together with the
  normal-direction obstruction showing that the ambient pre-energy does not respect `L²`
  fibers on a proper affine support, and the raw/sequential-core agreement of the pre-energy
  with its relaxation for laws with a local density (`Energy.SmoothGradient.LocalDensity`);
* the minimal closed full-measure affine carrier, its intrinsic probability law, and the
  linearly isometric equivalence between the ambient and intrinsic real `L²` spaces, including
  transport of the closed-quadratic relaxation;
* equality of ambient and intrinsic relaxations, preservation of arbitrary pre-energy Poincaré
  constants by relaxation, and equality with the finite-dimensional smooth-test optimum.
* the globally Lipschitz covariance-weighted gradient pre-energy, its sequential relaxation on
  the intrinsic law, and the affine covariance Poincaré constant `Poincare.CovarianceGradient.Intrinsic.constant`, with
  transport of the covariance relaxation and its optimal constant along translations and linear
  isometric equivalences and general continuous linear equivalences, the whitening of a positive
  definite covariance, the ambient translation invariance of the affine constant, and the
  identification of the identity-weighted Lipschitz gradient relaxation constant with the legacy
  and literature constants; no Poincaré inequality is exported;
* the weighted gradient as a partially defined operator on `L²(ν)`, the generic identification of
  the sequential relaxation of `‖T f‖²` with `‖T̄ f‖²` for closable `T`, integration by parts for
  Lipschitz functions, and closability, dense domain and smooth core of the weighted gradient
  under absolute continuity, null support frontier and local domination of Haar measure.

The accepted smooth-test theorems remain available from `Poincare.SmoothTest.Basic` and its existing
downstream modules. Both concrete test layers use ordinary `C∞` regularity (`ContDiff ℝ ∞` in
Mathlib v4.33); this aggregate still does not identify their optimal constants with a Cheeger or
spectral-gap formulation.

## Reading and using this API

Start with `Poincare.L2Energy` for the inequality and optimal constant, then read
`Poincare.SmoothGradient.Intrinsic` for the selected concrete energy. Read
`Energy.Relaxation.Basic` and `Energy.Relaxation.Quadratic` when the proof needs approximation or
closedness. `examples/PoincareFoundation.lean` at the repository root contains compiled applications
and boundary examples; the adjacent `README.md` explains their mathematical meaning and the source hierarchy.

This aggregate intentionally lists its exports explicitly. Applications can use this one import;
reusable library modules should import the subject modules they actually use.
-/
