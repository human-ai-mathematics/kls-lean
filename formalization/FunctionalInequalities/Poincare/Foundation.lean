module

public import FunctionalInequalities.Energy.Form.ClosedQuadratic
public import FunctionalInequalities.Energy.Form.Comparison
public import FunctionalInequalities.Energy.Form.Dirichlet
public import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison
public import FunctionalInequalities.Energy.CovarianceGradient.Basic
public import FunctionalInequalities.Energy.WeightedGradient.Closable
public import FunctionalInequalities.Energy.WeightedGradient.Core
public import FunctionalInequalities.Energy.CovarianceGradient.Isometry
public import FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv
public import FunctionalInequalities.Energy.WeightedGradient.Basic
public import FunctionalInequalities.Energy.CovarianceGradient.Translation
public import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic
public import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
public import FunctionalInequalities.Energy.SmoothGradient.Basic
public import FunctionalInequalities.Energy.SmoothGradient.Closed
public import FunctionalInequalities.Energy.SmoothGradient.Core
public import FunctionalInequalities.Energy.SmoothGradient.Density
public import FunctionalInequalities.Energy.SmoothGradient.Dirichlet
public import FunctionalInequalities.Energy.SmoothGradient.NormalDirection
public import FunctionalInequalities.Energy.SmoothGradient.Quadratic
public import FunctionalInequalities.Energy.Euclidean.WeakDerivative
public import FunctionalInequalities.Energy.Form.Core
public import FunctionalInequalities.Energy.Form.Functional
public import FunctionalInequalities.Energy.Form.QuadraticPreEnergy
public import FunctionalInequalities.Energy.Relaxation.Approximation
public import FunctionalInequalities.Energy.Relaxation.Basic
public import FunctionalInequalities.Energy.Relaxation.Contraction
public import FunctionalInequalities.Energy.Relaxation.LinearPMap
public import FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
public import FunctionalInequalities.Energy.Relaxation.Quadratic
public import FunctionalInequalities.Energy.Relaxation.Recovery
public import FunctionalInequalities.L2.MeanVariance
public import FunctionalInequalities.Poincare.Comparison
public import FunctionalInequalities.Poincare.SmoothGradient.Comparison
public import FunctionalInequalities.Poincare.CovarianceGradient.Intrinsic
public import FunctionalInequalities.Poincare.CovarianceGradient.Translation
public import FunctionalInequalities.Poincare.LipschitzGradient.Comparison
public import FunctionalInequalities.Poincare.SmoothGradient.Intrinsic
public import FunctionalInequalities.Poincare.SmoothTest.Comparison
public import FunctionalInequalities.Poincare.SmoothGradient.Ambient
public import FunctionalInequalities.Poincare.L2.Comparison
public import FunctionalInequalities.Poincare.L2.Energy
public import FunctionalInequalities.Poincare.SmoothTest.Optimal
public import FunctionalInequalities.Poincare.Relaxation
public import FunctionalInequalities.Probability.Support.Affine
public import FunctionalInequalities.Probability.Basic
public import FunctionalInequalities.Probability.Covariance.Factorization
public import FunctionalInequalities.Probability.Covariance.Whitening

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
  the intrinsic law, and the affine covariance Poincaré constant
  `Poincare.CovarianceGradient.Intrinsic.constant`, with
  transport of the covariance relaxation and its optimal constant along translations and linear
  isometric equivalences and general continuous linear equivalences, the whitening of a positive
  definite covariance, the ambient translation invariance of the affine constant, and the
  identification of the identity-weighted Lipschitz gradient relaxation constant with the legacy
  and literature constants; no Poincaré inequality is exported;
* the weighted gradient as a partially defined operator on `L²(ν)`, the generic identification of
  the sequential relaxation of `‖T f‖²` with `‖T̄ f‖²` for closable `T`, integration by parts for
  Lipschitz functions, and closability, dense domain and smooth core of the weighted gradient
  under absolute continuity, null support frontier and local domination of Haar measure.

The smooth-test theorems remain available from `Poincare.SmoothTest.Basic` and its existing
downstream modules. Both concrete test layers use ordinary `C∞` regularity (`ContDiff ℝ ∞` in
Mathlib v4.33); this aggregate still does not identify their optimal constants with a Cheeger or
spectral-gap formulation.

## Reading and using this API

Start with `Poincare.L2Energy` for the inequality and optimal constant, then read
`Poincare.SmoothGradient.Intrinsic` for the selected concrete energy. Read
`Energy.Relaxation.Basic` and `Energy.Relaxation.Quadratic` when the proof needs approximation or
closedness. `examples/PoincareFoundation.lean` at the repository root contains compiled applications
and boundary examples; the adjacent `README.md` explains their mathematical meaning and the source
hierarchy.

This aggregate intentionally lists its exports explicitly. Applications can use this one import;
reusable library modules should import the subject modules they actually use.
-/
