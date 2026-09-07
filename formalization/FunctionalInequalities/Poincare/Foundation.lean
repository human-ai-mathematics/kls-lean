import FunctionalInequalities.Energy.ClosedQuadratic
import FunctionalInequalities.Energy.Comparison
import FunctionalInequalities.Energy.Dirichlet
import FunctionalInequalities.Energy.Euclidean.AffineComparison
import FunctionalInequalities.Energy.Euclidean.IntrinsicAffine
import FunctionalInequalities.Energy.Euclidean.IntrinsicAffineClosed
import FunctionalInequalities.Energy.Euclidean.SmoothGradient
import FunctionalInequalities.Energy.Euclidean.SmoothGradientClosed
import FunctionalInequalities.Energy.Euclidean.SmoothGradientDensity
import FunctionalInequalities.Energy.Euclidean.SmoothGradientQuadratic
import FunctionalInequalities.Energy.FormCore
import FunctionalInequalities.Energy.Functional
import FunctionalInequalities.Energy.QuadraticPreEnergy
import FunctionalInequalities.Energy.Relaxation
import FunctionalInequalities.Energy.RelaxationApproximation
import FunctionalInequalities.Energy.RelaxationContraction
import FunctionalInequalities.Energy.RelaxationLowerSemicontinuous
import FunctionalInequalities.Energy.RelaxationQuadratic
import FunctionalInequalities.Energy.RelaxationRecovery
import FunctionalInequalities.L2.MeanVariance
import FunctionalInequalities.Poincare.Comparison
import FunctionalInequalities.Poincare.Euclidean.AffineComparison
import FunctionalInequalities.Poincare.Euclidean.IntrinsicAffine
import FunctionalInequalities.Poincare.Euclidean.LegacyComparison
import FunctionalInequalities.Poincare.Euclidean.SmoothGradient
import FunctionalInequalities.Poincare.L2Comparison
import FunctionalInequalities.Poincare.L2Energy
import FunctionalInequalities.Poincare.Optimal
import FunctionalInequalities.Poincare.Relaxation
import FunctionalInequalities.Probability.AffineSupport
import FunctionalInequalities.Probability.Basic

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

The accepted legacy smooth-test theorems remain available from `Poincare.Basic` and its existing
downstream modules. Both concrete test layers use ordinary `C∞` regularity (`ContDiff ℝ ∞` in
Mathlib v4.33); this aggregate still does not identify their optimal constants with a Cheeger or
spectral-gap formulation.

## Reading and using this API

Start with `Poincare.L2Energy` for the inequality and optimal constant, then read
`Poincare.Euclidean.IntrinsicAffine` for the selected concrete energy. Read
`Energy.Relaxation` and `Energy.RelaxationQuadratic` when the proof needs approximation or
closedness. `examples/PoincareFoundation.lean` at the repository root contains compiled applications
and boundary examples; the adjacent `README.md` explains their mathematical meaning and the source hierarchy.

This aggregate intentionally lists its exports explicitly. Applications can use this one import;
reusable library modules should import the subject modules they actually use.
-/
