import FunctionalInequalities.Energy.Euclidean.IntrinsicAffineClosed
import FunctionalInequalities.Poincare.L2Energy

/-!
# Poincaré optimization in intrinsic affine coordinates

This module attaches the generic real-`L²` Poincaré optimizer to the closed quadratic
smooth-gradient relaxation on the direction of the affine support. The variance is still the
intrinsic `L²(μ)` variance of the original probability law; only the energy is evaluated through
the linearly isometric intrinsic-coordinate presentation.

The name deliberately retains `IntrinsicAffineSmoothGradientRelaxation`. No equality with the
ambient smooth-gradient relaxation, Cheeger energy `2 Ch`, or a spectral-gap constant is asserted.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The optimal Poincaré constant of the intrinsic-affine smooth-gradient relaxation. -/
def intrinsicAffineSmoothGradientRelaxationConstant (μ : ProbabilityMeasure E) : ENNReal :=
  constantOfL2Energy μ
    (Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation μ)

/-- Validity of a finite Poincaré constant on the finite domain of the intrinsic-affine
smooth-gradient relaxation. -/
def IntrinsicAffineSmoothGradientRelaxationHolds
    (μ : ProbabilityMeasure E) (C : NNReal) : Prop :=
  HoldsL2Energy μ (Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation μ) C

/-- A finite constant is valid for the intrinsic-affine relaxation exactly when it bounds the
optimal extended constant. -/
theorem intrinsicAffineSmoothGradientRelaxationHolds_iff_constant_le
    (μ : ProbabilityMeasure E) (C : NNReal) :
    IntrinsicAffineSmoothGradientRelaxationHolds μ C ↔
      intrinsicAffineSmoothGradientRelaxationConstant μ ≤ (C : ENNReal) := by
  exact holdsL2Energy_iff_constant_le μ
    (Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation μ) C

end FunctionalInequalities.Poincare.Euclidean
