import FunctionalInequalities.Energy.Euclidean.SmoothGradient
import FunctionalInequalities.Poincare.L2Energy

/-!
# Poincaré optimization for the smooth-gradient relaxation

This module attaches the generic `L²` Poincaré optimizer to the concrete sequential relaxation
of globally smooth finite-gradient tests. Its names retain `smoothGradientRelaxation`: no
unproved identification with Cheeger energy or a closed Sobolev form is hidden here.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- The optimal Poincaré constant of the smooth-gradient sequential relaxation. -/
def smoothGradientRelaxationConstant (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] : ENNReal :=
  constantOfL2Energy μ (Energy.Euclidean.smoothGradientRelaxation μ)

/-- Validity of a finite Poincaré constant on the finite domain of the smooth-gradient
sequential relaxation. -/
def SmoothGradientRelaxationHolds (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] (C : NNReal) : Prop :=
  HoldsL2Energy μ (Energy.Euclidean.smoothGradientRelaxation μ) C

/-- A finite constant is valid for the smooth-gradient relaxation exactly when it bounds its
optimal extended constant. -/
theorem smoothGradientRelaxationHolds_iff_constant_le (μ : ProbabilityMeasure E)
    [FiniteDimensional ℝ E] [BorelSpace E] [SecondCountableTopology E] (C : NNReal) :
    SmoothGradientRelaxationHolds μ C ↔
      smoothGradientRelaxationConstant μ ≤ (C : ENNReal) := by
  exact holdsL2Energy_iff_constant_le μ (Energy.Euclidean.smoothGradientRelaxation μ) C

end FunctionalInequalities.Poincare.Euclidean
