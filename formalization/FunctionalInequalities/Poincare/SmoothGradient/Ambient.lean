import FunctionalInequalities.Energy.SmoothGradient.Basic
import FunctionalInequalities.Poincare.L2Energy

/-!
# Poincaré optimization for the smooth-gradient relaxation

This module attaches the generic `L²` Poincaré optimizer to the concrete sequential relaxation
of globally smooth finite-gradient tests. Its names retain `Energy.SmoothGradient.relaxation`: no
unproved identification with Cheeger energy or a closed Sobolev form is hidden here.
-/

-- `Ambient` refers to relaxation before passing to affine-support coordinates.

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.SmoothGradient.Ambient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- The optimal Poincaré constant of the smooth-gradient sequential relaxation. -/
def constant (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] : ENNReal :=
  L2Energy.constant μ (Energy.SmoothGradient.relaxation μ)

/-- Validity of a finite Poincaré constant on the finite domain of the smooth-gradient
sequential relaxation. -/
def Holds (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] (C : NNReal) : Prop :=
  L2Energy.Holds μ (Energy.SmoothGradient.relaxation μ) C

/-- A finite constant is valid for the smooth-gradient relaxation exactly when it bounds its
optimal extended constant. -/
theorem holds_iff_constant_le (μ : ProbabilityMeasure E)
    [FiniteDimensional ℝ E] [BorelSpace E] [SecondCountableTopology E] (C : NNReal) :
    Holds μ C ↔
      constant μ ≤ (C : ENNReal) := by
  exact L2Energy.holds_iff_constant_le μ (Energy.SmoothGradient.relaxation μ) C

end FunctionalInequalities.Poincare.SmoothGradient.Ambient
