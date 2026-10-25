import FunctionalInequalities.Energy.LocalSlope.Basic
import FunctionalInequalities.Probability.AffineSupport

/-! # Local-slope Poincaré bounds

`Holds` uses the given coordinate law; `Intrinsic.constant` first takes the intrinsic law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare.LocalSlope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- A finite bound on all literature tests in the displayed coordinate space.
The extended variance is finite by `Energy.LocalSlope.Admissible.memLp_two`;
no real-valued infinite integral is used. -/
def Holds (ν : ProbabilityMeasure E) (C : NNReal) : Prop :=
  ∀ f : E → ℝ, Energy.LocalSlope.Admissible ν f →
    evariance f (ν : Measure E) ≤ (C : ENNReal) * Energy.LocalSlope.energy ν f

/-- The infimum of finite nonnegative Poincaré bounds for `Probability.intrinsicMeasure μ`.
Intrinsic coordinates remove redundant affine directions using an affine isometry; they do not
normalize the covariance. An empty set of finite bounds gives `⊤`. A zero-dimensional intrinsic
coordinate space has value zero, as proved below. -/
def Intrinsic.constant (μ : ProbabilityMeasure E) : ENNReal :=
  ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds (Probability.intrinsicMeasure μ) C},
    (C.1 : ENNReal)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- All tests on a zero-dimensional coordinate space have zero variance. -/
theorem holds_zero_of_subsingleton [Subsingleton E] (ν : ProbabilityMeasure E) :
    Holds ν 0 := by
  intro f _
  have hf : f = fun _ ↦ f 0 := funext fun y ↦ congrArg f (Subsingleton.elim y 0)
  rw [hf]
  simp [evariance]

section DegenerateConstants

omit [CompleteSpace E]
/-- The literature optimum includes the zero-dimensional case with value zero. -/
theorem Intrinsic.constant_eq_zero_of_subsingleton [Subsingleton E] (μ : ProbabilityMeasure E) :
    Poincare.LocalSlope.Intrinsic.constant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le ⟨0, Poincare.LocalSlope.holds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
    (by simp)

/-- A zero-dimensional direction space gives literature optimum zero: every intrinsic test is
constant there. -/
theorem Intrinsic.constant_eq_zero_of_direction_subsingleton (μ : ProbabilityMeasure E)
    [Subsingleton (Probability.affineSupport μ).direction] :
    Poincare.LocalSlope.Intrinsic.constant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le ⟨0, Poincare.LocalSlope.holds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
    (by simp)

/-- The zero-dimensional case stated through the direction submodule. -/
theorem Intrinsic.constant_eq_zero_of_direction_eq_bot (μ : ProbabilityMeasure E)
    (h : (Probability.affineSupport μ).direction = ⊥) :
    Poincare.LocalSlope.Intrinsic.constant μ = 0 := by
  have : Subsingleton (Probability.affineSupport μ).direction :=
    Submodule.subsingleton_iff_eq_bot.mpr h
  exact Intrinsic.constant_eq_zero_of_direction_subsingleton μ

end DegenerateConstants

end FunctionalInequalities.Poincare.LocalSlope
