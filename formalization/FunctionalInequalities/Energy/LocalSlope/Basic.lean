import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Squared local metric slope and its finite-energy test class -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Energy.LocalSlope

section Metric

variable {X : Type*} [MetricSpace X]

/-- Pointwise local metric slope as the infimum of punctured-ball secant suprema.
The real quotient at `y = x` is zero, so including the center does not change the supremum.
At an isolated point the slope is zero. This is not the two-moving-point Lipschitz constant. -/
def apply (f : X → ℝ) (x : X) : ENNReal :=
  ⨅ (r : ℝ) (_ : 0 < r), ⨆ (y : X) (_ : dist y x < r),
    ENNReal.ofReal (dist (f y) (f x) / dist y x)

@[simp] theorem apply_const (c : ℝ) (x : X) :
    apply (fun _ : X ↦ c) x = 0 := by
  unfold apply
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le (1 : ℝ) (iInf_le_of_le zero_lt_one (by simp))

/-- The local-slope definition handles a one-point carrier without a nontriviality premise. -/
theorem apply_eq_zero_of_subsingleton [Subsingleton X] (f : X → ℝ) (x : X) :
    apply f x = 0 := by
  have hf : f = fun _ ↦ f x := funext fun y ↦ congrArg f (Subsingleton.elim y x)
  rw [hf, apply_const]

end Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/-- The unnormalized squared local-slope integral in an intrinsic coordinate space. -/
def energy (ν : ProbabilityMeasure E) (f : E → ℝ) : ENNReal :=
  ∫⁻ x, apply f x ^ 2 ∂(ν : Measure E)

/-- The literature test domain, independent of the candidate Poincaré constant. -/
structure Admissible (ν : ProbabilityMeasure E) (f : E → ℝ) : Prop where
  locallyLipschitz : LocallyLipschitz f
  memLp_two : MemLp f 2 (ν : Measure E)
  finite_energy : energy ν f ≠ ⊤


end FunctionalInequalities.Energy.LocalSlope
