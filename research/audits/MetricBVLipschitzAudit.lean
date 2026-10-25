import FunctionalInequalities.Analysis.MetricBV.Basic
import FunctionalInequalities.Analysis.MetricBV.Finite
import FunctionalInequalities.Analysis.MetricBV.Approximation
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for the globally Lipschitz test-class bridge of the metric
BV perimeter on a finite Borel measure: the explicit truncated test and its pointwise bounds,
the explicit sequence theorems, the existence form (including an empty carrier) and the perimeter
upper bound. An application uses an approximant that is not a test (the constant one on `ℝ`, with
unbounded support). Only global Lipschitz functions and global `L¹` convergence are involved; no
identification with local Lipschitz or `L¹_loc` classes and no BV--Minkowski identification is
stated. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MetricBVLipschitzAudit

open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

section TruncatedTests

omit [MeasurableSpace X] [BorelSpace X]
theorem truncatedSlope (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (x : X) :
    FunctionalInequalities.Energy.LocalSlope.apply (Test.truncate x₀ R f hf) x ≤
      FunctionalInequalities.Energy.LocalSlope.apply f x +
        (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  exact apply_truncate_le x₀ R hf x

theorem truncatedDistance (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (B : Set X) (x : X) :
    ‖Test.truncate x₀ R f hf x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      ‖f x - B.indicator (1 : X → ℝ) x‖ₑ + (Metric.ball x₀ R)ᶜ.indicator 1 x := by
  exact enorm_truncate_sub_le x₀ R hf B x

end TruncatedTests

theorem explicitConvergence (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X) {B : Set X}
    {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncate x₀ n (f n) (hf n)) B)
      atTop (𝓝 0) := by
  exact tendsto_indicatorDistance_truncate ν x₀ hf hconv

theorem explicitCost (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X) {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n)) :
    liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop ≤
      liminf (fun n => ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact liminf_cost_truncate_le ν x₀ hf

theorem existenceForm (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply (f n) x ∂ν)
          atTop := by
  exact exists_approximatingSequence_of_lipschitz ν hf hconv

theorem perimeterBound (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤
      liminf (fun n => ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact perimeter_le_liminf_of_lipschitz ν hf hconv

/-- Empty carrier: the existence form still applies. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) (f : ℕ → Empty → ℝ) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply (f n) x ∂ν)
          atTop := by
  refine exists_approximatingSequence_of_lipschitz ν (fun n => ⟨0, fun x => x.elim⟩) ?_
  simp [Measure.eq_zero_of_isEmpty ν]

/-- An approximant that is not a test: the constant one on `ℝ` has unbounded support, yet it
bounds the perimeter of the whole line for the standard Gaussian law, which is therefore zero.
The finite-space theorem `perimeter_univ` does not apply here. -/
theorem gaussianWholeLine :
    perimeter (ProbabilityTheory.gaussianReal 0 1) (Set.univ : Set ℝ) = 0 := by
  have h := perimeter_le_liminf_of_lipschitz (ProbabilityTheory.gaussianReal 0 1)
    (B := Set.univ) (f := fun _ _ => (1 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 1⟩)
    (by simp)
  simp only [FunctionalInequalities.Energy.LocalSlope.apply_const, lintegral_zero,
    liminf_const] at h
  exact le_antisymm h bot_le

#print axioms truncatedSlope
#print axioms truncatedDistance
#print axioms explicitConvergence
#print axioms explicitCost
#print axioms existenceForm
#print axioms perimeterBound
#print axioms emptyCarrier
#print axioms gaussianWholeLine

end MetricBVLipschitzAudit
