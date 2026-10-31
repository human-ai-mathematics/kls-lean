module

public import FunctionalInequalities.Probability.ExponentialMoments.Norm
public import FunctionalInequalities.L2.MeanVariance

@[expose] public section

open MeasureTheory FunctionalInequalities

namespace SourceLayout

/-- The smaller radius may be negative and the ambient measure need not be finite. -/
theorem negative_radius {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {r : ℝ} (hr : 0 ≤ r)
    (h : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    Integrable (fun x => Real.exp (-‖x‖)) μ := by
  simpa only [neg_one_mul] using
    Probability.integrable_exp_mul_norm_of_le h (show (-1 : ℝ) ≤ r by linarith)

/-- A probability law on a subsingleton carrier forces every L2 class to be constant. -/
theorem subsingleton_l2 {α : Type*} [MeasurableSpace α] [Subsingleton α]
    (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    ∃ c : ℝ, f = L2.const μ c := L2.exists_eq_const_of_subsingleton μ f

#print axioms negative_radius
#print axioms subsingleton_l2
end SourceLayout
