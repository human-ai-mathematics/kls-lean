module

public import FunctionalInequalities.Probability.ExponentialMoments.Norm
public import FunctionalInequalities.Probability.ExponentialMoments.Temperate

/-! Generic finite-measure moments and normed-source temperate L2 clients. -/

@[expose] public section
set_option autoImplicit false
open FunctionalInequalities MeasureTheory
open scoped RealInnerProductSpace
namespace SourceLayout

theorem norm_moments {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (he : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (d : ℕ) :
    Integrable (fun x => ‖x‖ ^ d) μ :=
  Probability.integrable_norm_pow_of_exp μ hr he d

theorem rank_one_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : ℕ) (v : Fin d → E) (x : E) :
    ‖∏ j, ⟪x, v j⟫‖ ≤ ‖x‖ ^ d * ∏ j, ‖v j‖ :=
  Analysis.Tensor.norm_prod_inner_le d v x

theorem temperate_l2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (μ : Measure E)
    (he : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f : E → F} (hf : f.HasTemperateGrowth) : MemLp f 2 μ :=
  Probability.memLp_two_of_hasTemperateGrowth μ he hf

#print axioms SourceLayout.norm_moments
#print axioms SourceLayout.rank_one_bound
#print axioms SourceLayout.temperate_l2
end SourceLayout
