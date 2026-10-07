import FunctionalInequalities.L2.MeanVariance

/-!
# Components of vector-valued `L²` functions

For a real inner product space `G`, the scalar components of `g ∈ L²(μ; G)` along
`c ∈ G` are `(innerSL ℝ c).compLp g ∈ L²(μ)`. On a probability space the component means are the
components of the Bochner mean, and for an orthonormal basis the squared `L²` norms of the
components add up to `‖g‖²` (Parseval). These are the facts used to lift scalar results on `L²`
componentwise to tensor-valued data (Bizeul–Klartag–Lehec, Lemma 2.1, tensor version).
-/

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace
open MeasureTheory

namespace FunctionalInequalities.L2

variable {α : Type*} [MeasurableSpace α]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The mean of the component `⟪c, g⟫` of `g ∈ L²(μ; G)` is `⟪c, ∫ g⟫`. -/
theorem mean_compLp_innerSL [CompleteSpace G] (μ : ProbabilityMeasure α) (c : G)
    (g : Lp G 2 (μ : Measure α)) :
    mean μ ((innerSL ℝ c).compLp g) = ⟪c, ∫ x, g x ∂(μ : Measure α)⟫ := by
  rw [mean_eq_integral]
  calc
    ∫ x, ((innerSL ℝ c).compLp g) x ∂(μ : Measure α) =
        ∫ x, ⟪c, g x⟫_ℝ ∂(μ : Measure α) := by
      apply integral_congr_ae
      filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ c) g] with x hx
      simpa [innerSL] using hx
    _ = ⟪c, ∫ x, g x ∂(μ : Measure α)⟫_ℝ := by
      exact integral_inner ((Lp.memLp g).integrable (by norm_num)) c

private theorem norm_sq_eq_integral_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {μ : Measure α} (f : Lp F 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem integrable_norm_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure α} (f : Lp F 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  simpa only [real_inner_self_eq_norm_sq] using MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f f

/-- Parseval in `L²(μ; G)`: the squared norms of the components in an orthonormal basis add up
to the squared norm. -/
theorem sum_norm_sq_compLp_innerSL {μ : Measure α} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ G) (g : Lp G 2 μ) :
    ∑ k, ‖(innerSL ℝ (b k)).compLp g‖ ^ 2 = ‖g‖ ^ 2 := by
  rw [norm_sq_eq_integral_norm_sq g]
  rw [Finset.sum_congr rfl (fun k _ => norm_sq_eq_integral_norm_sq ((innerSL ℝ (b k)).compLp g))]
  rw [← integral_finsetSum _ (fun k _ => integrable_norm_sq _)]
  apply integral_congr_ae
  have hae : ∀ᵐ x ∂μ, ∀ k, ((innerSL ℝ (b k)).compLp g) x = ⟪b k, g x⟫ := by
    rw [ae_all_iff]
    intro k
    filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ (b k)) g] with x hx
    rw [hx, innerSL_apply_apply]
  filter_upwards [hae] with x hx
  simp only [hx]
  simpa only [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right (g x)

end FunctionalInequalities.L2
