import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# L2 sections and the two-factor variance bound

These measure-theoretic lemmas retain explicit L2/integrability hypotheses throughout.
They prove the law of total variance and the two-factor variance inequality for probability
measures, without smoothness or finite-dimensional assumptions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.ProductVariance

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : E × F → ℝ}

theorem memLp_right_ae (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ f (x, y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
    with x hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

theorem memLp_left_ae (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x ↦ f (x, y)) 2 μ := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hf.integrable_sq.prod_left_ae]
    with y hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

/-- Jensen's square inequality, with its necessary square-integrability hypothesis. -/
theorem sq_integral_le {g : E → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h0 := variance_nonneg g μ
  rw [variance_eq_sub hg] at h0
  simp only [Pi.pow_apply] at h0
  linarith

theorem memLp_integral_right (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x ↦ ∫ y, f (x, y) ∂ν) 2 μ := by
  have hsm : AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂ν) μ :=
    hf.aestronglyMeasurable.integral_prod_right'
  rw [memLp_two_iff_integrable_sq hsm]
  refine (hf.integrable_sq.integral_prod_left).mono'
    ((hsm.aemeasurable.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [memLp_right_ae hf] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_integral_le hx

theorem memLp_integral_left (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y ↦ ∫ x, f (x, y) ∂μ) 2 ν := by
  have hsm : AEStronglyMeasurable (fun y ↦ ∫ x, f (x, y) ∂μ) ν :=
    hf.aestronglyMeasurable.prod_swap.integral_prod_right'
  rw [memLp_two_iff_integrable_sq hsm]
  refine (hf.integrable_sq.integral_prod_right).mono'
    ((hsm.aemeasurable.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [memLp_left_ae hf] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_integral_le hy

theorem integrable_variance_right (hf : MemLp f 2 (μ.prod ν)) :
    Integrable (fun x ↦ variance (fun y ↦ f (x, y)) ν) μ := by
  refine ((hf.integrable_sq.integral_prod_left).sub
    (memLp_integral_right hf).integrable_sq).congr ?_
  filter_upwards [memLp_right_ae hf] with x hx
  rw [variance_eq_sub hx]
  simp only [Pi.sub_apply, Pi.pow_apply]

theorem integrable_variance_left (hf : MemLp f 2 (μ.prod ν)) :
    Integrable (fun y ↦ variance (fun x ↦ f (x, y)) μ) ν := by
  refine ((hf.integrable_sq.integral_prod_right).sub
    (memLp_integral_left hf).integrable_sq).congr ?_
  filter_upwards [memLp_left_ae hf] with y hy
  rw [variance_eq_sub hy]
  simp only [Pi.sub_apply, Pi.pow_apply]

/-- The law of total variance written using ordinary iterated integrals. -/
theorem variance_decomposition (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
      variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by
  have hg : MemLp (fun x ↦ ∫ y, f (x, y) ∂ν) 2 μ := memLp_integral_right hf
  have h1 : Integrable (fun x ↦ ∫ y, f (x, y) ^ 2 ∂ν) μ := hf.integrable_sq.integral_prod_left
  have h2 : Integrable (fun x ↦ (∫ y, f (x, y) ∂ν) ^ 2) μ := hg.integrable_sq
  have hVar : (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ)
      = ∫ x, ((∫ y, f (x, y) ^ 2 ∂ν) - (∫ y, f (x, y) ∂ν) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards [memLp_right_ae hf] with x hx
    rw [variance_eq_sub hx]
    simp only [Pi.pow_apply]
  have hsq : (∫ p, f p ^ 2 ∂μ.prod ν) = ∫ x, ∫ y, f (x, y) ^ 2 ∂ν ∂μ :=
    integral_prod _ hf.integrable_sq
  have hmean : (∫ p, f p ∂μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
    integral_prod _ (hf.integrable one_le_two)
  rw [hVar, integral_sub h1 h2, variance_eq_sub hf, variance_eq_sub hg]
  simp only [Pi.pow_apply]
  rw [hsq, hmean]
  ring

/-- Averaging one coordinate cannot increase the average variance in the other coordinate. -/
theorem variance_integral_le (hf : MemLp f 2 (μ.prod ν)) :
    variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ ≤
      ∫ y, variance (fun x ↦ f (x, y)) μ ∂ν := by
  set m : F → ℝ := fun y ↦ ∫ x, f (x, y) ∂μ with hm
  have hmL2 : MemLp m 2 ν := memLp_integral_left hf
  have hh : MemLp (fun p : E × F ↦ f p - m p.2) 2 (μ.prod ν) := hf.sub (hmL2.comp_snd μ)
  have hgsm : AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂ν) μ :=
    hf.aestronglyMeasurable.integral_prod_right'
  have hstepA : variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ
      = variance (fun x ↦ ∫ y, (f (x, y) - m y) ∂ν) μ := by
    rw [← variance_sub_const hgsm (∫ y, m y ∂ν)]
    apply variance_congr
    filter_upwards [(hf.integrable one_le_two).prod_right_ae] with x hx
    show (∫ y, f (x, y) ∂ν) - (∫ y, m y ∂ν) = ∫ y, (f (x, y) - m y) ∂ν
    rw [integral_sub hx (hmL2.integrable one_le_two)]
  have hG : MemLp (fun x ↦ ∫ y, (f (x, y) - m y) ∂ν) 2 μ := memLp_integral_right hh
  have hstepB : variance (fun x ↦ ∫ y, (f (x, y) - m y) ∂ν) μ
      ≤ ∫ x, (∫ y, (f (x, y) - m y) ∂ν) ^ 2 ∂μ := by
    have := variance_le_expectation_sq hG.aestronglyMeasurable
    simpa only [Pi.pow_apply] using this
  have hstepC : (∫ x, (∫ y, (f (x, y) - m y) ∂ν) ^ 2 ∂μ)
      ≤ ∫ x, ∫ y, (f (x, y) - m y) ^ 2 ∂ν ∂μ := by
    refine integral_mono_ae hG.integrable_sq hh.integrable_sq.integral_prod_left ?_
    filter_upwards [memLp_right_ae hh] with x hx
    exact sq_integral_le hx
  have hstepD : (∫ x, ∫ y, (f (x, y) - m y) ^ 2 ∂ν ∂μ)
      = ∫ y, ∫ x, (f (x, y) - m y) ^ 2 ∂μ ∂ν :=
    integral_integral_swap hh.integrable_sq
  have hstepE : (∫ y, ∫ x, (f (x, y) - m y) ^ 2 ∂μ ∂ν)
      = ∫ y, variance (fun x ↦ f (x, y)) μ ∂ν := by
    apply integral_congr_ae
    filter_upwards [memLp_left_ae hf] with y hy
    rw [variance_eq_integral hy.aemeasurable]
  calc variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ
      = variance (fun x ↦ ∫ y, (f (x, y) - m y) ∂ν) μ := hstepA
    _ ≤ ∫ x, (∫ y, (f (x, y) - m y) ∂ν) ^ 2 ∂μ := hstepB
    _ ≤ ∫ x, ∫ y, (f (x, y) - m y) ^ 2 ∂ν ∂μ := hstepC
    _ = ∫ y, ∫ x, (f (x, y) - m y) ^ 2 ∂μ ∂ν := hstepD
    _ = ∫ y, variance (fun x ↦ f (x, y)) μ ∂ν := hstepE

/-- The nonlinear two-factor variance inequality, with coefficient one in each coordinate. -/
theorem variance_le (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) ≤
      (∫ y, variance (fun x ↦ f (x, y)) μ ∂ν) +
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) := by
  rw [variance_decomposition hf]
  have := variance_integral_le hf
  linarith

end FunctionalInequalities.ProductVariance
