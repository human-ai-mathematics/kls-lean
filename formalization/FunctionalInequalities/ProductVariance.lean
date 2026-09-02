import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# L2 sections and the two-factor variance bound

These measure-theoretic lemmas retain explicit L2/integrability hypotheses throughout.
They are draft statements awaiting human review and a separate proof phase.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.ProductVariance

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : E × F → ℝ}

theorem memLp_right_ae (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ f (x, y)) 2 ν := sorry

theorem memLp_left_ae (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂ν, MemLp (fun x ↦ f (x, y)) 2 μ := sorry

/-- Jensen's square inequality, with its necessary square-integrability hypothesis. -/
theorem sq_integral_le {g : E → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := sorry

theorem memLp_integral_right (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x ↦ ∫ y, f (x, y) ∂ν) 2 μ := sorry

theorem memLp_integral_left (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y ↦ ∫ x, f (x, y) ∂μ) 2 ν := sorry

theorem integrable_variance_right (hf : MemLp f 2 (μ.prod ν)) :
    Integrable (fun x ↦ variance (fun y ↦ f (x, y)) ν) μ := sorry

theorem integrable_variance_left (hf : MemLp f 2 (μ.prod ν)) :
    Integrable (fun y ↦ variance (fun x ↦ f (x, y)) μ) ν := sorry

/-- The law of total variance written using ordinary iterated integrals. -/
theorem variance_decomposition (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
      variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ := sorry

/-- Averaging one coordinate cannot increase the average variance in the other coordinate. -/
theorem variance_integral_le (hf : MemLp f 2 (μ.prod ν)) :
    variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ ≤
      ∫ y, variance (fun x ↦ f (x, y)) μ ∂ν := sorry

/-- The nonlinear two-factor variance inequality, with coefficient one in each coordinate. -/
theorem variance_le (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) ≤
      (∫ y, variance (fun x ↦ f (x, y)) μ ∂ν) +
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) := sorry

end FunctionalInequalities.ProductVariance
