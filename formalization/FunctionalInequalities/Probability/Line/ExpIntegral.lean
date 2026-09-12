import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of exponential functions of an affine argument

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, supporting calculus. Read
`integral_exp_affine`, `integral_exp_affine_Ioi` and `integral_exp_affine_Iic`.

The chord and tangent bounds of a log-concave density are exponentials `C · exp (κ (s - x₀))`.
This module records their interval integrals and, for the decaying direction, their half-line
integrals with integrability, so that mass bounds of log-concave laws reduce to one-line
computations.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace FunctionalInequalities.Probability.Line

/-- The antiderivative of `C · exp (κ (s - x₀))`. -/
theorem hasDerivAt_exp_affine {κ : ℝ} (hκ : κ ≠ 0) (C x₀ s : ℝ) :
    HasDerivAt (fun t ↦ C / κ * Real.exp (κ * (t - x₀))) (C * Real.exp (κ * (s - x₀))) s := by
  have h : HasDerivAt (fun t ↦ κ * (t - x₀)) κ s := by
    simpa using ((hasDerivAt_id s).sub_const x₀).const_mul κ
  have h2 := (h.exp).const_mul (C / κ)
  refine h2.congr_deriv ?_
  field_simp

/-- The interval integral of an exponential of an affine argument. -/
theorem integral_exp_affine (C κ x₀ u v : ℝ) (hκ : κ ≠ 0) :
    ∫ s in u..v, C * Real.exp (κ * (s - x₀)) =
      C / κ * (Real.exp (κ * (v - x₀)) - Real.exp (κ * (u - x₀))) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hasDerivAt_exp_affine hκ C x₀ s)
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _)]
  ring

/-- A decaying exponential is integrable on a right half-line. -/
theorem integrableOn_exp_affine_Ioi {C κ : ℝ} (hC : 0 ≤ C) (hκ : κ < 0) (x₀ y : ℝ) :
    IntegrableOn (fun s ↦ C * Real.exp (κ * (s - x₀))) (Ioi y) := by
  have hκ' : κ ≠ 0 := hκ.ne
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t ↦ C / κ * Real.exp (κ * (t - x₀)))
    (l := 0) ?_ (fun s _ ↦ hasDerivAt_exp_affine hκ' C x₀ s) (fun s _ ↦ ?_) ?_
  · exact (hasDerivAt_exp_affine hκ' C x₀ y).continuousAt.continuousWithinAt
  · exact mul_nonneg hC (Real.exp_pos _).le
  · have h : Tendsto (fun t : ℝ ↦ κ * (t - x₀)) atTop atBot := by
      have : Tendsto (fun t : ℝ ↦ t - x₀) atTop atTop :=
        tendsto_atTop_add_const_right _ (-x₀) tendsto_id
      exact Tendsto.const_mul_atTop_of_neg hκ this
    have := (Real.tendsto_exp_atBot.comp h).const_mul (C / κ)
    simpa using this

/-- The right half-line integral of a decaying exponential. -/
theorem integral_exp_affine_Ioi {C κ : ℝ} (hC : 0 ≤ C) (hκ : κ < 0) (x₀ y : ℝ) :
    ∫ s in Ioi y, C * Real.exp (κ * (s - x₀)) = -(C / κ) * Real.exp (κ * (y - x₀)) := by
  have hκ' : κ ≠ 0 := hκ.ne
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t ↦ C / κ * Real.exp (κ * (t - x₀)))
    (m := 0) (hasDerivAt_exp_affine hκ' C x₀ y).continuousAt.continuousWithinAt
    (fun s _ ↦ hasDerivAt_exp_affine hκ' C x₀ s) (integrableOn_exp_affine_Ioi hC hκ x₀ y) ?_]
  · ring
  · have h : Tendsto (fun t : ℝ ↦ κ * (t - x₀)) atTop atBot := by
      have : Tendsto (fun t : ℝ ↦ t - x₀) atTop atTop :=
        tendsto_atTop_add_const_right _ (-x₀) tendsto_id
      exact Tendsto.const_mul_atTop_of_neg hκ this
    have := (Real.tendsto_exp_atBot.comp h).const_mul (C / κ)
    simpa using this

/-- A growing exponential is integrable on a left half-line. -/
theorem integrableOn_exp_affine_Iic {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (x₀ y : ℝ) :
    IntegrableOn (fun s ↦ C * Real.exp (κ * (s - x₀))) (Iic y) := by
  have hκ' : κ ≠ 0 := hκ.ne'
  have hint : IntegrableOn (fun s ↦ C * Real.exp (-κ * (s - -x₀))) (Ioi (-y)) :=
    integrableOn_exp_affine_Ioi hC (neg_neg_iff_pos.mpr hκ) (-x₀) (-y)
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  have := hint.comp_neg
  rw [neg_Ioi, neg_neg] at this
  refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Iio
  simp only
  congr 2
  ring

/-- The left half-line integral of a growing exponential. -/
theorem integral_exp_affine_Iic {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (x₀ y : ℝ) :
    ∫ s in Iic y, C * Real.exp (κ * (s - x₀)) = C / κ * Real.exp (κ * (y - x₀)) := by
  have hκ' : κ ≠ 0 := hκ.ne'
  rw [integral_Iic_of_hasDerivAt_of_tendsto (f := fun t ↦ C / κ * Real.exp (κ * (t - x₀)))
    (m := 0) (hasDerivAt_exp_affine hκ' C x₀ y).continuousAt.continuousWithinAt
    (fun s _ ↦ hasDerivAt_exp_affine hκ' C x₀ s) (integrableOn_exp_affine_Iic hC hκ x₀ y) ?_]
  · ring
  · have h : Tendsto (fun t : ℝ ↦ κ * (t - x₀)) atBot atBot := by
      have : Tendsto (fun t : ℝ ↦ t - x₀) atBot atBot :=
        tendsto_atBot_add_const_right _ (-x₀) tendsto_id
      exact Tendsto.const_mul_atBot hκ this
    have := (Real.tendsto_exp_atBot.comp h).const_mul (C / κ)
    simpa using this

end FunctionalInequalities.Probability.Line
