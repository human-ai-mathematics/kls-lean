module

public import Mathlib.MeasureTheory.Function.L2Space

/-! # Bounded tests for the integral absolute value of an L2 function -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped RealInnerProductSpace
namespace FunctionalInequalities.L2
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The integral absolute value is attained by a bounded L2 sign test. -/
theorem exists_bounded_inner_eq_integral_abs (f : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ, (∀ᵐ x ∂μ, |g x| ≤ 1) ∧ ⟪f, g⟫ = ∫ x, |f x| ∂μ := by
  classical
  let g : X → ℝ := fun x => if 0 ≤ f x then 1 else -1
  have hg : Measurable g :=
    Measurable.ite (measurableSet_le measurable_const (Lp.stronglyMeasurable f).measurable)
      measurable_const measurable_const
  have hb : ∀ x, ‖g x‖ ≤ 1 := by intro x; dsimp [g]; split_ifs <;> norm_num
  have hL : MemLp g 2 μ := MemLp.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ hb)
  refine ⟨hL.toLp g, ?_, ?_⟩
  · filter_upwards [hL.coeFn_toLp] with x hx
    simpa [hx, Real.norm_eq_abs] using hb x
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hL.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
    dsimp [g]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]

/-- Pairing with an essentially bounded L2 function is controlled by the integral absolute value. -/
theorem inner_le_mul_integral_abs (f g : Lp ℝ 2 μ) {M : ℝ}
    (hg : ∀ᵐ x ∂μ, |g x| ≤ M) : ⟪f, g⟫ ≤ M * ∫ x, |f x| ∂μ := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae (L2.integrable_inner f g)
    (((Lp.memLp f).integrable one_le_two).abs.const_mul M)
  filter_upwards [hg] with x hx
  simp only [Real.inner_apply]
  calc
    f x * g x ≤ |f x * g x| := le_abs_self _
    _ = |f x| * |g x| := abs_mul _ _
    _ ≤ |f x| * M := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = M * |f x| := mul_comm _ _

/-- A scalar test bounded by one cannot exceed the integral absolute value. -/
theorem inner_le_integral_abs (f g : Lp ℝ 2 μ) (hg : ∀ᵐ x ∂μ, |g x| ≤ 1) :
    ⟪f, g⟫ ≤ ∫ x, |f x| ∂μ := by
  rw [L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner f g) ((Lp.memLp f).integrable one_le_two).abs
  filter_upwards [hg] with x hx
  simp only [Real.inner_apply]
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hx)

/-- Bounded L2 dual tests suffice to bound the integral absolute value. -/
theorem integral_abs_le_of_inner_le (f : Lp ℝ 2 μ) {C : ℝ}
    (h : ∀ g : Lp ℝ 2 μ, (∀ᵐ x ∂μ, |g x| ≤ 1) → ⟪f, g⟫ ≤ C) :
    (∫ x, |f x| ∂μ) ≤ C := by
  obtain ⟨g, hg, heq⟩ := exists_bounded_inner_eq_integral_abs f
  rw [← heq]
  exact h g hg
end FunctionalInequalities.L2
