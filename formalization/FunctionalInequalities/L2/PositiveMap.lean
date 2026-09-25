import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.Instances.Rat

/-!
# Quadratic inequalities under positive maps on L2

A positive real linear map preserves pointwise positive semidefinite two-by-two
matrices. Rational quadratic tests provide one common full-measure set; continuity
then supplies all real tests. Neither continuity nor preservation of constants is
required of the linear map.
-/
noncomputable section
open MeasureTheory Filter Topology
namespace FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem quadratic_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : b ^ 2 ≤ a * c) (q : ℝ) : 0 ≤ q ^ 2 * a - 2 * q * b + c := by
  by_cases ha0 : a = 0
  · have hb : b = 0 := by nlinarith [sq_nonneg b]
    simp [ha0, hb, hc]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hp : 0 ≤ a * (q ^ 2 * a - 2 * q * b + c) := by
      nlinarith [sq_nonneg (a * q - b)]
    exact nonneg_of_mul_nonneg_right hp ha'

private theorem coeFn_quadratic (a b c : Lp ℝ 2 μ) (q : ℝ) :
    ∀ᵐ x ∂μ, (q ^ 2 • a - (2 * q) • b + c : Lp ℝ 2 μ) x =
      q ^ 2 * a x - 2 * q * b x + c x := by
  filter_upwards [Lp.coeFn_add (q ^ 2 • a - (2 * q) • b) c,
    Lp.coeFn_sub (q ^ 2 • a) ((2 * q) • b),
    Lp.coeFn_smul (q ^ 2) a, Lp.coeFn_smul (2 * q) b] with x h₁ h₂ h₃ h₄
  simp only [h₁, Pi.add_apply, h₂, Pi.sub_apply, h₃, h₄, Pi.smul_apply, smul_eq_mul]

/-- A positive linear map on real L2 preserves the pointwise Cauchy-Schwarz
inequality for a positive semidefinite two-by-two matrix of L2 entries. -/
theorem ae_sq_le_mul_of_positive (P : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ)
    (hP : ∀ f, 0 ≤ f → 0 ≤ P f) (a b c : Lp ℝ 2 μ)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hc : ∀ᵐ x ∂μ, 0 ≤ c x)
    (h : ∀ᵐ x ∂μ, b x ^ 2 ≤ a x * c x) :
    ∀ᵐ x ∂μ, (P b) x ^ 2 ≤ (P a) x * (P c) x := by
  have hq (q : ℚ) : ∀ᵐ x ∂μ,
      (q : ℝ) ^ 2 * (P a) x - 2 * q * (P b) x + (P c) x ≥ 0 := by
    have hi : 0 ≤ ((q : ℝ) ^ 2 • a - (2 * (q : ℝ)) • b + c) := by
      apply (Lp.coeFn_nonneg _).mp
      filter_upwards [ha, hc, h, coeFn_quadratic a b c q] with x ha hc h he
      rw [he]
      exact quadratic_nonneg ha hc h q
    have ho := (Lp.coeFn_nonneg _).mpr (hP _ hi)
    simp only [map_add, map_sub, map_smul] at ho
    filter_upwards [ho, coeFn_quadratic (P a) (P b) (P c) q] with x hx he
    rwa [he] at hx
  filter_upwards [ae_all_iff.mpr hq] with x hx
  have hr (q : ℝ) : 0 ≤ q ^ 2 * (P a) x - 2 * q * (P b) x + (P c) x :=
    Rat.denseRange_cast.induction_on q (isClosed_le continuous_const (by fun_prop)) hx
  have hd := discrim_le_zero (a := (P a) x) (b := -2 * (P b) x) (c := (P c) x)
    (fun q ↦ by nlinarith [hr q])
  dsimp [discrim] at hd
  nlinarith

end FunctionalInequalities.L2
