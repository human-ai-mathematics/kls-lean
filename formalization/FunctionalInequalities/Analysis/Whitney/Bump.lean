import FunctionalInequalities.Analysis.Whitney.Cover
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Uniformly scaled bumps for the Whitney cover

A single fixed bump, equal to one on the radius-five ball and supported in the radius-eight
ball, is translated and scaled. Its derivatives are uniformly bounded by a constant divided
by the scale. This quantitative estimate is needed for the Whitney affine-jet sum.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis.WhitneyCover

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- One common smooth profile for all centers and scales. -/
def baseBump : ContDiffBump (0 : V) := ⟨5, 8, by norm_num, by norm_num⟩

/-- A translated bump at scale `r`. Its support claims require `0 < r`. -/
def bump (z : V) (r : ℝ) (y : V) : ℝ := (baseBump (V := V)) (r⁻¹ • (y - z))

theorem contDiff_bump (z : V) (r : ℝ) : ContDiff ℝ ∞ (bump z r) := by
  exact (baseBump (V := V)).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)

theorem bump_nonneg (z : V) (r : ℝ) (y : V) : 0 ≤ bump z r y :=
  (baseBump (V := V)).nonneg

theorem bump_le_one (z : V) (r : ℝ) (y : V) : bump z r y ≤ 1 :=
  (baseBump (V := V)).le_one

theorem bump_eq_one {z y : V} {r : ℝ} (hr : 0 < r) (hy : dist y z ≤ 5 * r) :
    bump z r y = 1 := by
  apply (baseBump (V := V)).one_of_mem_closedBall
  change dist (r⁻¹ • (y - z)) 0 ≤ 5
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
  rw [← div_eq_inv_mul, div_le_iff₀ hr, ← dist_eq_norm]
  exact hy

theorem bump_eq_zero {z y : V} {r : ℝ} (hr : 0 < r) (hy : 8 * r ≤ dist y z) :
    bump z r y = 0 := by
  apply (baseBump (V := V)).zero_of_le_dist
  change 8 ≤ dist (r⁻¹ • (y - z)) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
  rw [← div_eq_inv_mul, le_div_iff₀ hr, ← dist_eq_norm]
  exact hy

theorem tsupport_bump_subset (z : V) {r : ℝ} (hr : 0 < r) :
    tsupport (bump z r) ⊆ closedBall z (8 * r) := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra h
  have hz := bump_eq_zero hr (le_of_lt (not_le.1 h))
  exact hy hz

/-- The derivative of the common profile is bounded; scaling gives a single bound valid for
all centers, all positive radii and all evaluation points, including zero-dimensional spaces. -/
theorem exists_derivative_bound [FiniteDimensional ℝ V] :
    ∃ M : ℝ, 0 < M ∧ ∀ z : V, ∀ r : ℝ, 0 < r → ∀ y : V,
      ‖fderiv ℝ (bump z r) y‖ ≤ M / r := by
  have hb : ContDiff ℝ 1 ((baseBump (V := V)) : V → ℝ) := (baseBump (V := V)).contDiff
  obtain ⟨M, hM⟩ := ((baseBump (V := V)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z r hr y => ?_⟩
  have hlin : HasFDerivAt (fun y : V => r⁻¹ • (y - z))
      (r⁻¹ • ContinuousLinearMap.id ℝ V) y :=
    ((hasFDerivAt_id y).sub_const z).const_smul _
  have hd := (hb.differentiable one_ne_zero _).hasFDerivAt.comp y hlin
  change ‖fderiv ℝ (((baseBump (V := V)) : V → ℝ) ∘ (fun y => r⁻¹ • (y - z))) y‖ ≤ _
  rw [hd.fderiv]
  have hop : ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ ≤ r⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hr.le)).trans_eq
      (mul_one _)
  calc
    _ ≤ ‖fderiv ℝ ((baseBump (V := V)) : V → ℝ) (r⁻¹ • (y - z))‖ *
        ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max M 1 * r⁻¹ := mul_le_mul ((hM _).trans (le_max_left _ _)) hop
      (norm_nonneg _) (le_trans zero_le_one (le_max_right _ _))
    _ = max M 1 / r := (div_eq_mul_inv _ _).symm

end FunctionalInequalities.Analysis.WhitneyCover
