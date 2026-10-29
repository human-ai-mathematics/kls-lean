import FunctionalInequalities.Analysis.IteratedDerivative.QuotientLimit
import FunctionalInequalities.Analysis.Iteration.Absorption
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Audit: generic tools for the interior Schauder bootstrap

Real clients of `FunctionalInequalities/Analysis/IteratedDerivative/QuotientLimit.lean` and
`FunctionalInequalities/Analysis/Iteration/Absorption.lean` (support for Gilbarg–Trudinger, Classics
2001, Theorems 4.6 and 6.2).

* `contDiffOn_two_of_hessian_limit` is applied on the unit ball of `ℝ²` to the non-constant family
  `v m x = (1 + 1/(m+1)) ‖x‖²` with limit `g x = ‖x‖²`, Hessian bound `K = 4` and Hölder exponent
  `α = 1/2`; every hypothesis (C² regularity, uniform gradient convergence, Hessian bound and
  Hölder estimate) is derived, and the Hessians of the family differ from the limit Hessian.
* `exists_absorption_constant` is applied with `θ = 1/2`, `k = 1`, `R₀ = 1`, the non-constant
  function `A r = r` and nonzero `B = C = 1`; the recursion is verified.
-/

noncomputable section
open Filter Topology Metric
open scoped RealInnerProductSpace
namespace SchauderToolsAudit
open FunctionalInequalities.Analysis

/-- The plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Scaling coefficients `1 + 1/(m+1) → 1`. -/
def coeff (m : ℕ) : ℝ := 1 + 1 / ((m : ℝ) + 1)

/-- The approximating family `v m x = (1 + 1/(m+1)) ‖x‖²`. -/
def v (m : ℕ) : E2 → ℝ := fun x => coeff m * ‖x‖ ^ 2

/-- The limit `g x = ‖x‖²`. -/
def g : E2 → ℝ := fun x => ‖x‖ ^ 2

/-- The constant Hessian `2 c ⟪·, ·⟫` of `c ‖x‖²`. -/
def hessianOf (c : ℝ) : E2 →L[ℝ] E2 →L[ℝ] ℝ := (2 * c) • innerSL ℝ

theorem hessianOf_apply_apply (c : ℝ) (x y : E2) : hessianOf c x y = 2 * c * ⟪x, y⟫ := by
  change (2 * c) * (innerSL ℝ x y) = _
  rw [innerSL_apply_apply]

theorem hasFDerivAt_scaled_sq (c : ℝ) (x : E2) :
    HasFDerivAt (fun y : E2 => c * ‖y‖ ^ 2) (hessianOf c x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul c
  have e : hessianOf c x = c • (2 • innerSL ℝ x) := by
    ext y
    rw [hessianOf_apply_apply]
    simp [innerSL_apply_apply]
    ring
  rw [e]; exact h

theorem fderiv_scaled_sq (c : ℝ) :
    fderiv ℝ (fun y : E2 => c * ‖y‖ ^ 2) = fun x => hessianOf c x :=
  funext fun x => (hasFDerivAt_scaled_sq c x).fderiv

theorem hessian_scaled_sq (c : ℝ) (x : E2) :
    fderiv ℝ (fderiv ℝ (fun y : E2 => c * ‖y‖ ^ 2)) x = hessianOf c := by
  rw [fderiv_scaled_sq]; exact (hessianOf c).fderiv

theorem g_eq : g = fun y : E2 => (1 : ℝ) * ‖y‖ ^ 2 := funext fun _ => (one_mul _).symm

theorem norm_hessianOf_apply_le (c : ℝ) (x : E2) : ‖hessianOf c x‖ ≤ 2 * |c| * ‖x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [hessianOf_apply_apply, Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
  have h := abs_real_inner_le_norm x y
  calc 2 * |c| * |⟪x, y⟫| ≤ 2 * |c| * (‖x‖ * ‖y‖) := by gcongr
    _ = 2 * |c| * ‖x‖ * ‖y‖ := by ring

theorem norm_hessianOf_le (c : ℝ) : ‖hessianOf c‖ ≤ 2 * |c| :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_hessianOf_apply_le c)

theorem coeff_nonneg (m : ℕ) : 0 ≤ coeff m := by unfold coeff; positivity

theorem coeff_le_two (m : ℕ) : coeff m ≤ 2 := by
  unfold coeff
  have : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  linarith

theorem hv (m : ℕ) : ContDiffOn ℝ 2 (v m) (ball (0 : E2) 1) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn

theorem hg : ContDiffOn ℝ 1 g (ball (0 : E2) 1) := (contDiff_norm_sq ℝ).contDiffOn

theorem hessian_v (m : ℕ) (x : E2) : fderiv ℝ (fderiv ℝ (v m)) x = hessianOf (coeff m) :=
  hessian_scaled_sq (coeff m) x

theorem hessian_g (x : E2) : fderiv ℝ (fderiv ℝ g) x = hessianOf 1 := by
  rw [g_eq]; exact hessian_scaled_sq 1 x

theorem hbound (m : ℕ) : ∀ x ∈ ball (0 : E2) 1, ‖fderiv ℝ (fderiv ℝ (v m)) x‖ ≤ 4 := by
  intro x _
  rw [hessian_v]
  refine (norm_hessianOf_le _).trans ?_
  rw [abs_of_nonneg (coeff_nonneg m)]
  linarith [coeff_le_two m]

theorem hhol (m : ℕ) : ∀ x ∈ ball (0 : E2) 1, ∀ y ∈ ball (0 : E2) 1,
    ‖fderiv ℝ (fderiv ℝ (v m)) x - fderiv ℝ (fderiv ℝ (v m)) y‖ ≤ 4 * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  intro x _ y _
  rw [hessian_v, hessian_v]
  have h0 : hessianOf (coeff m) - hessianOf (coeff m) = 0 :=
    sub_self (hessianOf (coeff m))
  rw [h0, ContinuousLinearMap.opNorm_zero]
  positivity

theorem hD : TendstoLocallyUniformlyOn (fun m => fderiv ℝ (v m)) (fderiv ℝ g) atTop
    (ball (0 : E2) 1) := by
  refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
  have hfv (m : ℕ) : fderiv ℝ (v m) = fun x => hessianOf (coeff m) x := fderiv_scaled_sq _
  have hfg : fderiv ℝ g = fun x => hessianOf 1 x := by rw [g_eq]; exact fderiv_scaled_sq 1
  simp only [hfv, hfg]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [hsmall] with m hm x hx
  have hx1 : ‖x‖ < 1 := by simpa using hx
  have hsub : hessianOf 1 x - hessianOf (coeff m) x = hessianOf (-(1 / ((m : ℝ) + 1))) x := by
    ext y
    simp only [sub_apply, hessianOf_apply_apply, coeff]
    ring
  calc dist (hessianOf 1 x) (hessianOf (coeff m) x)
      = ‖hessianOf 1 x - hessianOf (coeff m) x‖ :=
        dist_eq_norm (hessianOf 1 x) (hessianOf (coeff m) x)
    _ = ‖hessianOf (-(1 / ((m : ℝ) + 1))) x‖ := by rw [hsub]
    _ ≤ 2 * |-(1 / ((m : ℝ) + 1))| * ‖x‖ := norm_hessianOf_apply_le _ x
    _ ≤ 2 * (1 / ((m : ℝ) + 1)) * 1 := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
        gcongr
    _ < ε := by linarith

/-- The approximating Hessians are genuinely different from the limit Hessian. -/
theorem hessian_v_ne_g (m : ℕ) (x : E2) :
    fderiv ℝ (fderiv ℝ (v m)) x ≠ fderiv ℝ (fderiv ℝ g) x := by
  rw [hessian_v, hessian_g]
  intro h
  have e : hessianOf (coeff m) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) =
      hessianOf 1 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) := by rw [h]
  simp only [hessianOf_apply_apply, EuclideanSpace.inner_single_left, coeff] at e
  have hpos : 0 < 1 / ((m : ℝ) + 1) := by positivity
  simp at e
  linarith

/-- Client of `contDiffOn_two_of_hessian_limit`: the limit `‖x‖²` of the family is `C²` on the unit
ball with Hessian bound `4` and `1/2`-Hölder constant `4`. -/
theorem quotientLimit_client :
    ContDiffOn ℝ 2 g (ball (0 : E2) 1) ∧
      (∀ x ∈ ball (0 : E2) 1, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ 4) ∧
      ∀ x ∈ ball (0 : E2) 1, ∀ y ∈ ball (0 : E2) 1,
        ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ 4 * ‖x - y‖ ^ (1 / 2 : ℝ) :=
  contDiffOn_two_of_hessian_limit isOpen_ball g v 4 (by norm_num) hv hg hD hbound hhol

/-- Client of `exists_absorption_constant`: `θ = 1/2`, `k = 1`, `R₀ = 1`, `A r = r`, `B = C = 1`. -/
theorem absorption_client :
    ∃ c : ℝ, 0 < c ∧ ∀ r ∈ Set.Ioo (0 : ℝ) 1, r ≤ c * (1 / (1 - r) ^ (1 : ℝ) + 1) := by
  obtain ⟨c, hc, h⟩ := exists_absorption_constant (θ := 1 / 2) (by norm_num) (by norm_num)
    (k := 1) one_pos
  refine ⟨c, hc, fun r hr => h 1 one_pos (fun r => r) 1 1 zero_le_one zero_le_one
    (fun r hr => hr.1.le) ⟨1, fun r hr => hr.2⟩ ?_ r hr⟩
  intro r r' hr hrr' hr'
  rw [Real.rpow_one]
  have : 0 < 1 / (r' - r) := div_pos one_pos (by linarith)
  linarith

end SchauderToolsAudit

#print axioms SchauderToolsAudit.quotientLimit_client
#print axioms SchauderToolsAudit.hessian_v_ne_g
#print axioms SchauderToolsAudit.absorption_client
#print axioms FunctionalInequalities.Analysis.contDiffOn_two_of_hessian_limit
#print axioms FunctionalInequalities.Analysis.norm_sub_sub_le_of_holder_fderiv
#print axioms FunctionalInequalities.Analysis.exists_absorption_constant
#print axioms FunctionalInequalities.Analysis.absorption_le_chain
