import FunctionalInequalities.Analysis.Cutoff.Profile
import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere

/-!
# Audit: affine rescaling and inverse-Hessian positivity for Letwin Lemma A.4

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17). Actual clients, every hypothesis derived here, never a target
conclusion:

* rescaling (`deriv_comp_sub_div_and_deriv_deriv`): the actual function `exp` with the nontrivial shift `c = 1` and scale
  `R = 2` at `t = 3` (coefficients `2⁻¹ e` and `(2⁻¹)² e`); the total-derivative convention at `R = 0` for arbitrary `f`
  (both derivatives `0`); and the Lemma A.4 use with the adopted profile bound: `|(η((· − c)/R))″| ≤ (R⁻¹)² B`;
* positivity (`sum_inverseHessianEntry_mul_mul_nonneg`): the scaled Gaussian potential `δ/2 ‖y‖²` (`δ > 0`) on the genuine
  two-dimensional `EuclideanSpace ℝ (Fin 2)`, positive definite by the existing Hessian lemma; the coordinate form of the
  chain rule (`a_i = DW(x)(b_i)` for an arbitrary `W`); and the rank-zero boundary `EuclideanSpace ℝ (Fin 0)`.

Client bodies: Claude.
-/

open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace A4RescalingClient

/-- `exp((s − 1)/2)` at `t = 3`: first derivative `2⁻¹ e`, second `(2⁻¹)² e`. -/
theorem exp_shift_scale :
    deriv (fun s => Real.exp ((s - 1) / 2)) 3 = 2⁻¹ * Real.exp 1 ∧
      deriv (deriv (fun s => Real.exp ((s - 1) / 2))) 3 = (2⁻¹) ^ 2 * Real.exp 1 := by
  obtain ⟨h1, h2⟩ := deriv_comp_sub_div_and_deriv_deriv Real.exp 1 2 3
  rw [Real.deriv_exp] at h1
  rw [Real.deriv_exp, Real.deriv_exp] at h2
  have e : ((3 : ℝ) - 1) / 2 = 1 := by norm_num
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- `R = 0`: Lean's total-derivative convention makes both derivatives vanish, for every `f`. -/
theorem zero_scale (f : ℝ → ℝ) (c t : ℝ) :
    deriv (fun s => f ((s - c) / 0)) t = 0 ∧ deriv (deriv (fun s => f ((s - c) / 0))) t = 0 := by
  obtain ⟨h1, h2⟩ := deriv_comp_sub_div_and_deriv_deriv f c 0 t
  refine ⟨?_, ?_⟩
  · rw [h1]; simp
  · rw [h2]; simp

/-- The Lemma A.4 use: with the adopted profile bound `B`, `|(η((· − c)/R))″(t)| ≤ (R⁻¹)² B` for all `c`, `R`, `t`. -/
theorem profile_second_derivative_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c R t : ℝ,
      |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - (s - c) / R))) t| ≤ (R⁻¹) ^ 2 * B := by
  obtain ⟨B, hB, hbound⟩ := smoothTransition_two_sub_cutoff.2.2.2.2.2.2.2.2
  refine ⟨B, hB, fun c R t => ?_⟩
  rw [(deriv_comp_sub_div_and_deriv_deriv (fun s : ℝ => Real.smoothTransition (2 - s)) c R t).2, abs_mul,
    abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hbound _).2 (sq_nonneg _)

end A4RescalingClient

namespace A4PositivityClient

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E0 := EuclideanSpace ℝ (Fin 0)

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hessian_zero_fun (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun _ : E => (0 : ℝ)) x v v = 0 := by
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply contDiff_const x v v]
  simp

/-- The scaled Gaussian potential `δ/2 ‖y‖²` has positive definite Hessian `δ ‖v‖²` for `δ > 0`. -/
theorem gaussian_posDef {δ : ℝ} (hδ : 0 < δ) (x v : E)
    (hv : v ≠ 0) : 0 < bilinearIteratedFDerivTwo ℝ (fun y : E => (0 : ℝ) + δ / 2 * ‖y‖ ^ 2) x v v := by
  rw [bilinearIteratedFDerivTwo_add_quadratic contDiff_const δ x v, hessian_zero_fun, zero_add]
  exact mul_pos hδ (pow_pos (norm_pos_iff.mpr hv) 2)

theorem gaussian_contDiff (δ : ℝ) :
    ContDiff ℝ 2 (fun y : E => (0 : ℝ) + δ / 2 * ‖y‖ ^ 2) :=
  contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))

end InnerProduct

/-- Genuine positive-dimensional case, any positive scale: on `ℝ²` with the standard basis (rank 2). -/
theorem plane_quadratic_nonneg {δ : ℝ} (hδ : 0 < δ) (x : E2) (a : Fin (Module.finrank ℝ E2) → ℝ) :
    0 ≤ ∑ i, ∑ j, inverseHessianEntry (fun y : E2 => (0 : ℝ) + δ / 2 * ‖y‖ ^ 2) (stdOrthonormalBasis ℝ E2) x i j *
      a i * a j :=
  sum_inverseHessianEntry_mul_mul_nonneg _ (gaussian_contDiff δ) x (gaussian_posDef hδ x) a

/-- Coordinate form of the chain rule (`a_i = DW(x)(b_i)`), as consumed in `L(h ∘ W)`: the `Γ`-term is nonnegative. -/
theorem chain_rule_gamma_nonneg {δ : ℝ} (hδ : 0 < δ) (W : E2 → ℝ) (x : E2) :
    0 ≤ ∑ i, ∑ j, inverseHessianEntry (fun y : E2 => (0 : ℝ) + δ / 2 * ‖y‖ ^ 2) (stdOrthonormalBasis ℝ E2) x i j *
      fderiv ℝ W x (stdOrthonormalBasis ℝ E2 i) * fderiv ℝ W x (stdOrthonormalBasis ℝ E2 j) :=
  sum_inverseHessianEntry_mul_mul_nonneg _ (gaussian_contDiff δ) x (gaussian_posDef hδ x)
    (fun i => fderiv ℝ W x (stdOrthonormalBasis ℝ E2 i))

/-- The plane has rank 2 (so the previous clients are not the empty sum). -/
theorem plane_rank : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin

theorem subsingleton_E0 : Subsingleton E0 :=
  Module.finrank_zero_iff.mp (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 0))

/-- Rank-zero boundary: the zero potential on the zero space; positive definiteness is vacuous. -/
theorem rank_zero_quadratic_nonneg (x : E0) (a : Fin (Module.finrank ℝ E0) → ℝ) :
    0 ≤ ∑ i, ∑ j, inverseHessianEntry (fun _ : E0 => (0 : ℝ)) (stdOrthonormalBasis ℝ E0) x i j * a i * a j :=
  sum_inverseHessianEntry_mul_mul_nonneg _ contDiff_const x
    (fun v hv => (hv (@Subsingleton.elim _ subsingleton_E0 v 0)).elim) a

end A4PositivityClient

#print axioms deriv_comp_sub_div_and_deriv_deriv
#print axioms sum_inverseHessianEntry_mul_mul_nonneg
#print axioms A4RescalingClient.exp_shift_scale
#print axioms A4RescalingClient.zero_scale
#print axioms A4RescalingClient.profile_second_derivative_bound
#print axioms A4PositivityClient.hessian_zero_fun
#print axioms A4PositivityClient.gaussian_posDef
#print axioms A4PositivityClient.gaussian_contDiff
#print axioms A4PositivityClient.plane_quadratic_nonneg
#print axioms A4PositivityClient.chain_rule_gamma_nonneg
#print axioms A4PositivityClient.plane_rank
#print axioms A4PositivityClient.subsingleton_E0
#print axioms A4PositivityClient.rank_zero_quadratic_nonneg
