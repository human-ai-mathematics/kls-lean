import FunctionalInequalities.Analysis.Newtonian.Kernel

/-!
# First derivatives, smoothness and measurability of the Newtonian kernel

For the source-normalized kernel `newtonianKernel n` of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12), in every
dimension `n ≥ 2`:

* `hasFDerivAt_newtonianKernel`: `DΓ(x) = (n ω_n)⁻¹ ‖x‖^(-n) ⟪x, ·⟫` at `x ≠ 0` ((2.13));
* `contDiffAt_newtonianKernel`: `Γ` is smooth of every order off the origin;
* `abs_fderiv_newtonianKernel_basis_le`: `|D_i Γ(x)| ≤ (n ω_n)⁻¹ ‖x‖^(1-n)` ((2.14));
* `abs_newtonianKernel_of_two_lt` (`n ≥ 3`): the exact absolute value of `Γ`;
* `measurable_newtonianKernel`, `measurable_fderiv_newtonianKernel_apply`: Borel measurability of
  `Γ` and of each first-derivative component, whatever their values at `0`.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Actual source-normalized first derivative (GT2001 (2.13)), including n=2. -/
theorem hasFDerivAt_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    HasFDerivAt (newtonianKernel n)
      (((1/((n:ℝ)*euclideanUnitBallVolume n))*‖x‖^(-(n:ℝ))) • innerSL ℝ x) x := by
  by_cases h2 : n=2
  · subst n
    rw [euclideanUnitBallVolume_two]
    change HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => (1/(2*Real.pi))*Real.log ‖y‖) _ x
    exact ((hasFDerivAt_log_norm_of_ne_zero x hx).const_mul (1/(2*Real.pi))).congr_fderiv
      (by rw [smul_smul];norm_num)
  · have h3 : 3 ≤ n := by omega
    have hN : (3:ℝ) ≤ n := by exact_mod_cast h3
    have hN0 : (n:ℝ) ≠ 0 := by linarith
    have hp0 : (2:ℝ)-n ≠ 0 := by linarith
    have hw := euclideanUnitBallVolume_pos n
    have he : newtonianKernel n = powerKernel n (euclideanUnitBallVolume n) := by
      funext y;simp only [newtonianKernel,if_neg h2]
    rw [he]
    have h := (hasFDerivAt_norm_rpow_of_ne_zero x ((2:ℝ)-n) hx).const_mul
      (1/((n:ℝ)*(2-n)*euclideanUnitBallVolume n))
    have hc : (1/((n:ℝ)*(2-n)*euclideanUnitBallVolume n))*(((2:ℝ)-n)*‖x‖^((2:ℝ)-n-2)) =
        (1/((n:ℝ)*euclideanUnitBallVolume n))*‖x‖^(-(n:ℝ)) := by
      rw [show (2:ℝ)-n-2 = -(n:ℝ) by ring]
      field_simp [hN0,hp0,hw.ne']
    exact h.congr_fderiv (by rw [smul_smul,hc])

/-- Smoothness of the actual scalar expression off the singularity. -/
theorem contDiffAt_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (newtonianKernel n) x := by
  by_cases h2 : n=2
  · subst n
    change ContDiffAt ℝ k (fun y : EuclideanSpace ℝ (Fin 2) => (1/(2*Real.pi))*Real.log ‖y‖) x
    exact contDiffAt_const.mul ((contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx))
  · have he : newtonianKernel n = powerKernel n (euclideanUnitBallVolume n) := by
      funext y;simp only [newtonianKernel,if_neg h2]
    rw [he]
    exact contDiffAt_const.mul ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx))

/-- Each actual first-derivative component is measurable, with no value
at the singular point assumed. -/
theorem measurable_fderiv_newtonianKernel_apply {n : ℕ} (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) : Measurable (fun x => fderiv ℝ (newtonianKernel n) x u) := by
  apply measurable_of_continuousOn_compl_singleton (0:EuclideanSpace ℝ (Fin n))
  intro x hx
  have hx0 : x ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hx
  have h := (contDiffAt_newtonianKernel hn x hx0 1).fderiv_right (m := 0) (by norm_num)
  exact (h.continuousAt.clm_apply continuousAt_const).continuousWithinAt

/-- Exact first-derivative entry bound in GT2001 (2.14). -/
theorem abs_fderiv_newtonianKernel_basis_le {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (i : Fin n) :
    |fderiv ℝ (newtonianKernel n) x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
      (1/((n:ℝ)*euclideanUnitBallVolume n))*‖x‖^((1:ℝ)-n) := by
  have hN : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hw := euclideanUnitBallVolume_pos n
  have hc : |⟪x,EuclideanSpace.basisFun (Fin n) ℝ i⟫| ≤ ‖x‖ := by
    simpa only [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i,mul_one] using
      abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin n) ℝ i)
  rw [(hasFDerivAt_newtonianKernel hn x hx).fderiv]
  change |((1/((n:ℝ)*euclideanUnitBallVolume n))*‖x‖^(-(n:ℝ)))*⟪x,EuclideanSpace.basisFun (Fin n) ℝ i⟫| ≤ _
  have hp : ‖x‖^(-(n:ℝ))*‖x‖ = ‖x‖^((1:ℝ)-n) := by
    calc
      _ = ‖x‖^(-(n:ℝ))*‖x‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = ‖x‖^(-(n:ℝ)+1) := (Real.rpow_add (norm_pos_iff.mpr hx) _ _).symm
      _ = _ := by congr 1;ring
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (1/((n:ℝ)*euclideanUnitBallVolume n))*‖x‖^(-(n:ℝ)))]
  calc
    _ ≤ ((1/((n:ℝ)*euclideanUnitBallVolume n))*‖x‖^(-(n:ℝ)))*‖x‖ := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [mul_assoc,hp]

/-- Absolute scalar kernel in dimensions n>2, including its chosen value at0. -/
theorem abs_newtonianKernel_of_two_lt {n : ℕ} (hn : 3 ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    |newtonianKernel n x| = (1/((n:ℝ)*((n:ℝ)-2)*euclideanUnitBallVolume n))*‖x‖^((2:ℝ)-n) := by
  have h2 : n ≠ 2 := by omega
  have hN3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (n:ℝ) := by linarith
  have hp : (2:ℝ)-n < 0 := by linarith
  have hw := euclideanUnitBallVolume_pos n
  simp only [newtonianKernel,if_neg h2,powerKernel,abs_mul,abs_div,abs_one,
    abs_of_pos hN,abs_of_neg hp,abs_of_pos hw,neg_sub,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) ((2:ℝ)-n))]


/-- Measurability of the actual scalar kernel, including its chosen finite
value at the singular point. -/
theorem measurable_newtonianKernel {n : ℕ} (hn : 2 ≤ n) : Measurable (newtonianKernel n) := by
  apply measurable_of_continuousOn_compl_singleton (0:EuclideanSpace ℝ (Fin n))
  intro x hx
  exact (contDiffAt_newtonianKernel hn x
    (by simpa only [mem_compl_iff,mem_singleton_iff] using hx) 0).continuousAt.continuousWithinAt

end FunctionalInequalities.Analysis
