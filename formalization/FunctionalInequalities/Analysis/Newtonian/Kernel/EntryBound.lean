import FunctionalInequalities.Analysis.Newtonian.Kernel.Radial.Hessian

/-!
# Entrywise Hessian bounds for the radial Newtonian kernel expressions

For the expressions of `Analysis/Newtonian/Kernel/Radial/Hessian.lean` and the standard basis of
`EuclideanSpace ℝ (Fin n)`, the second-derivative entries obey the bound (2.14) of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7):

* `abs_bilinear_powerKernel_basis_le` (`n ≥ 3`): `|D_ij powerKernel n omega x| ≤ omega⁻¹ ‖x‖^(-n)`;
* `abs_bilinear_logKernel_basis_le` (`n = 2`): `|D_ij logKernel x| ≤ π⁻¹ ‖x‖^(-2)`.

Pointwise bounds at `x ≠ 0` only.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem entry_model_bound {ι : Type*} [DecidableEq ι] (N : ℝ) (hN : 1 ≤ N)
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1) (i j : ι) :
    |(if i=j then (1:ℝ) else 0)-N*a i*a j| ≤ N := by
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    have hs := (sq_le_one_iff_abs_le_one (a i)).mpr (ha i)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (a i)]
  · rw [if_neg hij,zero_sub,abs_neg,abs_mul,abs_mul,abs_of_nonneg (by linarith : 0 ≤ N)]
    calc
      _ ≤ N*1*1 := by gcongr;exact ha i;exact ha j
      _ = N := by ring

private theorem coord_abs_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h := abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin n) ℝ i)
  simpa only [EuclideanSpace.inner_basisFun_real,
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i,mul_one] using h

/-- Exact Hessian-entry bound (2.14), with omega the explicit unit-ball
normalization parameter, for the actual higher-dimensional power expression. -/
theorem abs_bilinear_powerKernel_basis_le {n : ℕ} (hn : 3 ≤ n) {omega : ℝ}
    (hw : 0 < omega) (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (powerKernel n omega) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (1/omega)*‖x‖^(-(n:ℝ)) := by
  let r := ‖x‖
  let a : Fin n → ℝ := fun k => x k/r
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have ha (k : Fin n) : |a k| ≤ 1 := by
    dsimp only [a]
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr (coord_abs_le_norm x k)
  have hmod := entry_model_bound (n:ℝ) (by linarith) a ha i j
  have heij := orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j
  have hform : bilinearIteratedFDerivTwo ℝ (powerKernel n omega) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      ((1/((n:ℝ)*omega))*r^(-(n:ℝ)))*((if i=j then 1 else 0)-(n:ℝ)*a i*a j) := by
    rw [bilinear_powerKernel hn hw x _ _ hx,heij,
      EuclideanSpace.inner_basisFun_real,EuclideanSpace.inner_basisFun_real]
    dsimp only [a,r]
    rw [Real.rpow_sub hr,Real.rpow_two]
    field_simp [hr.ne',hn0,hw.ne']
    ring
  have hp : 0 ≤ (1/((n:ℝ)*omega))*r^(-(n:ℝ)) := by positivity
  rw [hform,abs_mul,abs_of_nonneg hp]
  calc
    _ ≤ ((1/((n:ℝ)*omega))*r^(-(n:ℝ)))*(n:ℝ) := mul_le_mul_of_nonneg_left hmod hp
    _ = _ := by dsimp only [r];field_simp [hn0,hw.ne']


/-- Exact planar Hessian-entry bound (2.14), with the actual pi normalization. -/
theorem abs_bilinear_logKernel_basis_le (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ≠ 0) (i j : Fin 2) :
    |bilinearIteratedFDerivTwo ℝ logKernel x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)| ≤
      (1/Real.pi)*‖x‖^(-2:ℝ) := by
  let r := ‖x‖
  let a : Fin 2 → ℝ := fun k => x k/r
  have hr : 0 < r := norm_pos_iff.mpr hx
  have ha (k : Fin 2) : |a k| ≤ 1 := by
    dsimp only [a]
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr (coord_abs_le_norm x k)
  have hmod := entry_model_bound 2 (by norm_num) a ha i j
  have heij := orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal i j
  have hform : bilinearIteratedFDerivTwo ℝ logKernel x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j) =
      ((1/(2*Real.pi))*r^(-2:ℝ))*((if i=j then 1 else 0)-2*a i*a j) := by
    rw [bilinear_logKernel x _ _ hx,heij,
      EuclideanSpace.inner_basisFun_real,EuclideanSpace.inner_basisFun_real]
    dsimp only [a,r]
    rw [show (-4:ℝ) = (-2:ℝ)-2 by norm_num,Real.rpow_sub hr,Real.rpow_two]
    field_simp [hr.ne',Real.pi_ne_zero]
    ring
  have hp : 0 ≤ (1/(2*Real.pi))*r^(-2:ℝ) := by positivity
  rw [hform,abs_mul,abs_of_nonneg hp]
  calc
    _ ≤ ((1/(2*Real.pi))*r^(-2:ℝ))*2 := mul_le_mul_of_nonneg_left hmod hp
    _ = _ := by dsimp only [r];ring

end FunctionalInequalities.Analysis
