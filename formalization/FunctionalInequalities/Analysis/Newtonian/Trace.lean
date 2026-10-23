import FunctionalInequalities.Analysis.Newtonian.Kernel

/-!
# Trace of the Newtonian kernel Hessian

`sum_bilinear_newtonianKernel_basis_self_eq_zero`: for `n ≥ 2` and `x ≠ 0`, the diagonal entries of the
actual Hessian of the kernel `Γ` of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12)–(2.13), sum to zero. This is classical
harmonicity off the origin; no distributional identity at `0` is asserted.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The actual normalized Hessian has zero trace off the singularity.
This is off-origin harmonicity; no distributional identity is asserted. -/
theorem sum_bilinear_newtonianKernel_basis_self_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    (∑ i : Fin n, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i))=0 := by
  have hii (i : Fin n) : ⟪EuclideanSpace.basisFun (Fin n) ℝ i,EuclideanSpace.basisFun (Fin n) ℝ i⟫ = (1:ℝ) := by
    simp
  simp_rw [bilinear_newtonianKernel hn x _ _ hx,hii,EuclideanSpace.inner_basisFun_real,mul_one]
  rw [← Finset.mul_sum]
  have he : (∑ i : Fin n, (‖x‖^(-(n:ℝ))-(n:ℝ)*‖x‖^(-(n:ℝ)-2)*(x i)*(x i))) =
      (n:ℝ)*‖x‖^(-(n:ℝ))-(n:ℝ)*‖x‖^(-(n:ℝ)-2)*(∑ i : Fin n,(x i)^2) := by
    simp_rw [show ∀ i : Fin n, (n:ℝ)*‖x‖^(-(n:ℝ)-2)*(x i)*(x i) =
      ((n:ℝ)*‖x‖^(-(n:ℝ)-2))*(x i)^2 by intro i;ring]
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]
  rw [he,← EuclideanSpace.real_norm_sq_eq x]
  have hpow : ‖x‖^(-(n:ℝ)-2)*‖x‖^2=‖x‖^(-(n:ℝ)) := by
    rw [← Real.rpow_two,← Real.rpow_add (norm_pos_iff.mpr hx)]
    congr 1
    ring
  rw [mul_assoc,hpow,sub_self,mul_zero]

end FunctionalInequalities.Analysis
