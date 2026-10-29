import FunctionalInequalities.Analysis.Newtonian.Kernel.Difference

/-!
# Far-field differences of the Newtonian kernel Hessian

`newtonianKernel_shift_difference_le_of_far`: for `n ≥ 2`, `x ≠ z` and `2 ‖z - x‖ ≤ ‖y - x‖`,
`|D_ijΓ(x - y) - D_ijΓ(z - y)| ≤ (n + 5) / ω_n · 2^(n+1) ‖z - x‖ ‖y - x‖^(-n-1)`. This is the far-field
kernel estimate in the proof of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 57–59, with an explicit
dimensional constant derived from the third derivative and the mean value theorem.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

/-- Actual shifted Hessian difference outside twice the point separation.
The dimensional constant is derived from the third derivative and MVT. -/
theorem newtonianKernel_shift_difference_le_of_far {n : ℕ} (hn : 2 ≤ n)
    (x z y : EuclideanSpace ℝ (Fin n)) (hxz : x ≠ z)
    (hfar : 2*‖z-x‖ ≤ ‖y-x‖) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z-y)
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (((n:ℝ)+5)/euclideanUnitBallVolume n*2^((n:ℝ)+1))*‖z-x‖*‖y-x‖^(-(n:ℝ)-1) := by
  have hd : 0 < ‖z-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz.symm)
  have hr : 0 < ‖x-y‖ := by rw [norm_sub_rev];linarith
  have hba : (z-y)-(x-y) = z-x := by abel
  have hab : (x-y)-(z-y) = x-z := by abel
  have hclose : ‖(z-y)-(x-y)‖ ≤ ‖x-y‖/2 := by rw [hba,norm_sub_rev x y];linarith
  have h := newtonianKernel_entry_difference_le_of_close hn (x-y) (z-y)
    (norm_pos_iff.mp hr) hclose i j
  have hpow : (‖x-y‖/2)^(-(n:ℝ)-1) = 2^((n:ℝ)+1)*‖x-y‖^(-(n:ℝ)-1) := by
    rw [Real.div_rpow hr.le (by norm_num : 0 ≤ (2:ℝ)),div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
    have he : -(-(n:ℝ)-1) = (n:ℝ)+1 := by ring
    rw [he,mul_comm]
  rw [hpow,hab,norm_sub_rev x z,norm_sub_rev x y] at h
  calc
    _ ≤ (((n:ℝ)+5)/euclideanUnitBallVolume n*(2^((n:ℝ)+1)*‖y-x‖^(-(n:ℝ)-1)))*‖z-x‖ := h
    _ = _ := by ring

end FunctionalInequalities.Analysis
