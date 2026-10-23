import FunctionalInequalities.Analysis.Newtonian.ThirdBound
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differences of Newtonian kernel Hessian entries

Mean-value consequences of `norm_fderiv_newtonianKernel_entry_le`, for `n ≥ 2`:

* `newtonianKernel_entry_difference_le_of_segment_norm`: if every point of the segment `[a, b]` has norm
  at least `r > 0`, then `|D_ijΓ(a) - D_ijΓ(b)| ≤ (n + 5) / ω_n · r^(-n-1) ‖a - b‖`;
* `newtonianKernel_entry_difference_le_of_close`: the same with `r = ‖a‖/2` when `‖b - a‖ ≤ ‖a‖/2`.

This is the kernel estimate behind the far-field integrals in Lemma 4.4 of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
pp. 57–59.
-/

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The actual kernel-entry difference from its proved derivative bound.
Only geometric separation of the segment from zero is assumed. -/
theorem newtonianKernel_entry_difference_le_of_segment_norm {n : ℕ} (hn : 2 ≤ n)
    (a b : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hseg : ∀ z ∈ segment ℝ a b, r ≤ ‖z‖) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (newtonianKernel n) a
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) b
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (((n:ℝ)+5)/euclideanUnitBallVolume n*r^(-(n:ℝ)-1))*‖a-b‖ := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hw : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  have hN : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hdiff (z) (hz : z ∈ segment ℝ a b) : DifferentiableAt ℝ F z :=
    (contDiffAt_bilinear_newtonianKernel hn z _ _
      (norm_pos_iff.mp (hr.trans_le (hseg z hz))) 1).differentiableAt (by norm_num)
  have hbound (z) (hz : z ∈ segment ℝ a b) : ‖fderiv ℝ F z‖ ≤
      ((n:ℝ)+5)/euclideanUnitBallVolume n*r^(-(n:ℝ)-1) := by
    have h := norm_fderiv_newtonianKernel_entry_le hn z
      (norm_pos_iff.mp (hr.trans_le (hseg z hz))) i j
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hr (hseg z hz) (by linarith)) (by positivity))
  simpa only [Real.norm_eq_abs] using (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (right_mem_segment ℝ a b) (left_mem_segment ℝ a b)

/-- A concrete local difference estimate: closeness relative to the distance
from zero supplies the required segment separation by the reverse triangle inequality. -/
theorem newtonianKernel_entry_difference_le_of_close {n : ℕ} (hn : 2 ≤ n)
    (a b : EuclideanSpace ℝ (Fin n)) (ha : a ≠ 0) (hab : ‖b-a‖ ≤ ‖a‖/2) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (newtonianKernel n) a
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) b
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (((n:ℝ)+5)/euclideanUnitBallVolume n*(‖a‖/2)^(-(n:ℝ)-1))*‖a-b‖ := by
  have hr : 0 < ‖a‖/2 := by positivity
  apply newtonianKernel_entry_difference_le_of_segment_norm hn a b hr _ i j
  intro z hz
  have h1 := (norm_sub_le_of_mem_segment hz).trans hab
  have h2 := norm_sub_norm_le a z
  rw [norm_sub_rev] at h2
  linarith

end FunctionalInequalities.Analysis
