import FunctionalInequalities.Analysis.Newtonian.Measurable
import FunctionalInequalities.Analysis.Newtonian.CancelledNearIntegral

/-!
# The near-field Newtonian Hessian integral

`newtonian_near_integrable_integral_le_of_exponent_lt_dim`: for `n ≥ 2`, `0 < α < n`, `R > 0` and `f`
a.e.-measurable on `B_R(x)` with `|f y - f x| ≤ H ‖y - x‖^α` there, each cancelled Hessian integrand
`D_ijΓ(x - y) (f(y) - f(x))` is integrable on `B_R(x)` and
`|∫_{B_R(x)} D_ijΓ(x - y) (f(y) - f(x)) dy| ≤ (n / α) H R^α`, the constant of the near-field estimate in
Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
2001 (ISBN 3-540-41160-7), pp. 57–59.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The actual near Newtonian Hessian integral, with the exact GT2001
n/alpha constant. Integrability is derived from local measurability and the
centered Hölder estimate, not postulated for the singular product. -/
theorem newtonian_near_integrable_integral_le_of_exponent_lt_dim {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {R alpha H : ℝ} (hR : 0 < R)
    (ha : 0 < alpha) (had : alpha < (n:ℝ)) (hH : 0 ≤ H)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : AEMeasurable f (volume.restrict (ball x R)))
    (hf : ∀ y ∈ ball x R, |f y-f x| ≤ H*‖y-x‖^alpha) (i j : Fin n) :
    IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)*(f y-f x))
      (ball x R) volume ∧
    |∫ y in ball x R, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)*(f y-f x)| ≤
      (n:ℝ)*H/alpha*R^alpha := by
  let omega := euclideanUnitBallVolume n
  let k : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hw : 0 < omega := euclideanUnitBallVolume_pos n
  have hg (r : ℝ) (hr : 0 < r) :
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) ≤
        ENNReal.ofReal (omega*r^(n:ℝ)) := by
    rw [Measure.addHaar_ball_of_pos _ x hr,finrank_euclideanSpace_fin,Real.rpow_natCast]
    change ENNReal.ofReal (r^n)*(volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≤
      ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal*r^n)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal measure_ball_lt_top.ne,mul_comm]
  have hk : ∀ y ∈ ball x R, y ≠ x → |k y| ≤ (1/omega)*‖y-x‖^(-(n:ℝ)) := by
    intro y _ hy
    have h := abs_bilinear_newtonianKernel_basis_le hn (x-y) (sub_ne_zero.mpr hy.symm) i j
    rw [norm_sub_rev] at h
    exact h
  have hkm : Measurable k := (measurable_bilinear_newtonianKernel hn
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)).comp
      (continuous_const.sub continuous_id).measurable
  have hprod : AEMeasurable (fun y => k y*(f y-f x)) (volume.restrict (ball x R)) :=
    hkm.aemeasurable.mul (hm.sub aemeasurable_const)
  have h := cancelled_near_kernel_integrable_integral_le volume x hw.le hR ha had
    (by positivity : 0 ≤ 1/omega) hH hg k f hprod hk hf
  have hc : (1/omega)*H*(omega*(n:ℝ)/alpha*R^alpha) = (n:ℝ)*H/alpha*R^alpha := by
    field_simp [hw.ne']
  simpa only [hc] using h

end FunctionalInequalities.Analysis
