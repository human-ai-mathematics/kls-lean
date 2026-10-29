import FunctionalInequalities.Analysis.Newtonian.Kernel.FarDifference
import FunctionalInequalities.Analysis.Newtonian.BallGrowth.FarCancelledAE

/-!
# The far-field Newtonian Hessian difference integral

`newtonian_far_integrable_integral_le`: for `n ≥ 2`, `x ≠ z`, `0 < α < 1`, a measurable set `S` and `f`
a.e.-measurable on `S` with `|f y - f x| ≤ H ‖y - x‖^α` on `S`, the integrand
`(D_ijΓ(x - y) - D_ijΓ(z - y)) (f(y) - f(x))` is integrable on `S ∩ {‖y - x‖ ≥ 2 ‖z - x‖}` and its integral
is at most `(n + 5) 2^(n+1) H (n + 1 - α) / (1 - α) · (2 ‖z - x‖)^α` in absolute value. This is the far-field
step of Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), pp. 57–59, with a coarse explicit constant `C(n, α)`. No Hölder
control of `f` outside `S` is used.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Actual far Newtonian Hessian difference on an arbitrary measurable source
domain. The source need not supply Holder control outside that domain.
The explicit dimensional/exponent constant is a permissible coarse C(n,alpha)
for the far mechanism of GT2001 Lemma 4.4. -/
theorem newtonian_far_integrable_integral_le {n : ℕ} (hn : 2 ≤ n)
    (x z : EuclideanSpace ℝ (Fin n)) (hxz : x ≠ z) {alpha H : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hH : 0 ≤ H)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : MeasurableSet S)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : AEMeasurable f (volume.restrict S))
    (hf : ∀ y ∈ S, |f y-f x| ≤ H*‖y-x‖^alpha) (i j : Fin n) :
    IntegrableOn (fun y =>
      (bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z-y)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))*(f y-f x))
      (S ∩ {y | 2*‖z-x‖ ≤ ‖y-x‖}) volume ∧
    |∫ y in S ∩ {y | 2*‖z-x‖ ≤ ‖y-x‖},
      (bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z-y)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))*(f y-f x)| ≤
      ((n:ℝ)+5)*2^((n:ℝ)+1)*H*(((n:ℝ)+1-alpha)/(1-alpha))*(2*‖z-x‖)^alpha := by
  let N := (n:ℝ)
  let omega := euclideanUnitBallVolume n
  let delta := 2*‖z-x‖
  let A := (N+5)/omega*2^(N+1)
  let ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S
  let F : Set (EuclideanSpace ℝ (Fin n)) := {y | delta ≤ ‖y-x‖}
  let k₁ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  let k₂ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z-y)
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hd : 0 < delta := by dsimp [delta];exact mul_pos (by norm_num) (norm_pos_iff.mpr (sub_ne_zero.mpr hxz.symm))
  have hN : 0 < N := by dsimp [N];exact_mod_cast (by omega : 0 < n)
  have hw : 0 < omega := euclideanUnitBallVolume_pos n
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hF : MeasurableSet F := (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).measurableSet
  have hg (r : ℝ) (hr : 0 < r) : ν (ball x r) ≤ ENNReal.ofReal (omega*r^N) := by
    calc
      _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) := Measure.restrict_apply_le S _
      _ = _ := by
        rw [Measure.addHaar_ball_of_pos _ x hr,finrank_euclideanSpace_fin]
        dsimp only [N]
        rw [Real.rpow_natCast]
        change ENNReal.ofReal (r^n)*(volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) =
          ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal*r^n)
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal measure_ball_lt_top.ne,mul_comm]
  have hkm₁ : Measurable k₁ := (measurable_bilinear_newtonianKernel hn _ _).comp (continuous_const.sub continuous_id).measurable
  have hkm₂ : Measurable k₂ := (measurable_bilinear_newtonianKernel hn _ _).comp (continuous_const.sub continuous_id).measurable
  have hmf : AEMeasurable f (ν.restrict F) := hm.mono_measure Measure.restrict_le_self
  have hprod : AEMeasurable (fun y => (k₁ y-k₂ y)*(f y-f x)) (ν.restrict F) :=
    (hkm₁.sub hkm₂).aemeasurable.mul (hmf.sub aemeasurable_const)
  have hk : ∀ᵐ y ∂(ν.restrict F), |k₁ y-k₂ y| ≤ A*delta*‖y-x‖^(-N-1) := by
    filter_upwards [ae_restrict_mem hF] with y hy
    have h := newtonianKernel_shift_difference_le_of_far hn x z y hxz hy i j
    have hsmall : ‖z-x‖ ≤ delta := by dsimp [delta];nlinarith [norm_nonneg (z-x)]
    calc
      _ ≤ A*‖z-x‖*‖y-x‖^(-N-1) := h
      _ ≤ _ := by gcongr
  have hfae : ∀ᵐ y ∂(ν.restrict F), |f y-f x| ≤ H*‖y-x‖^alpha := by
    filter_upwards [ae_restrict_of_ae (ae_restrict_mem hS)] with y hy
    exact hf y hy
  have h := cancelled_far_kernel_integrable_integral_le_of_ae ν x hw.le hd ha ha1 hN hA hH hg
    k₁ k₂ f hprod hk hfae
  have hAomega : A*omega = (N+5)*2^(N+1) := by dsimp [A];field_simp [hw.ne']
  have hc : A*H*(omega*(N+1-alpha)/(1-alpha))*delta^alpha =
      (N+5)*2^(N+1)*H*((N+1-alpha)/(1-alpha))*delta^alpha := by
    calc
      _ = (A*omega)*H*((N+1-alpha)/(1-alpha))*delta^alpha := by ring
      _ = _ := by rw [hAomega]
  rw [hc] at h
  have hmeasure : ν.restrict F = (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S∩F) := by
    dsimp only [ν]
    rw [Measure.restrict_restrict hF,inter_comm F S]
  rcases h with ⟨hi,hb⟩
  constructor
  · change Integrable _ ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S∩F))
    rw [← hmeasure]
    exact hi
  · change |∫ y, (k₁ y-k₂ y)*(f y-f x) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (S∩F))| ≤ _
    rw [← hmeasure]
    exact hb

end FunctionalInequalities.Analysis
