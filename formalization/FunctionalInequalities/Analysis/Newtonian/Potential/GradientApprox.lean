module

public import FunctionalInequalities.Analysis.Newtonian.Truncation.GradientBounds
public import FunctionalInequalities.Analysis.Newtonian.Potential.Basic
public import FunctionalInequalities.Analysis.Newtonian.HessianIntegral.NearExponent
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Approximation of the Newtonian gradient by cut-off kernels (GT Lemma 4.2, first step)

The approximation step of the proof of Lemma 4.2 of Gilbarg–Trudinger, *Elliptic Partial
Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 55–56, with the cut-off first
derivative `v_{ε,i}(x) = ∫_Ω χ_ε(|x - y|) D_iΓ(x - y) f(y) dy` (`newtonianGradientApprox`):

* `setIntegral_ball_comp_sub`, `hasFDerivAt_setIntegral_comp_sub_mul`: translation of ball integrals
  and
  differentiation under the integral sign for a `C¹` kernel against a bounded density;
* `hasFDerivAt_newtonianGradientApprox`: the approximants are `C¹`, with derivative under the
  integral;
* `abs_newtonianGradientApprox_sub_le`: `|v_{ε,i}(x) - ∫_Ω D_iΓ(x - y) f(y) dy| ≤ max M 0 · 2ε`;
* `newtonianTruncatedGradient_near_error`: the near cancellation error (p. 56) with the constant
  `(n/α + 2B) H (2ε)^α`, where `B = newtonianCutoffCap` is the derived profile cap (GT's profile
  bound
  `2` is not claimed);
* `newtonianGradientApprox_deriv_eq_test`: the compact-test representation of `D_j v_{ε,i}`, exact
  for
  small `ε`, obtained by integration by parts.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section Translation

variable {n : ℕ}

/-- `∫_{B(x,R)} h(x − y) dy = ∫_{B(0,R)} h`. -/
theorem setIntegral_ball_comp_sub (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    (∫ y in ball x R, h (x - y)) = ∫ z in ball 0 R, h z := by
  have heq :
    (fun y => (ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator h (x - y)) =
      (ball x R).indicator (fun y => h (x - y)) := by
    funext y
    by_cases hy : y ∈ ball x R
    · have hy' : x - y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) R := by
        rw [mem_ball, dist_zero_right, norm_sub_rev]; rwa [mem_ball, dist_eq_norm] at hy
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy]
    · have hy' : x - y ∉ ball (0 : EuclideanSpace ℝ (Fin n)) R := by
        rw [mem_ball, dist_zero_right, norm_sub_rev]; rwa [mem_ball, dist_eq_norm] at hy
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball, ← heq,
    integral_sub_left_eq_self (fun z => (ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator h z)
      volume x]

end Translation

section Differentiation

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}

end Differentiation

/-- GT2001 p. 55: `v_{ε,i}(x) = ∫_Ω χ_ε(|x − y|) D_iΓ(x − y) f(y) dy`. -/
def newtonianGradientApprox (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (eps : ℝ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  ∫ y in Ω, newtonianTruncatedGradientComponent n eps i (x - y) * f y

section Approx

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} {M eps : ℝ}

/--
The approximants are `C¹` with the derivative under the integral sign, and every component is the
scalar integral. -/
theorem hasFDerivAt_newtonianGradientApprox (hn : 2 ≤ n) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hf : AEMeasurable f (volume.restrict Ω))
    (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M) (heps : 0 < eps) (i : Fin n) :
    (∀ x,
        HasFDerivAt (newtonianGradientApprox n Ω f eps i)
          (∫ y in Ω, f y • fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)) x) ∧
      Continuous
          (fun x =>
            ∫ y in Ω, f y • fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)) ∧
        ∀ x v,
          (∫ y in Ω, f y • fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)) v =
            ∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) v * f y := by
  have hT : ContDiff ℝ 1 (newtonianTruncatedGradientComponent n eps i) :=
    (contDiff_newtonianTruncatedGradientComponent hn heps i).of_le
      (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨hd, hi, hc⟩ := hasFDerivAt_setIntegral_comp_sub_mul hT hΩm hΩb hf hM
  refine ⟨hd, hc, fun x v => ?_⟩
  rw [ContinuousLinearMap.integral_apply (hi x) v]
  simp only [smul_apply, smul_eq_mul, mul_comm]

/--
`|v_{ε,i}(x) − ∫_Ω D_iΓ(x−y) f(y) dy| ≤ max M 0 · 2ε` at every `x` (the cut-off error lives on
`B(0,2ε)`). -/
theorem abs_newtonianGradientApprox_sub_le (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hf : AEMeasurable f (volume.restrict Ω)) (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M)
    (heps : 0 < eps) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    |newtonianGradientApprox n Ω f eps i x -
          ∫ y in Ω,
            fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * f y| ≤
      max M 0 * (2 * eps) := by
  set M' := max M 0
  have hM' : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M' :=
    hM.mono fun _ h => h.trans (le_max_left _ _)
  set D : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
  set E : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    newtonianTruncatedGradientComponent n eps i z - D z
  obtain ⟨hDi, hDb⟩ :=
    integrableOn_fderiv_newtonianKernel_ball hn (by positivity : 0 < 2 * eps) i
  have hEle :
    ∀ z, |E z| ≤ (ball (0 : EuclideanSpace ℝ (Fin n)) (2 * eps)).indicator (fun z => |D z|) z := by
    intro z
    by_cases hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (2 * eps)
    · rw [Set.indicator_of_mem hz]
      simp only [E, D, newtonianTruncatedGradientComponent]
      rw [show
          newtonianCutoffProfile eps ‖z‖ *
                fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i) -
              fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i) =
            (newtonianCutoffProfile eps ‖z‖ - 1) *
              fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
          by ring,
        abs_mul]
      have h1 : |newtonianCutoffProfile eps ‖z‖ - 1| ≤ 1 := by
        rw [abs_le];
        constructor <;>
          linarith [newtonianCutoffProfile_nonneg (eps := eps) ‖z‖,
            newtonianCutoffProfile_le_one (eps := eps) ‖z‖]
      exact mul_le_of_le_one_left (abs_nonneg _) h1
    · have hz' : 2 * eps ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz
      rw [Set.indicator_of_notMem hz]
      simp only [E, D, newtonianTruncatedGradientComponent_eq_of_far heps i hz', sub_self,
        abs_zero, le_refl]
  have hIi :
    Integrable ((ball (0 : EuclideanSpace ℝ (Fin n)) (2 * eps)).indicator (fun z => |D z|))
      volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hDi.abs
  have hEm : AEStronglyMeasurable E volume :=
    ((contDiff_newtonianTruncatedGradientComponent hn heps i).continuous.measurable.sub
        (measurable_fderiv_newtonianKernel_apply hn _)).aestronglyMeasurable
  have hE : Integrable E volume :=
    hIi.mono' hEm (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hEle z)
  have hEb : (∫ z, |E z|) ≤ 2 * eps := by
    calc
      (∫ z, |E z|) ≤
          ∫ z, (ball (0 : EuclideanSpace ℝ (Fin n)) (2 * eps)).indicator (fun z => |D z|) z :=
        integral_mono hE.abs hIi hEle
      _ = ∫ z in ball 0 (2 * eps), |D z| := integral_indicator measurableSet_ball
      _ ≤ 2 * eps := hDb
  have hEx : Integrable (fun y => E (x - y)) volume := hE.comp_sub_left x
  have hW := integrableOn_fderiv_newtonianKernel_sub_mul hn hΩb hf hM x i
  have hEf : Integrable (fun y => E (x - y) * f y) (volume.restrict Ω) :=
    hEx.integrableOn.mul_bdd hf.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM)
  have hA :
    Integrable (fun y => newtonianTruncatedGradientComponent n eps i (x - y) * f y)
      (volume.restrict Ω) :=
    (hW.add hEf).congr (ae_of_all _ fun y => by simp only [E, D, Pi.add_apply]; ring)
  have hdiff :
    newtonianGradientApprox n Ω f eps i x -
        (∫ y in Ω,
          fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * f y) =
      ∫ y in Ω, E (x - y) * f y := by
    unfold newtonianGradientApprox
    rw [← integral_sub hA hW]
    congr 1; funext y; simp only [E, D]; ring
  have hg : Integrable (fun y => M' * |E (x - y)|) volume := hEx.abs.const_mul M'
  rw [hdiff, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y in Ω, M' * |E (x - y)| := by
      refine norm_integral_le_of_norm_le hg.integrableOn ?_
      filter_upwards [hM'] with y hy
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    _ ≤ ∫ y, M' * |E (x - y)| := setIntegral_le_integral hg (ae_of_all _ fun y => by positivity)
    _ = M' * ∫ y, |E y| := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun z => |E z|) volume x]
    _ ≤ M' * (2 * eps) := mul_le_mul_of_nonneg_left hEb (le_max_right _ _)

end Approx

section NearError

variable {n : ℕ} {eps : ℝ}

private theorem volume_ball_le_euclideanUnitBallVolume (x : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) ≤
      ENNReal.ofReal (euclideanUnitBallVolume n * r ^ (n : ℝ)) := by
  rw [Measure.addHaar_ball_of_pos _ x hr, finrank_euclideanSpace_fin, Real.rpow_natCast]
  change
    ENNReal.ofReal (r ^ n) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≤
      ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal * r ^ n)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal measure_ball_lt_top.ne,
    mul_comm]

private theorem abs_rpow_neg_one_mul_inner_le (z u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    |‖z‖ ^ (-1:ℝ) * ⟪z, u⟫| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have h1 : |⟪z, u⟫| ≤ ‖z‖ := by simpa only [hu, mul_one] using abs_real_inner_le_norm z u
  by_cases hz : z = 0
  · subst z; simp
  · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc ‖z‖ ^ (-1:ℝ) * |⟪z, u⟫| ≤ ‖z‖ ^ (-1:ℝ) * ‖z‖ :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (norm_nonneg _) _)
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hp.ne']

/--
GT2001 p. 56 near cancellation, for any integrable bounded density `φ` that is `α`-Hölder AT `x` on
`B(x,2ε)`
(hence `φ(x) = 0`): both kernels are integrable against `φ`, and
`|∫ D_jG_{ε,i}(x−y)φ(y) − ∫ D_jD_iΓ(x−y)φ(y)| ≤ (n/α + 2B) H (2ε)^α`, `B = newtonianCutoffCap` (the
derived cap; the book's
profile bound `2` is NOT claimed). -/
theorem newtonianTruncatedGradient_near_error (hn : 2 ≤ n) (heps : 0 < eps) {α H : ℝ}
    (hα : 0 < α) (hαn : α < n) (hH : 0 ≤ H) (x : EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφi : Integrable φ volume)
    (hφH : ∀ y ∈ ball x (2 * eps), |φ y| ≤ H * ‖y - x‖ ^ α) (i j : Fin n) :
    Integrable
        (fun y =>
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
              (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) *
            φ y)
        volume ∧
      Integrable
          (fun y =>
            fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)
                (EuclideanSpace.basisFun (Fin n) ℝ j) *
              φ y)
          volume ∧
        |(∫ y,
                fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)
                    (EuclideanSpace.basisFun (Fin n) ℝ j) *
                  φ y) -
              ∫ y,
                bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
                    (EuclideanSpace.basisFun (Fin n) ℝ j)
                    (EuclideanSpace.basisFun (Fin n) ℝ i) *
                  φ y| ≤
          ((n : ℝ) / α + 2 * newtonianCutoffCap) * H * (2 * eps) ^ α := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set R := 2 * eps with hRdef
  have hR : 0 < R := by positivity
  set w0 := euclideanUnitBallVolume n
  have hw0 : 0 < w0 := euclideanUnitBallVolume_pos n
  set B := newtonianCutoffCap
  have hB : 0 < B := newtonianCutoffCap_pos
  set χ := newtonianCutoffProfile eps
  set k0 : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y) (b j) (b i)
  set D : EuclideanSpace ℝ (Fin n) → ℝ := fun z => fderiv ℝ (newtonianKernel n) z (b i)
  have hφx : φ x = 0 := by
    have h := hφH x (mem_ball_self hR)
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at h
    exact abs_nonpos_iff.mp h
  have hφH' : ∀ y ∈ ball x R, |φ y - φ x| ≤ H * ‖y - x‖ ^ α := by
    intro y hy;
    rw [hφx, sub_zero]; exact hφH y hy
  have hm : AEMeasurable φ (volume.restrict (ball x R)) :=
    hφi.aemeasurable.mono_measure Measure.restrict_le_self
  have hk0m : Measurable k0 :=
    (measurable_bilinear_newtonianKernel hn (b j) (b i)).comp
      (continuous_const.sub continuous_id).measurable
  have hχc : Continuous (fun y : EuclideanSpace ℝ (Fin n) => χ ‖x - y‖) :=
    (contDiff_newtonianCutoffProfile eps).continuous.comp
      (continuous_const.sub continuous_id).norm
  have hg :
    ∀ r : ℝ,
      0 < r →
        (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) ≤
          ENNReal.ofReal (w0 * r ^ (n : ℝ)) :=
    volume_ball_le_euclideanUnitBallVolume
      x
  -- (a) the plain Hessian kernel against φ

  have hnear :=
    newtonian_near_integrable_integral_le_of_exponent_lt_dim hn x hR hα hαn hH φ hm hφH' j i
  have hk0near : IntegrableOn (fun y => k0 y * φ y) (ball x R) volume := by
    simpa only [hφx, sub_zero] using hnear.1
  have hk0far : IntegrableOn (fun y => k0 y * φ y) (ball x R)ᶜ volume := by
    refine
      hφi.integrableOn.bdd_mul (c := (1 / w0) * R ^ (-(n : ℝ))) hk0m.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with y hy
    have hy' : R ≤ ‖x - y‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
    have hne : x - y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hy')
    rw [Real.norm_eq_abs]
    refine (abs_bilinear_newtonianKernel_basis_le hn (x - y) hne j i).trans ?_
    exact
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hR hy' (by simp)) (by positivity)
  have hk0 : Integrable (fun y => k0 y * φ y) volume := by
    have h := hk0near.union hk0far
    rwa [union_compl_self,
      integrableOn_univ] at h
  -- (b) the two cancellation pieces on `B(x,2ε)`

  set p1 : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (χ ‖x - y‖ - 1) * k0 y * φ y
  set p2 : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    deriv χ ‖x - y‖ * (‖x - y‖ ^ (-1 : ℝ) * ⟪x - y, b j⟫) * D (x - y) * φ y
  have hc1 :=
    cancelled_near_kernel_integrable_integral_le volume x hw0.le hR hα hαn
      (by positivity : 0 ≤ 1 / w0) hH hg (fun y => (χ ‖x - y‖ - 1) * k0 y) φ
      (((hχc.measurable.sub measurable_const).mul hk0m).aemeasurable.mul
        (hm.sub aemeasurable_const))
      (by
        intro y _ hy
        have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
        have hb := abs_bilinear_newtonianKernel_basis_le hn (x - y) hne j i
        rw [norm_sub_rev] at hb
        have h1 : |χ ‖x - y‖ - 1| ≤ 1 := by
          rw [abs_le];
          constructor <;>
            linarith [newtonianCutoffProfile_nonneg (eps := eps) ‖x - y‖,
              newtonianCutoffProfile_le_one (eps := eps) ‖x - y‖]
        rw [abs_mul]
        exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans hb)
      hφH'
  have hp1 : IntegrableOn p1 (ball x R) volume := by simpa only [p1, hφx, sub_zero] using hc1.1
  have hp1b : |∫ y in ball x R, p1 y| ≤ (n : ℝ) / α * H * R ^ α := by
    have h := hc1.2
    simp only [hφx, sub_zero] at h
    calc
      |∫ y in ball x R, p1 y| = |∫ y in ball x R, (χ ‖x - y‖ - 1) * k0 y * φ y| := rfl
      _ ≤ 1 / w0 * H * (w0 * n / α * R ^ α) := h
      _ = (n : ℝ) / α * H * R ^ α := by field_simp
  obtain ⟨hDi, hDb⟩ := integrableOn_fderiv_newtonianKernel_ball hn hR i
  have hDx : IntegrableOn (fun y => |D (x - y)|) (ball x R) volume :=
    integrableOn_ball_comp_sub hDi.abs x
  have hDxb : (∫ y in ball x R, |D (x - y)|) ≤ R := by
    rw [setIntegral_ball_comp_sub (fun z => |D z|) x R]; exact hDb
  have hp2le : ∀ y ∈ ball x R, ‖p2 y‖ ≤ B / eps * (H * R ^ α) * |D (x - y)| := by
    intro y hy
    have hyx : ‖y - x‖ < R := by rwa [mem_ball, dist_eq_norm] at hy
    have h1 := abs_deriv_newtonianCutoffProfile_le heps ‖x - y‖
    have h2 := abs_rpow_neg_one_mul_inner_le (x - y) (b j) (by simp [b])
    have h3 : |φ y| ≤ H * R ^ α :=
      (hφH y hy).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyx.le hα.le) hH)
    rw [Real.norm_eq_abs,
      show p2 y = deriv χ ‖x - y‖ * (‖x - y‖ ^ (-1 : ℝ) * ⟪x - y, b j⟫) * D (x - y) * φ y from
        rfl,
      abs_mul, abs_mul, abs_mul]
    calc
      |deriv χ ‖x - y‖| * |‖x - y‖ ^ (-1 : ℝ) * ⟪x - y, b j⟫| * |D (x - y)| * |φ y| ≤
          B / eps * 1 * |D (x - y)| * (H * R ^ α) := by
        gcongr
      _ = B / eps * (H * R ^ α) * |D (x - y)| := by ring
  have hp2m : AEStronglyMeasurable p2 (volume.restrict (ball x R)) := by
    have hdc : Continuous (deriv χ) :=
      (contDiff_newtonianCutoffProfile eps).continuous_deriv (by simp)
    have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) :=
      continuous_const.sub continuous_id
    refine
      (((hdc.comp hsub.norm).measurable.mul
                ((hsub.norm.measurable.pow_const (-1 : ℝ)).mul
                  (hsub.inner continuous_const).measurable)).mul
            ((measurable_fderiv_newtonianKernel_apply hn (b i)).comp
              hsub.measurable)).aestronglyMeasurable.mul
        hm.aestronglyMeasurable
  have hp2 : IntegrableOn p2 (ball x R) volume :=
    (hDx.const_mul (B / eps * (H * R ^ α))).mono' hp2m
      ((ae_restrict_mem measurableSet_ball).mono fun y hy => hp2le y hy)
  have hp2b : |∫ y in ball x R, p2 y| ≤ 2 * B * H * R ^ α := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ y in ball x R, p2 y‖ ≤ ∫ y in ball x R, B / eps * (H * R ^ α) * |D (x - y)| :=
        norm_integral_le_of_norm_le (hDx.const_mul _)
          ((ae_restrict_mem measurableSet_ball).mono fun y hy => hp2le y hy)
      _ = B / eps * (H * R ^ α) * ∫ y in ball x R, |D (x - y)| := integral_const_mul _ _
      _ ≤ B / eps * (H * R ^ α) * R := mul_le_mul_of_nonneg_left hDxb (by positivity)
      _ = 2 * B * H * R ^ α := by
        rw [hRdef];
        field_simp
  -- (c) the cut-off kernel minus the Hessian kernel is the indicator of the pieces

  have hdiff :
    ∀ y,
      fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (b j) * φ y - k0 y * φ y =
        (ball x R).indicator (fun y => p1 y + p2 y) y := by
    intro y
    by_cases hyx : y = x
    · subst y
      rw [Set.indicator_of_mem (mem_ball_self hR)]
      simp only [p1, p2, hφx, mul_zero, sub_self, add_zero]
    by_cases hy : y ∈ ball x R
    · rw [Set.indicator_of_mem hy]
      have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
      rw [fderiv_newtonianTruncatedGradientComponent_apply hn i hne]
      simp only [p1, p2, D, k0, χ]
      ring
    · rw [Set.indicator_of_notMem hy]
      have hy' : R ≤ ‖x - y‖ := by
        simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
      have hne : x - y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR hy')
      rw [fderiv_newtonianTruncatedGradientComponent_apply hn i hne,
        deriv_newtonianCutoffProfile_eq_zero heps (Or.inr hy'),
        newtonianCutoffProfile_one heps hy']
      simp only [k0]
      ring
  have hind : Integrable ((ball x R).indicator (fun y => p1 y + p2 y)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr (hp1.add hp2)
  have hG :
    Integrable
      (fun y => fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (b j) * φ y)
      volume :=
    (hk0.add hind).congr (ae_of_all _ fun y => by rw [Pi.add_apply, ← hdiff y]; ring)
  refine ⟨hk0, hG, ?_⟩
  rw [← integral_sub hG hk0]
  simp_rw [hdiff]
  rw [integral_indicator measurableSet_ball, integral_add hp1 hp2]
  calc
    |(∫ y in ball x R, p1 y) + ∫ y in ball x R, p2 y| ≤
        |∫ y in ball x R, p1 y| + |∫ y in ball x R, p2 y| :=
      abs_add_le _ _
    _ ≤ (n : ℝ) / α * H * R ^ α + 2 * B * H * R ^ α := add_le_add hp1b hp2b
    _ = ((n : ℝ) / α + 2 * B) * H * R ^ α := by ring

end NearError

section TestRepresentation

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} {M eps : ℝ}

/--
The compact-test identity for the approximants (exact for small `ε`, no limit): if `θ ∈ C¹_c` equals
`1` on an open
`U ⊇ Ω` and `B(x,2ε) ⊆ Ω`, then with `F = 1_Ω f`,
`D_j v_{ε,i}(x) = ∫ D_jG_{ε,i}(x−y)(F(y) − f(x)θ(y))dy + f(x)∫ D_iΓ(x−y)D_jθ(y)dy`, all integrands
integrable.
Derived by compact integration by parts; the second integrand vanishes near `x`. -/
theorem newtonianGradientApprox_deriv_eq_test (hn : 2 ≤ n) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hfi : IntegrableOn f Ω volume) (heps : 0 < eps)
    {θ : EuclideanSpace ℝ (Fin n) → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hΩU : Ω ⊆ U) (hθ1 : ∀ y ∈ U, θ y = 1)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ball x (2 * eps) ⊆ Ω) (i j : Fin n) :
    Integrable
        (fun y =>
          fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)
              (EuclideanSpace.basisFun (Fin n) ℝ j) *
            (Ω.indicator f y - f x * θ y))
        volume ∧
      Integrable
          (fun y =>
            fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
              fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j))
          volume ∧
        (∫ y in Ω,
            fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)
                (EuclideanSpace.basisFun (Fin n) ℝ j) *
              f y) =
          (∫ y,
              fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)
                  (EuclideanSpace.basisFun (Fin n) ℝ j) *
                (Ω.indicator f y - f x * θ y)) +
            f x *
              ∫ y,
                fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                  fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set G := newtonianTruncatedGradientComponent n eps i
  have hG : ContDiff ℝ 1 G :=
    (contDiff_newtonianTruncatedGradientComponent hn heps i).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) :=
    continuous_const.sub continuous_id
  set DG : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ G (x - y) (b j)
  have hDGc : Continuous DG :=
    ((hG.continuous_fderiv one_ne_zero).comp hsub).clm_apply continuous_const
  set Dθ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ θ y (b j)
  have hDθc : Continuous Dθ := (hθ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDθs : HasCompactSupport Dθ := hθc.fderiv_apply ℝ (b j)
  set F := Ω.indicator f
  have hΩm : MeasurableSet Ω :=
    hΩo.measurableSet
  -- `D_jθ` vanishes on `B(x,2ε)`, where `G(x − ·) ≠ D_iΓ(x − ·)` may fail

  have hDθ0 : ∀ y ∈ ball x (2 * eps), Dθ y = 0 := by
    intro y hy
    have he : θ =ᶠ[𝓝 y] fun _ => 1 := by
      filter_upwards [hU.mem_nhds (hΩU (hx hy))] with z hz using hθ1 z hz
    simp only [Dθ, he.fderiv_eq, fderiv_const_apply, zero_apply]
  have hGD : ∀ y, G (x - y) * Dθ y = fderiv ℝ (newtonianKernel n) (x - y) (b i) * Dθ y := by
    intro y
    by_cases hy : y ∈ ball x (2 * eps)
    · simp only [hDθ0 y hy, mul_zero]
    · have hy' : 2 * eps ≤ ‖x - y‖ := by
        simpa only [mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
      rw [show G (x - y) = _ from newtonianTruncatedGradientComponent_eq_of_far heps i hy']
  -- integrability

  obtain ⟨C, hC⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hDGc.continuousOn
  have hDGf : Integrable (fun y => DG y * f y) (volume.restrict Ω) := by
    refine hfi.bdd_mul (c := C) hDGc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hΩm] with y hy using hC y (subset_closure hy)
  have hFeq : (fun y => DG y * F y) = Ω.indicator (fun y => DG y * f y) := by
    funext y; by_cases hy : y ∈ Ω
    · simp only [F, Set.indicator_of_mem hy]
    · simp only [F, Set.indicator_of_notMem hy, mul_zero]
  have hDGF : Integrable (fun y => DG y * F y) volume := by
    rw [hFeq];
    exact (integrable_indicator_iff hΩm).mpr hDGf
  have hDGθ : Integrable (fun y => DG y * θ y) volume :=
    (hDGc.mul hθ.continuous).integrable_of_hasCompactSupport hθc.mul_left
  have hGDθ : Integrable (fun y => G (x - y) * Dθ y) volume :=
    ((hG.continuous.comp hsub).mul hDθc).integrable_of_hasCompactSupport hDθs.mul_left
  have hT : Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (b i) * Dθ y) volume :=
    hGDθ.congr (ae_of_all _ hGD)
  have hDGφ : Integrable (fun y => DG y * (F y - f x * θ y)) volume :=
    (hDGF.sub (hDGθ.const_mul (f x))).congr
      (ae_of_all _ fun y => by simp only [Pi.sub_apply]; ring)
  refine
    ⟨hDGφ, hT, ?_⟩
  -- integration by parts: `∫ D_jG(x−y)θ(y) dy = ∫ G(x−y) D_jθ(y) dy`

  have hderiv : ∀ y, fderiv ℝ (fun y => G (x - y)) y (b j) = -DG y := by
    intro y
    have hs :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => x - y)
        (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
      (hasFDerivAt_id y).const_sub x
    have h : HasFDerivAt (fun y => G (x - y)) _ y :=
      ((hG.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp y hs
    rw [h.fderiv]
    simp [DG]
  have hIBP :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun y => G (x - y))
      (g := θ) (v := b j) (by simp only [hderiv, neg_mul]; exact hDGθ.neg) hGDθ
      ((hG.continuous.comp hsub).mul hθ.continuous |>.integrable_of_hasCompactSupport
        hθc.mul_left)
      (fun y _ => ((hG.differentiable one_ne_zero).comp (differentiable_id.const_sub x)) y)
      (fun y _ => hθ.differentiable one_ne_zero y)
  have hIBP' : (∫ y, DG y * θ y) = ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (b i) * Dθ y := by
    have h : (∫ y, G (x - y) * Dθ y) = ∫ y, DG y * θ y := by
      simpa only [hderiv, neg_mul, integral_neg, neg_neg] using hIBP
    rw [← h]; exact integral_congr_ae (ae_of_all _ hGD)
  rw [← hIBP', ← integral_indicator hΩm, ← hFeq]
  have hsplit : (∫ y, DG y * F y) = (∫ y, DG y * (F y - f x * θ y)) + f x * ∫ y, DG y * θ y := by
    rw [← integral_const_mul, ← integral_add hDGφ (hDGθ.const_mul (f x))]
    congr 1; funext y; ring
  exact hsplit

end TestRepresentation

end FunctionalInequalities.Analysis
