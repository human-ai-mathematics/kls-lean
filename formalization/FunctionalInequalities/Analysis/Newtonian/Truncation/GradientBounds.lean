import FunctionalInequalities.Analysis.Newtonian.Truncation.Gradient
import FunctionalInequalities.Analysis.Newtonian.Kernel.L1
import FunctionalInequalities.Analysis.Cutoff.RadialLipschitz

/-!
# Bounds for the truncated Newtonian gradient

Support for the proof of Lemma 4.2 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 55–56, about the cut-off first derivative
`newtonianTruncatedGradientComponent` (`χ_ε(|z|) D_iΓ(z)`, `χ_ε = newtonianCutoffProfile ε`):

* `newtonianCutoffCap`: the Lipschitz constant `B` of the profile chosen from
  `exists_lipschitz_radial_cutoff_cap` (derived, not claimed to equal any particular number), and
  `abs_deriv_newtonianCutoffProfile_le : |χ_ε'| ≤ B / ε`;
* profile positivity, monotonicity, and vanishing of `χ_ε'` on `r ≤ ε` and on `r ≥ 2ε`, endpoints
  included;
* the component vanishes near `0`, equals `D_iΓ` on `‖z‖ ≥ 2ε`, is dominated by `|D_iΓ|`, and has
  derivative `χ_ε'(|z|) |z|⁻¹ ⟪z,v⟫ D_iΓ + χ_ε(|z|) D²Γ(z)(v, e_i)` off `0`;
* the trace density `∑ᵢ D_i G_{ε,i}` equals the radial expression at every point (including `0`), is
  nonnegative and vanishes on `‖z‖ ≥ 2ε`.

The unit radial mass is imported (`integral_sum_fderiv_newtonianTruncatedGradientComponent`), not
re-proved.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The derived dimension-free profile cap: `s ↦ ρ(2 − s)` is `newtonianCutoffCap`-Lipschitz. -/
def newtonianCutoffCap : ℝ := Classical.choose exists_lipschitz_radial_cutoff_cap

theorem newtonianCutoffCap_pos : 0 < newtonianCutoffCap := (Classical.choose_spec exists_lipschitz_radial_cutoff_cap).1

section Profile

variable {eps : ℝ}

theorem newtonianCutoffProfile_nonneg (r : ℝ) : 0 ≤ newtonianCutoffProfile eps r :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem newtonianCutoffProfile_le_one (r : ℝ) : newtonianCutoffProfile eps r ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem monotone_newtonianCutoffProfile (heps : 0 < eps) : Monotone (newtonianCutoffProfile eps) := by
  intro r s hrs
  have h := FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff.2.1 (div_le_div_of_nonneg_right hrs heps.le)
  simp only [newtonianCutoffProfile]
  linarith

theorem deriv_newtonianCutoffProfile_nonneg (heps : 0 < eps) (r : ℝ) : 0 ≤ deriv (newtonianCutoffProfile eps) r :=
  (monotone_newtonianCutoffProfile heps).deriv_nonneg

theorem hasDerivAt_newtonianCutoffProfile (r : ℝ) :
    HasDerivAt (newtonianCutoffProfile eps) (deriv (newtonianCutoffProfile eps) r) r :=
  ((contDiff_newtonianCutoffProfile eps).differentiable (by simp) r).hasDerivAt

/-- The profile derivative vanishes on `r ≤ ε` and on `r ≥ 2ε`, endpoints included (one-sided uniqueness). -/
theorem deriv_newtonianCutoffProfile_eq_zero (heps : 0 < eps) {r : ℝ} (hr : r ≤ eps ∨ 2 * eps ≤ r) :
    deriv (newtonianCutoffProfile eps) r = 0 := by
  have hd := hasDerivAt_newtonianCutoffProfile (eps := eps) r
  rcases hr with hr | hr
  · have hc : HasDerivWithinAt (newtonianCutoffProfile eps) 0 (Iic r) r :=
      (hasDerivWithinAt_const r (Iic r) (0:ℝ)).congr (fun s hs => newtonianCutoffProfile_zero heps (le_trans hs hr))
        (newtonianCutoffProfile_zero heps hr)
    exact (uniqueDiffWithinAt_Iic r).eq_deriv _ hd.hasDerivWithinAt hc
  · have hc : HasDerivWithinAt (newtonianCutoffProfile eps) 0 (Ici r) r :=
      (hasDerivWithinAt_const r (Ici r) (1:ℝ)).congr (fun s hs => newtonianCutoffProfile_one heps (le_trans hr hs))
        (newtonianCutoffProfile_one heps hr)
    exact (uniqueDiffWithinAt_Ici r).eq_deriv _ hd.hasDerivWithinAt hc

theorem abs_deriv_newtonianCutoffProfile_le (heps : 0 < eps) (r : ℝ) :
    |deriv (newtonianCutoffProfile eps) r| ≤ newtonianCutoffCap / eps := by
  have hP : HasDerivAt (fun s : ℝ => Real.smoothTransition (2 - s))
      (deriv (fun s : ℝ => Real.smoothTransition (2 - s)) (r / eps)) (r / eps) :=
    ((FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff.1.differentiable (by simp)) _).hasDerivAt
  have hq : HasDerivAt (fun s : ℝ => s / eps) (1 / eps) r := (hasDerivAt_id r).div_const eps
  have hc := (hP.comp r hq).const_sub 1
  have he : deriv (newtonianCutoffProfile eps) r =
      -(deriv (fun s : ℝ => Real.smoothTransition (2 - s)) (r / eps) * (1 / eps)) := hc.deriv
  have hL : ‖deriv (fun s : ℝ => Real.smoothTransition (2 - s)) (r / eps)‖ ≤ Real.toNNReal newtonianCutoffCap :=
    norm_deriv_le_of_lipschitz (Classical.choose_spec exists_lipschitz_radial_cutoff_cap).2.1
  rw [Real.norm_eq_abs, Real.coe_toNNReal _ newtonianCutoffCap_pos.le] at hL
  rw [he, abs_neg, abs_mul, abs_of_pos (one_div_pos.mpr heps), div_eq_mul_one_div newtonianCutoffCap eps]
  exact mul_le_mul_of_nonneg_right hL (one_div_pos.mpr heps).le

end Profile

section Component

variable {n : ℕ} {eps : ℝ}

theorem newtonianTruncatedGradientComponent_eq_zero (heps : 0 < eps) (i : Fin n) {z : EuclideanSpace ℝ (Fin n)}
    (hz : ‖z‖ ≤ eps) : newtonianTruncatedGradientComponent n eps i z = 0 := by
  simp only [newtonianTruncatedGradientComponent, newtonianCutoffProfile_zero heps hz, zero_mul]

theorem newtonianTruncatedGradientComponent_eq_of_far (heps : 0 < eps) (i : Fin n) {z : EuclideanSpace ℝ (Fin n)}
    (hz : 2 * eps ≤ ‖z‖) :
    newtonianTruncatedGradientComponent n eps i z =
      fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  simp only [newtonianTruncatedGradientComponent, newtonianCutoffProfile_one heps hz, one_mul]

theorem abs_newtonianTruncatedGradientComponent_le (i : Fin n) (z : EuclideanSpace ℝ (Fin n)) :
    |newtonianTruncatedGradientComponent n eps i z| ≤
      |fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)| := by
  rw [newtonianTruncatedGradientComponent, abs_mul, abs_of_nonneg (newtonianCutoffProfile_nonneg _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (newtonianCutoffProfile_le_one _)

theorem newtonianTruncatedGradientComponent_eventuallyEq_zero (heps : 0 < eps) (i : Fin n) :
    newtonianTruncatedGradientComponent n eps i =ᶠ[𝓝 (0:EuclideanSpace ℝ (Fin n))] fun _ => 0 := by
  filter_upwards [Metric.ball_mem_nhds (0:EuclideanSpace ℝ (Fin n)) heps] with y hy
  have hyr : ‖y‖ < eps := by simpa only [mem_ball, dist_zero_right] using hy
  exact newtonianTruncatedGradientComponent_eq_zero heps i hyr.le

theorem fderiv_newtonianTruncatedGradientComponent_zero (heps : 0 < eps) (i : Fin n) :
    fderiv ℝ (newtonianTruncatedGradientComponent n eps i) 0 = 0 := by
  rw [(newtonianTruncatedGradientComponent_eventuallyEq_zero heps i).fderiv_eq, fderiv_const_apply]

/-- Far from `0` the component is the exact Newtonian derivative near the point. -/
theorem newtonianTruncatedGradientComponent_eventuallyEq_of_far (heps : 0 < eps) (i : Fin n)
    {z : EuclideanSpace ℝ (Fin n)} (hz : 2 * eps < ‖z‖) :
    newtonianTruncatedGradientComponent n eps i =ᶠ[𝓝 z]
      fun y => fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with y hy
  exact newtonianTruncatedGradientComponent_eq_of_far heps i (le_of_lt hy)

/-- The derivative of the cut-off first derivative off `0`: `D_v G = χ′(|z|) |z|⁻¹⟨z,v⟩ D_iΓ + χ(|z|) D²Γ(z)(v, e_i)`. -/
theorem fderiv_newtonianTruncatedGradientComponent_apply (hn : 2 ≤ n) (i : Fin n) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ≠ 0) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z v =
      deriv (newtonianCutoffProfile eps) ‖z‖ * (‖z‖ ^ (-1:ℝ) * ⟪z, v⟫) *
          fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i) +
        newtonianCutoffProfile eps ‖z‖ *
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z v (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (newtonianKernel n)) z :=
    (contDiffAt_newtonianKernel hn z hz 2).fderiv_right (by norm_num)
  have hg : DifferentiableAt ℝ (fun y => fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)) z :=
    (hD.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have hp := (hasFDerivAt_newtonianCutoffProfile_norm eps z hz).mul hg.hasFDerivAt
  change HasFDerivAt (newtonianTruncatedGradientComponent n eps i) _ z at hp
  have hsecond : fderiv ℝ (fun y => fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)) z v =
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z v (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    rw [fderiv_clm_apply (hD.differentiableAt one_ne_zero) (differentiableAt_const _)]
    simp [bilinearIteratedFDerivTwo]
  rw [hp.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, hsecond]
  ring

/-- The trace density `Σ_i D_i G_{ε,i}` equals the radial expression at EVERY point, including `0`. -/
theorem sum_fderiv_newtonianTruncatedGradientComponent_eq (hn : 2 ≤ n) (heps : 0 < eps) (z : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      (1/((n:ℝ)*euclideanUnitBallVolume n))*‖z‖^(1-(n:ℝ))*deriv (newtonianCutoffProfile eps) ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    have h0 : deriv (newtonianCutoffProfile eps) ‖(0:EuclideanSpace ℝ (Fin n))‖ = 0 :=
      deriv_newtonianCutoffProfile_eq_zero heps (Or.inl (by simpa using heps.le))
    simp only [fderiv_newtonianTruncatedGradientComponent_zero heps, zero_apply, Finset.sum_const_zero, h0, mul_zero]
  · exact sum_fderiv_newtonianTruncatedGradientComponent hn eps z hz

theorem sum_fderiv_newtonianTruncatedGradientComponent_nonneg (hn : 2 ≤ n) (heps : 0 < eps)
    (z : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ∑ i : Fin n, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [sum_fderiv_newtonianTruncatedGradientComponent_eq hn heps]
  have hw := euclideanUnitBallVolume_pos n
  have h1 : 0 ≤ 1 / ((n:ℝ) * euclideanUnitBallVolume n) := by positivity
  exact mul_nonneg (mul_nonneg h1 (Real.rpow_nonneg (norm_nonneg _) _)) (deriv_newtonianCutoffProfile_nonneg heps _)

theorem sum_fderiv_newtonianTruncatedGradientComponent_eq_zero (hn : 2 ≤ n) (heps : 0 < eps)
    {z : EuclideanSpace ℝ (Fin n)} (hz : 2 * eps ≤ ‖z‖) :
    (∑ i : Fin n, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
  rw [sum_fderiv_newtonianTruncatedGradientComponent_eq hn heps, deriv_newtonianCutoffProfile_eq_zero heps (Or.inr hz),
    mul_zero]

end Component

end FunctionalInequalities.Analysis
