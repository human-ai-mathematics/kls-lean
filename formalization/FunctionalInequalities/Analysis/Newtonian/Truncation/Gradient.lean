module

public import FunctionalInequalities.Analysis.Newtonian.Truncation.CutoffMass
public import FunctionalInequalities.Analysis.Newtonian.Kernel.First
public import FunctionalInequalities.Analysis.Newtonian.Kernel.Trace

/-!
# The truncated Newtonian gradient and its divergence

For `n ≥ 2` and `eps > 0`, the components `η_eps(‖z‖) ∂ᵢΓ(z)` of the truncated kernel gradient
(`newtonianTruncatedGradientComponent`), the smooth approximants in the proof of Lemma 4.2 of
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7):

* `contDiff_newtonianTruncatedGradientComponent`: each component is globally `C^∞`;
* `sum_fderiv_newtonianTruncatedGradientComponent`: off the origin its divergence is the radial
  density `(n ω_n)⁻¹ ‖z‖^(1-n) η'_eps(‖z‖)` (using the harmonicity of `Γ` off `0`);
* `integral_sum_fderiv_newtonianTruncatedGradientComponent`: the divergence is integrable with total
  mass one, the approximate identity behind `Δw = f`.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The smooth approximation of GT's proof of Lemma 4.2 cuts off the first derivative itself:
`η_eps(‖z‖) ∂ᵢΓ(z)`, with the profile `newtonianCutoffProfile`. -/
def newtonianTruncatedGradientComponent (n : ℕ) (eps : ℝ) (i : Fin n)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  newtonianCutoffProfile eps ‖z‖ *
    fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)

theorem hasFDerivAt_newtonianCutoffProfile_norm {n : ℕ} (eps : ℝ) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => newtonianCutoffProfile eps ‖y‖)
      ((deriv (newtonianCutoffProfile eps) ‖z‖ * ‖z‖ ^ (-1 : ℝ)) • innerSL ℝ z) z := by
  have hn :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) (‖z‖ ^ (-1 : ℝ) • innerSL ℝ z) z := by
    simpa only [Real.rpow_one, one_mul, show (1 : ℝ) - 2 = -1 by norm_num] using
      hasFDerivAt_norm_rpow_of_ne_zero z 1 hz
  have hp := ((contDiff_newtonianCutoffProfile eps).differentiable (by simp) ‖z‖).hasDerivAt
  convert! hp.comp_hasFDerivAt z hn using 1
  simp [smul_smul]

theorem contDiff_newtonianTruncatedGradientComponent {n : ℕ} (hn : 2 ≤ n) {eps : ℝ}
    (heps : 0 < eps) (i : Fin n) : ContDiff ℝ ∞ (newtonianTruncatedGradientComponent n eps i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : newtonianTruncatedGradientComponent n eps i =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [ball_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) heps] with y hy
      have hy' : ‖y‖ ≤ eps :=
        (by simpa only [mem_ball, dist_zero_right] using hy : ‖y‖ < eps).le
      simp only [newtonianTruncatedGradientComponent, newtonianCutoffProfile_zero heps hy',
        zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hg :
      ContDiffAt ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i))
        z :=
      ((contDiffAt_newtonianKernel hn z hz ∞).fderiv_right (by simp)).clm_apply contDiffAt_const
    exact
      ((contDiff_newtonianCutoffProfile eps).contDiffAt.comp z (contDiffAt_norm ℝ hz)).mul hg

/-- The actual trace of the smooth truncated gradient has the claimed radial density. -/
theorem sum_fderiv_newtonianTruncatedGradientComponent {n : ℕ} (hn : 2 ≤ n) (eps : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    (∑ i : Fin n,
        fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z
          (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      (1 / ((n : ℝ) * euclideanUnitBallVolume n)) * ‖z‖ ^ (1 - (n : ℝ)) *
        deriv (newtonianCutoffProfile eps) ‖z‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let c : ℝ := 1 / ((n : ℝ) * euclideanUnitBallVolume n)
  have hχ := hasFDerivAt_newtonianCutoffProfile_norm eps z hz
  have hD : ContDiffAt ℝ 1 (fderiv ℝ (newtonianKernel n)) z :=
    (contDiffAt_newtonianKernel hn z hz 2).fderiv_right (by norm_num)
  have hfirst : fderiv ℝ (newtonianKernel n) z = (c * ‖z‖ ^ (-(n : ℝ))) • innerSL ℝ z :=
    (hasFDerivAt_newtonianKernel hn z hz).fderiv
  have hsecond (i : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (newtonianKernel n) y (b i)) z (b i) =
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (b i) (b i) := by
    rw [fderiv_clm_apply (hD.differentiableAt one_ne_zero) (differentiableAt_const (b i))]
    simp [bilinearIteratedFDerivTwo]
  have he (i : Fin n) :
    fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z (b i) =
      newtonianCutoffProfile eps ‖z‖ *
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (b i) (b i) +
        ((deriv (newtonianCutoffProfile eps) ‖z‖ * ‖z‖ ^ (-1 : ℝ)) * (c * ‖z‖ ^ (-(n : ℝ)))) *
          (z i) ^ 2 := by
    have hg : DifferentiableAt ℝ (fun y => fderiv ℝ (newtonianKernel n) y (b i)) z :=
      (hD.clm_apply contDiffAt_const).differentiableAt one_ne_zero
    have hp := hχ.mul hg.hasFDerivAt
    change HasFDerivAt (newtonianTruncatedGradientComponent n eps i) _ z at hp
    rw [hp.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, hsecond, hfirst]
    rw [show ⟪z, b i⟫ = z i by simp only [b, EuclideanSpace.inner_basisFun_real]]
    ring
  change (∑ i : Fin n, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z (b i)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_bilinear_newtonianKernel_basis_self_eq_zero hn z hz, mul_zero, zero_add, ←
    Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq z]
  have hp : ‖z‖ ^ (-1 : ℝ) * ‖z‖ ^ (-(n : ℝ)) * ‖z‖ ^ 2 = ‖z‖ ^ (1 - (n : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add (norm_pos_iff.mpr hz), ←
      Real.rpow_add (norm_pos_iff.mpr hz)]
    congr 1
    ring
  calc
    _ =
        c * (‖z‖ ^ (-1 : ℝ) * ‖z‖ ^ (-(n : ℝ)) * ‖z‖ ^ 2) *
          deriv (newtonianCutoffProfile eps) ‖z‖ := by
      ring
    _ = _ := by rw [hp]

/-- The actual smooth truncated-gradient trace is integrable and has mass one. -/
theorem integral_sum_fderiv_newtonianTruncatedGradientComponent {n : ℕ} (hn : 2 ≤ n) {eps : ℝ}
    (heps : 0 < eps) :
    Integrable
        (fun z : EuclideanSpace ℝ (Fin n) =>
          ∑ i : Fin n,
            fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z
              (EuclideanSpace.basisFun (Fin n) ℝ i))
        volume ∧
      (∫ z : EuclideanSpace ℝ (Fin n),
          ∑ i : Fin n,
            fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z
              (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        1 := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have he :
    (fun z : EuclideanSpace ℝ (Fin n) =>
        ∑ i : Fin n,
          fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z
            (EuclideanSpace.basisFun (Fin n) ℝ i)) =ᵐ[volume]
      (fun z =>
        (1 / ((n : ℝ) * euclideanUnitBallVolume n)) * ‖z‖ ^ (1 - (n : ℝ)) *
          deriv (newtonianCutoffProfile eps) ‖z‖) := by
    filter_upwards [((volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne 0)] with z hz
    exact sum_fderiv_newtonianTruncatedGradientComponent hn eps z hz
  obtain ⟨hi, hI⟩ := newtonian_radial_cutoff_mass hn heps
  exact ⟨hi.congr he.symm, (integral_congr_ae he).trans hI⟩

end FunctionalInequalities.Analysis
