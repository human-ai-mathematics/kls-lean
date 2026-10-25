import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
import FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
import FunctionalInequalities.Probability.Product
import FunctionalInequalities.Probability.Covariance.Basic
import Mathlib.MeasureTheory.Group.IntegralConvolution
import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Calculus
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments

section

/-!
# Moments of the Gaussian noise and of the smoothed law

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: the Gaussian
noise `γ_s` (kernel `e^{-s‖y‖²}`, variance `ε = 1/(2s)`) has mean zero and `∫⟪v,y⟫² = ‖v‖²/(2s)`;
the smoothed law `μ * γ_s` of a law with finite second moment keeps the mean and has covariance
`Cov μ + ε·Id`, with `∫‖y‖²` increased by `n ε`. As `s → ∞` the means, raw second moments and
covariance operators converge to those of `μ`. The weak convergence of the smoothed laws is in
`Approximation`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section GaussianMoments

omit [CompleteSpace E]
/-- The Gaussian noise law `γ_s` is the tilt of Lebesgue measure by `e^{-s‖y‖²}`. -/
theorem gaussianLaw_eq_tilted {s : ℝ} (hs : 0 < s) :
    gaussianLaw (V := E) s = (volume : Measure E).tilted (fun y => -s * ‖y‖ ^ 2) := by
  have hmass : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2)) = mass (V := E) s := integral_kernel hs
  unfold gaussianLaw Measure.tilted normalizedKernel kernel
  rw [hmass]

/-- `∫ e^{‖y‖} dγ_s < ∞`. -/
theorem gaussianLaw_exp_norm_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (fun y : E => Real.exp ‖y‖) (gaussianLaw s) := by
  rw [gaussianLaw_eq_tilted hs]
  have hk : Integrable (fun y : E => Real.exp (-s * ‖y‖ ^ 2)) volume := integrable_kernel hs
  rw [integrable_tilted_iff hk]
  have hh : Integrable (fun y : E => Real.exp (-(s / 2) * ‖y‖ ^ 2)) volume :=
    integrable_kernel (by positivity : 0 < s / 2)
  refine (hh.const_mul (Real.exp (1 / (2 * s)))).mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [smul_eq_mul, Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hquad : ‖y‖ - s / 2 * ‖y‖ ^ 2 ≤ 1 / (2 * s) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
    nlinarith [sq_nonneg (s * ‖y‖ - 1)]
  nlinarith

private theorem ofReal_integral_exp_gaussian {s : ℝ} (hs : 0 < s) (z : E) :
    ((∫ y : E, Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫) : ℝ) : ℂ) =
      (Real.pi / (s : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (‖z‖ ^ 2 / (4 * (s : ℂ))) := by
  have hb : 0 < (s : ℂ).re := by simpa using hs
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := E) hb 1 z
  calc
    ((∫ y : E, Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫) : ℝ) : ℂ) =
        ∫ y : E, (Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫) : ℂ) := integral_complex_ofReal.symm
    _ = ∫ y : E, Complex.exp (-(s : ℂ) * ‖y‖ ^ 2 + 1 * ⟪z, y⟫) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    _ = _ := by rw [h]; simp

/-- Laplace transform of `γ_s`: `∫ e^{⟪z,y⟫} dγ_s = e^{‖z‖²/(4s)}` (variance `ε = 1/(2s)`). -/
theorem gaussianLaw_laplace {s : ℝ} (hs : 0 < s) (z : E) :
    (∫ y, Real.exp ⟪z, y⟫ ∂(gaussianLaw (V := E) s)) = Real.exp (‖z‖ ^ 2 / (4 * s)) := by
  rw [gaussianLaw_eq_tilted hs, integral_tilted]
  simp only [smul_eq_mul]
  have hnum : (∫ y : E, Real.exp (-s * ‖y‖ ^ 2) /
      (∫ w : E, Real.exp (-s * ‖w‖ ^ 2)) * Real.exp ⟪z, y⟫) =
      (∫ y : E, Real.exp (-s * ‖y‖ ^ 2 + ⟪z, y⟫)) /
        (∫ w : E, Real.exp (-s * ‖w‖ ^ 2)) := by
    rw [← integral_div]
    congr 1
    funext y
    rw [Real.exp_add]
    ring
  rw [hnum]
  have h0 := ofReal_integral_exp_gaussian hs (0 : E)
  simp only [inner_zero_left, add_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Complex.ofReal_zero, zero_div, Complex.exp_zero, mul_one] at h0
  have hz := ofReal_integral_exp_gaussian hs z
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hne : (Real.pi / (s : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (div_ne_zero hpC hsC) h.1
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, hz, h0, Complex.ofReal_exp]
  push_cast
  field_simp


/-- `γ_s` has a finite second moment. -/
theorem gaussianLaw_memLp_two {s : ℝ} (hs : 0 < s) : MemLp id 2 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable (E := E) hs
  exact (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    (Probability.integrable_norm_pow_of_integrable_exp_norm (by norm_num : (0 : ℝ) < 1) he 2)

end GaussianMoments

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem hasFDerivAt_exp_norm_sq_div {s : ℝ} (hs : 0 < s) (z : E) :
    HasFDerivAt (fun w : E => Real.exp (‖w‖ ^ 2 / (4 * s)))
      ((Real.exp (‖z‖ ^ 2 / (4 * s)) / (2 * s)) • innerSL ℝ z) z := by
  have hn : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hq : HasFDerivAt (fun w : E => ‖w‖ ^ 2 / (4 * s))
      ((4 * s)⁻¹ • (2 • innerSL ℝ z)) z := by
    convert! hn.const_mul (4 * s)⁻¹ using 1
    funext w
    simp only [div_eq_mul_inv]
    ring
  have h := hq.exp
  convert h using 1
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  field_simp [hs.ne']
  ring

/-- `γ_s` has mean zero. -/
theorem gaussianLaw_mean_zero {s : ℝ} (hs : 0 < s) :
    (∫ y : E, y ∂(gaussianLaw s)) = 0 := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have hi : Integrable id (gaussianLaw (V := E) s) := (gaussianLaw_memLp_two hs).integrable one_le_two
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable (E := E) hs
  have hfun : (fun z : E => ∫ y, Real.exp ⟪z, y⟫ ∂(gaussianLaw s)) =
      fun z => Real.exp (‖z‖ ^ 2 / (4 * s)) := funext fun z => gaussianLaw_laplace hs z
  apply ext_inner_left ℝ
  intro v
  rw [inner_zero_right]
  change (innerSL ℝ v) (∫ y, id y ∂(gaussianLaw s)) = 0
  rw [← (innerSL ℝ v).integral_comp_comm hi]
  change (∫ y : E, ⟪v, y⟫ ∂(gaussianLaw s)) = 0
  have hm := iteratedFDeriv_laplace_zero (gaussianLaw (V := E) s)
    (by norm_num : (0 : ℝ) < 1) he 1 (fun _ => v)
  rw [hfun] at hm
  have hzero : fderiv ℝ (fun z : E => Real.exp (‖z‖ ^ 2 / (4 * s))) 0 = 0 := by
    rw [(hasFDerivAt_exp_norm_sq_div hs (0 : E)).fderiv]
    simp
  simp only [iteratedFDeriv_one_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, pow_one, hzero, zero_apply] at hm
  calc (∫ y : E, ⟪v, y⟫ ∂(gaussianLaw s)) = ∫ y : E, ⟪y, v⟫ ∂(gaussianLaw s) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => (real_inner_comm v y).symm
    _ = 0 := hm.symm

section SmoothedMoments

omit [CompleteSpace E]
/-- `∫ ⟪v,y⟫² dγ_s = ‖v‖²/(2s)`. -/
theorem gaussianLaw_inner_sq {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(gaussianLaw s)) = ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun y : E => Real.exp ((1 : ℝ) * ‖y‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable (E := E) hs
  let F : E → ℝ := fun z => Real.exp (‖z‖ ^ 2 / (4 * s))
  have hF : ContDiff ℝ 2 F := ((contDiff_norm_sq ℝ).div_const (4 * s)).exp
  have hm := iteratedFDeriv_laplace_zero (gaussianLaw (V := E) s)
    (by norm_num : (0 : ℝ) < 1) he 2 ![v, v]
  have hfunL : (fun z : E => ∫ y, Real.exp ⟪z, y⟫ ∂(gaussianLaw s)) = F :=
    funext fun z => gaussianLaw_laplace hs z
  rw [hfunL] at hm
  have hprod : (fun y : E => ∏ j : Fin 2, ⟪y, (![v, v] : Fin 2 → E) j⟫) =
      fun y => ⟪v, y⟫ ^ 2 := by
    funext y
    simp [Fin.prod_univ_two, pow_two, real_inner_comm]
  rw [hprod, ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_fderiv_apply hF] at hm
  have hfun : (fun z : E => fderiv ℝ F z v) =
      fun z => (F z / (2 * s)) * ⟪v, z⟫ := by
    funext z
    rw [(hasFDerivAt_exp_norm_sq_div hs z).fderiv]
    simp [F, innerSL_apply_apply, real_inner_comm]
  have hzero : HasFDerivAt F (0 : E →L[ℝ] ℝ) 0 := by
    simpa only [F, innerSL, map_zero, smul_zero] using hasFDerivAt_exp_norm_sq_div hs (0 : E)
  have hscaled : HasFDerivAt (fun z => F z / (2 * s)) (0 : E →L[ℝ] ℝ) 0 := by
    convert! hzero.const_mul (2 * s)⁻¹ using 1
    · funext z
      simp only [div_eq_mul_inv]
      ring
    · simp
  have hd : HasFDerivAt (fun z => F z / (2 * s) * ⟪v, z⟫)
      ((1 / (2 * s)) • innerSL ℝ v) 0 := by
    simpa only [Pi.mul_def, coe_innerSL_apply, F, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Real.exp_zero, inner_zero_right, zero_smul, add_zero] using
      hscaled.mul ((innerSL ℝ v).hasFDerivAt (x := (0 : E)))

  rw [hfun, hd.fderiv] at hm
  simpa only [F, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.exp_zero,
    inner_zero_right, innerSL_apply_apply, add_apply,
    smul_apply, smul_eq_mul, zero_apply,
    mul_zero, zero_smul, zero_add, add_zero, real_inner_self_eq_norm_sq,
    one_div, one_mul, div_eq_mul_inv, mul_comm] using hm.symm

/-- The smoothed law `μ * γ_s` has a finite second moment when `μ` does. -/
theorem smoothedLaw_memLp_two (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) : MemLp id 2 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  unfold smoothedLaw Measure.conv
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact (hμ2.comp_fst (gaussianLaw s)).add ((gaussianLaw_memLp_two hs).comp_snd μ)

end SmoothedMoments

/-- Gaussian smoothing preserves the mean. -/
theorem smoothedLaw_mean (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, y ∂(smoothedLaw μ s)) = ∫ y : E, y ∂μ := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have hfirst : Integrable (fun p : E × E => p.1) (μ.prod (gaussianLaw s)) :=
    (hμ2.comp_fst (gaussianLaw s)).integrable one_le_two
  have hsecond : Integrable (fun p : E × E => p.2) (μ.prod (gaussianLaw s)) :=
    ((gaussianLaw_memLp_two hs).comp_snd μ).integrable one_le_two
  unfold smoothedLaw Measure.conv
  change (∫ y, id y ∂(Measure.map (fun p : E × E => p.1 + p.2) (μ.prod (gaussianLaw s)))) = _
  rw [integral_map (by fun_prop) continuous_id.aestronglyMeasurable]
  change (∫ p : E × E, p.1 + p.2 ∂(μ.prod (gaussianLaw s))) = _
  rw [integral_add hfirst hsecond, integral_fun_fst (fun y : E => y), integral_fun_snd (fun y : E => y),
    gaussianLaw_mean_zero hs]
  simp

/-- `Var_{γ_s}⟪v,·⟫ = ‖v‖²/(2s)`. -/
theorem gaussianLaw_variance {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (gaussianLaw s) = ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have h2 : MemLp (fun y : E => ⟪v, y⟫) 2 (gaussianLaw s) := by
    simpa only [id_eq, innerSL_apply_apply] using
      (gaussianLaw_memLp_two hs).continuousLinearMap_comp (innerSL ℝ v)
  have h0 : (∫ y : E, ⟪v, y⟫ ∂(gaussianLaw s)) = 0 := by
    change (∫ y, (innerSL ℝ v) (id y) ∂(gaussianLaw s)) = 0
    rw [(innerSL ℝ v).integral_comp_comm ((gaussianLaw_memLp_two hs).integrable one_le_two)]
    simp only [id_eq]
    rw [gaussianLaw_mean_zero hs]
    simp
  rw [variance_eq_sub h2, h0]
  simp only [Pi.pow_apply]
  rw [gaussianLaw_inner_sq hs]
  simp

/-- Variances add under smoothing: `Var_{μ*γ_s}⟪v,·⟫ = Var_μ⟪v,·⟫ + ‖v‖²/(2s)`. -/
theorem smoothedLaw_variance (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    variance (fun y : E => ⟪v, y⟫) (smoothedLaw μ s) =
      variance (fun y : E => ⟪v, y⟫) μ + ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have hX : MemLp (fun y : E => ⟪v, y⟫) 2 μ := by
    simpa only [id_eq, innerSL_apply_apply] using hμ2.continuousLinearMap_comp (innerSL ℝ v)
  have hY : MemLp (fun y : E => ⟪v, y⟫) 2 (gaussianLaw s) := by
    simpa only [id_eq, innerSL_apply_apply] using
      (gaussianLaw_memLp_two hs).continuousLinearMap_comp (innerSL ℝ v)
  have h := variance_add_prod hX hY
  rw [gaussianLaw_variance hs] at h
  unfold smoothedLaw Measure.conv
  rw [variance_map (by fun_prop : AEMeasurable (fun y : E => ⟪v, y⟫) _)
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)]
  simpa only [Function.comp_def, inner_add_right] using h


/-- The covariance form of the smoothed law is `Cov_μ + ⟪·,·⟫/(2s)`. -/
theorem smoothedLaw_covarianceBilin (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v w : E) :
    covarianceBilin (smoothedLaw μ s) v w = covarianceBilin μ v w + ⟪v, w⟫ / (2 * s) := by
  let _ : IsProbabilityMeasure (smoothedLaw μ s) := smoothedLaw_probability hs
  have hsm2 := smoothedLaw_memLp_two μ hμ2 hs
  have hdiag (u : E) : covarianceBilin (smoothedLaw μ s) u u =
      covarianceBilin μ u u + ‖u‖ ^ 2 / (2 * s) := by
    rw [covarianceBilin_self hsm2, covarianceBilin_self hμ2]
    exact smoothedLaw_variance μ hμ2 hs u
  have hv := hdiag v
  have hw := hdiag w
  have hsum := hdiag (v + w)
  simp only [map_add, add_apply] at hsum
  rw [covarianceBilin_comm (μ := smoothedLaw μ s) w v, covarianceBilin_comm (μ := μ) w v,
    norm_add_sq_real] at hsum
  field_simp [hs.ne'] at hv hw hsum ⊢
  nlinarith

/-- **Covariance of the smoothed law**: `Cov(μ * γ_s) = Cov μ + (1/(2s)) · Id` (BKL Section 2, p. 5). -/
theorem smoothedLaw_covariance_operator (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    Covariance.operator (smoothedLaw μ s) = Covariance.operator μ +
      (1 / (2 * s)) • (1 : E →L[ℝ] E) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  rw [Covariance.operator_inner]
  simp only [add_apply, smul_apply, inner_add_left, real_inner_smul_left,
    Covariance.operator_inner]
  have hone : (1 : E →L[ℝ] E) v = v := rfl
  rw [hone]
  simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using smoothedLaw_covarianceBilin μ hμ2 hs v w


/-- Raw directional second moments increase by `‖v‖²/(2s)`. -/
theorem smoothedLaw_inner_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) (v : E) :
    (∫ y : E, ⟪v, y⟫ ^ 2 ∂(smoothedLaw μ s)) =
      (∫ y : E, ⟪v, y⟫ ^ 2 ∂μ) + ‖v‖ ^ 2 / (2 * s) := by
  let _ : IsProbabilityMeasure (smoothedLaw μ s) := smoothedLaw_probability hs
  have hsm2 := smoothedLaw_memLp_two μ hμ2 hs
  have hX : MemLp (fun y : E => ⟪v, y⟫) 2 μ := by
    simpa only [id_eq, innerSL_apply_apply] using hμ2.continuousLinearMap_comp (innerSL ℝ v)
  have hY : MemLp (fun y : E => ⟪v, y⟫) 2 (smoothedLaw μ s) := by
    simpa only [id_eq, innerSL_apply_apply] using hsm2.continuousLinearMap_comp (innerSL ℝ v)
  have hm : (∫ y : E, ⟪v, y⟫ ∂(smoothedLaw μ s)) = ∫ y : E, ⟪v, y⟫ ∂μ := by
    change (∫ y, (innerSL ℝ v) (id y) ∂(smoothedLaw μ s)) = ∫ y, (innerSL ℝ v) (id y) ∂μ
    rw [(innerSL ℝ v).integral_comp_comm (hsm2.integrable one_le_two),
      (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)]
    congr 1
    simpa only [id_eq] using smoothedLaw_mean μ hμ2 hs
  have hv := smoothedLaw_variance μ hμ2 hs v
  rw [variance_eq_sub hY, variance_eq_sub hX, hm] at hv
  simp only [Pi.pow_apply] at hv
  linarith

/-- `∫ ‖y‖² d(μ*γ_s) = ∫ ‖y‖² dμ + n/(2s)`. -/
theorem smoothedLaw_norm_sq (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {s : ℝ} (hs : 0 < s) :
    (∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) =
      (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hsm2 := smoothedLaw_memLp_two μ hμ2 hs
  have hi (ν : Measure E) (hν : MemLp id 2 ν) (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun y : E => ⟪b i, y⟫ ^ 2) ν := by
    have h : MemLp (fun y : E => ⟪b i, y⟫) 2 ν := by
      simpa only [id_eq, innerSL_apply_apply] using hν.continuousLinearMap_comp (innerSL ℝ (b i))
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h
  have heq : (fun y : E => ‖y‖ ^ 2) = fun y => ∑ i, ⟪b i, y⟫ ^ 2 := by
    funext y
    exact (b.sum_sq_inner_right y).symm
  rw [heq, integral_finsetSum Finset.univ (fun i _ => hi _ hsm2 i),
    integral_finsetSum Finset.univ (fun i _ => hi _ hμ2 i)]
  simp_rw [smoothedLaw_inner_sq μ hμ2 hs]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [b.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

private theorem epsilon_tendsto_zero :
    Tendsto (fun s : ℝ => 1 / (2 * s)) atTop (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun s : ℝ => 2 * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  simpa only [Function.comp_def, one_div] using (tendsto_inv_atTop_zero.comp ht)

/-- The means of the smoothed laws converge (they are constant) as `s → ∞`. -/
theorem smoothedLaw_mean_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, y ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, y ∂μ)) := by
  apply (tendsto_const_nhds (x := ∫ y : E, y ∂μ)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_mean μ hμ2 hs).symm

/-- The raw second moments of the smoothed laws converge as `s → ∞`. -/
theorem smoothedLaw_norm_sq_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => ∫ y : E, ‖y‖ ^ 2 ∂(smoothedLaw μ s)) atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
  have ht : Tendsto (fun s : ℝ => (∫ y : E, ‖y‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * s))
      atTop (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂μ)) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_zero, add_zero] using
      (tendsto_const_nhds (x := ∫ y : E, ‖y‖ ^ 2 ∂μ)).add
        (epsilon_tendsto_zero.const_mul (Module.finrank ℝ E : ℝ))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_norm_sq μ hμ2 hs).symm

/-- The covariance operators of the smoothed laws converge in operator norm as `s → ∞`. -/
theorem smoothedLaw_covariance_operator_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) :
    Tendsto (fun s : ℝ => Covariance.operator (smoothedLaw μ s)) atTop (𝓝 (Covariance.operator μ)) := by
  have ht : Tendsto (fun s : ℝ => Covariance.operator μ + (1 / (2 * s)) • (1 : E →L[ℝ] E))
      atTop (𝓝 (Covariance.operator μ)) := by
    simpa only [zero_smul, add_zero] using (tendsto_const_nhds (x := Covariance.operator μ)).add
      (epsilon_tendsto_zero.smul (tendsto_const_nhds (x := (1 : E →L[ℝ] E))))
  apply ht.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
  exact (smoothedLaw_covariance_operator μ hμ2 hs).symm

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

section GaussianDirectionalIdentity

open MeasureTheory Filter
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

set_option maxHeartbeats 800000 in
/-- Gaussian integration by parts for C1 bounded globally Lipschitz tests: under `gaussianLaw s` (`s > 0`, all dimensions),
`∫ ⟪x, v⟫ f = (2 s)⁻¹ ∫ D_v f`, with both integrands integrable. -/
theorem gaussianLaw_directional_identity_of_bounded_lipschitz_test {n : ℕ}
    {s : ℝ} (hs : 0 < s) {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : ContDiff ℝ 1 f) (hLip : LipschitzWith L f) (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => ⟪x, v⟫ * f x) (gaussianLaw s) ∧
    Integrable (fun x => fderiv ℝ f x v) (gaussianLaw s) ∧
    (∫ x, ⟪x, v⟫ * f x ∂(gaussianLaw s)) =
      (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂(gaussianLaw s) := by
  let E := EuclideanSpace ℝ (Fin n)
  let w : E → ℝ := fun x => Real.exp (-s * ‖x‖ ^ 2)
  let mu : Measure E := gaussianLaw s
  let : IsProbabilityMeasure mu := gaussianLaw_probability hs
  have hexp : Integrable (fun x : E => Real.exp (-s * ‖x‖ ^ 2)) volume := integrable_kernel hs
  have hF : Integrable f mu :=
    (integrable_const C).mono' hf.continuous.aestronglyMeasurable (ae_of_all _ hbound)
  have hX : Integrable (fun x : E => ⟪x, v⟫) mu :=
    ((gaussianLaw_memLp_two hs).inner_const (𝕜 := ℝ) v).integrable one_le_two
  have hXF : Integrable (fun x : E => ⟪x, v⟫ * f x) mu :=
    hX.mul_bdd hf.continuous.aestronglyMeasurable (ae_of_all _ hbound)
  have hdfmeas : Measurable (fun x : E => fderiv ℝ f x v) :=
    (continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hDF : Integrable (fun x : E => fderiv ℝ f x v) mu := by
    apply (integrable_const ((L : ℝ) * ‖v‖)).mono' hdfmeas.aestronglyMeasurable
    exact ae_of_all _ fun x => ((fderiv ℝ f x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg v))
  have raw (k : E → ℝ) (hk : Integrable k mu) : Integrable (fun x => w x * k x) volume := by
    have hkt : Integrable k ((volume : Measure E).tilted (fun x => -s * ‖x‖ ^ 2)) := by
      rwa [← gaussianLaw_eq_tilted hs]
    simpa only [w, smul_eq_mul] using (integrable_tilted_iff hexp k).mp hkt
  have hRawF := raw f hF
  have hRawXF := raw (fun x => ⟪x, v⟫ * f x) hXF
  have hRawDF := raw (fun x => fderiv ℝ f x v) hDF
  have hw : ContDiff ℝ 1 w := by
    have hn : ContDiff ℝ 1 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact ((contDiff_const : ContDiff ℝ 1 (fun _ : E => -s)).mul hn).exp
  have hd (x : E) : fderiv ℝ (fun y => w y * f y) x v =
      w x * fderiv ℝ f x v - (2 * s) * (w x * (⟪x, v⟫ * f x)) := by
    have hwx : HasFDerivAt w (w x • ((-s) • (2 • innerSL ℝ x))) x :=
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-s)).exp
    change fderiv ℝ (w * f) x v = _
    rw [(hwx.mul ((hf.differentiable one_ne_zero x).hasFDerivAt)).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring
  have hRawD : Integrable (fun x => fderiv ℝ (fun y => w y * f y) x v) volume := by
    apply (hRawDF.sub (hRawXF.const_mul (2 * s))).congr
    filter_upwards [] with x
    exact (hd x).symm
  have hz := integral_eq_zero_of_integrable_weak_derivative
    (hasWeakDerivAlong_of_contDiff (hw.mul hf) v) hRawF hRawD
  have hRawEq : (∫ x, w x * fderiv ℝ f x v ∂volume) =
      (2 * s) * ∫ x, w x * (⟪x, v⟫ * f x) ∂volume := by
    have heq : (∫ x, fderiv ℝ (fun y => w y * f y) x v ∂volume) =
        (∫ x, w x * fderiv ℝ f x v ∂volume) -
        (2 * s) * ∫ x, w x * (⟪x, v⟫ * f x) ∂volume := by
      calc
        _ = ∫ x, w x * fderiv ℝ f x v - (2 * s) * (w x * (⟪x, v⟫ * f x)) ∂volume :=
          integral_congr_ae (ae_of_all _ hd)
        _ = _ := by rw [integral_sub hRawDF (hRawXF.const_mul (2 * s)), integral_const_mul]
    linarith
  have htilt (k : E → ℝ) : (∫ x, k x ∂mu) =
      (∫ x, w x * k x ∂volume) / (∫ x, w x ∂volume) := by
    dsimp only [mu]
    rw [gaussianLaw_eq_tilted hs, integral_tilted]
    change (∫ x, (w x / (∫ y, w y ∂volume)) * k x ∂volume) = _
    simp_rw [div_mul_eq_mul_div]
    exact integral_div _ _
  refine ⟨hXF, hDF, ?_⟩
  change (∫ x, ⟪x, v⟫ * f x ∂mu) = (2 * s)⁻¹ * ∫ x, fderiv ℝ f x v ∂mu
  rw [htilt, htilt, hRawEq, mul_div_assoc, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hs)), one_mul]

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end GaussianDirectionalIdentity

end

/-! ### Fourth moments of Gaussian, smoothed and linear-image laws; translated Gaussian identity

`gaussianLaw s` has a fourth moment; fourth moments pass to smoothed laws and linear images; the Gaussian directional identity for bounded Lipschitz `C¹` tests holds after a translation. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

theorem gaussianLaw_memLp_four {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : ℝ} (hs : 0 < s) : MemLp id 4 (gaussianLaw (V := E) s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  have he : Integrable (fun x : E => Real.exp ((1 : ℝ) * ‖x‖)) (gaussianLaw s) := by
    simpa only [one_mul] using gaussianLaw_exp_norm_integrable (E := E) hs
  have hp := Probability.integrable_norm_pow_of_integrable_exp_norm
    (by norm_num : (0 : ℝ) < 1) he 4
  apply (integrable_norm_rpow_iff (f := (id : E → E)) continuous_id.aestronglyMeasurable
    (by norm_num : (4 : ENNReal) ≠ 0) (by simp : (4 : ENNReal) ≠ ∞)).mp
  simpa using hp

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem smoothedLaw_memLp_four (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ4 : MemLp id 4 μ) {s : ℝ} (hs : 0 < s) : MemLp id 4 (smoothedLaw μ s) := by
  let _ : IsProbabilityMeasure (gaussianLaw (V := E) s) := gaussianLaw_probability hs
  unfold smoothedLaw Measure.conv
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun p : E × E => p.1 + p.2) _)).2
  exact (hμ4.comp_fst (gaussianLaw s)).add ((gaussianLaw_memLp_four hs).comp_snd μ)

theorem map_linear_memLp_four (μ : Measure E) (S : E →L[ℝ] E)
    (hμ4 : MemLp id 4 μ) : MemLp id 4 (μ.map S) := by
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable S.continuous.measurable.aemeasurable).2
  exact S.comp_memLp' hμ4

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

theorem gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {Lh : NNReal}
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (a v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    Integrable (fun z => ⟪z,v⟫ * h (a+z)) (gaussianLaw s) ∧
    Integrable (fun z => fderiv ℝ h (a+z) v) (gaussianLaw s) ∧
    (∫ z, ⟪z,v⟫ * h (a+z) ∂(gaussianLaw s)) =
      (2*s)⁻¹ * ∫ z, fderiv ℝ h (a+z) v ∂(gaussianLaw s) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hf : ContDiff ℝ 1 (fun z : E => h (a+z)) := hh.comp (contDiff_const.add contDiff_id)
  have hp := gaussianLaw_directional_identity_of_bounded_lipschitz_test hs hf
    (hhLip.comp ((LipschitzWith.const a).add LipschitzWith.id)) C (fun z => hbound (a+z)) v
  have hd (z : E) : fderiv ℝ (fun w => h (a+w)) z v = fderiv ℝ h (a+z) v := by
    have ha : HasFDerivAt (fun w : E => a+w) (ContinuousLinearMap.id ℝ E) z :=
      (hasFDerivAt_id z).const_add a
    exact congrArg (fun T : E →L[ℝ] ℝ => T v)
      ((hh.differentiable one_ne_zero (a+z)).hasFDerivAt.comp z ha).fderiv
  refine ⟨hp.1,hp.2.1.congr (ae_of_all _ hd),hp.2.2.trans ?_⟩
  congr 1
  exact integral_congr_ae (ae_of_all _ hd)

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end
