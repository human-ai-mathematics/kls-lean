import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.Poincare.Convolution
import FunctionalInequalities.Poincare.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Poincaré upper stability under actual Gaussian convolution

The normalized radial Gaussian kernel is identified with a scaled standard
multivariate Gaussian by its characteristic function. The product Poincaré
bound then controls the actual convolution, with a vanishing Gaussian term.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem charFun_gaussianLaw {s : ℝ} (hs : 0 < s) (t : V) :
    charFun (gaussianLaw (V := V) s) t = Complex.exp (-(‖t‖ ^ 2 / (4 * s) : ℝ)) := by
  rw [charFun_apply, gaussianLaw,
    integral_withDensity_eq_integral_toReal_smul
      ((normalizedKernel_measurable s).ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (normalizedKernel_pos hs _).le]
  have hform (x : V) : normalizedKernel s x •
      Complex.exp ((inner ℝ x t : ℂ) * Complex.I) =
      ((mass (V := V) s)⁻¹ : ℂ) •
        Complex.exp (-(s : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * (inner ℝ t x : ℂ)) := by
    simp only [normalizedKernel, kernel, real_inner_comm, Complex.exp_add]
    change ((Real.exp (-s * ‖x‖ ^ 2) / mass (V := V) s : ℝ) : ℂ) *
      Complex.exp ((inner ℝ t x : ℂ) * Complex.I) =
      ((mass (V := V) s)⁻¹ : ℂ) *
        (Complex.exp (-(s : ℂ) * (‖x‖ : ℂ) ^ 2) *
          Complex.exp (Complex.I * (inner ℝ t x : ℂ)))
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
  simp_rw [hform]
  rw [integral_smul]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := V) (show 0 < (s : ℂ).re from hs) Complex.I t]
  have hmass : (mass (V := V) s : ℂ) =
      ((Real.pi : ℂ) / s) ^ (((Module.finrank ℝ V : ℂ) / 2)) := by
    unfold mass
    norm_cast
    simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / s)
      ((Module.finrank ℝ V : ℝ) / 2))
  rw [← hmass]
  have hm : (mass (V := V) s : ℂ) ≠ 0 := by
    exact_mod_cast (mass_pos (V := V) hs).ne'
  simp only [smul_eq_mul, Complex.I_sq, neg_one_mul]
  have hexp : -(‖t‖ : ℂ) ^ 2 / (4 * (s : ℂ)) =
      -(‖t‖ ^ 2 / (4 * s) : ℝ) := by
    push_cast
    ring
  rw [hexp, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]

set_option linter.style.haveILetI false in
theorem gaussianLaw_eq_scaled_stdGaussian {s : ℝ} (hs : 0 < s) :
    gaussianLaw (V := V) s =
      (stdGaussian V).map (fun x : V => (Real.sqrt (2 * s))⁻¹ • x) := by
  haveI : IsProbabilityMeasure (gaussianLaw (V := V) s) :=
    gaussianLaw_probability hs
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_gaussianLaw hs, charFun_map_smul, charFun_stdGaussian]
  have hss : 0 < 2 * s := by positivity
  have hr : 0 ≤ (Real.sqrt (2 * s))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr2 : ((Real.sqrt (2 * s))⁻¹) ^ 2 = (2 * s)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hss.le]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  congr 1
  norm_cast
  rw [mul_pow, hr2]
  field_simp
  ring

/-- The Gaussian factor used by the actual convolution has fixed Poincaré
constant `1/(2s)`, also in dimension zero. -/
theorem gaussianLaw_smoothTest_holds {s : ℝ} (hs : 0 < s) :
    Poincare.SmoothTest.Holds (gaussianLaw (V := V) s) (1 / (2 * s)) := by
  rw [gaussianLaw_eq_scaled_stdGaussian hs]
  have h := Poincare.SmoothTest.holds_stdGaussian_map_smul (V := V)
    (Real.sqrt (2 * s))⁻¹
  have hsq : (Real.sqrt (2 * s))⁻¹ ^ 2 = 1 / (2 * s) := by
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * s)]
    ring
  rwa [hsq] at h

set_option linter.style.haveILetI false in
/-- The actual normalized Gaussian convolution has a smooth-test optimum
bounded by the source optimum plus its Gaussian variance. No source moment
assumption or attainment of an optimal constant is used. -/
theorem smoothedLaw_smoothTest_constant_le (ν : Measure V)
    [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s) :
    Poincare.SmoothTest.constant (smoothedLaw ν s) ≤
      Poincare.SmoothTest.constant ν + ENNReal.ofReal (1 / (2 * s)) := by
  letI := gaussianLaw_probability (V := V) hs
  let C : NNReal := ⟨1 / (2 * s), by positivity⟩
  have hC : Poincare.SmoothTest.Holds (gaussianLaw (V := V) s) (C : ℝ) := by
    change Poincare.SmoothTest.Holds (gaussianLaw (V := V) s) (1 / (2 * s))
    exact gaussianLaw_smoothTest_holds hs
  have hG : Poincare.SmoothTest.constant (gaussianLaw (V := V) s) ≤
      ENNReal.ofReal (1 / (2 * s)) := by
    have hcoe : (C : ENNReal) = ENNReal.ofReal (1 / (2 * s)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ 1 / (2 * s) by positivity)]
      rfl
    rw [← hcoe]
    exact Poincare.SmoothTest.constant_le hC
  exact (Poincare.SmoothTest.constant_conv_le_add (μ := ν)
    (ν := gaussianLaw (V := V) s)).trans (add_le_add le_rfl hG)

/-- Upper stability of the intrinsic literature Poincaré optimum for the
actual normalized Gaussian convolution. The additive term tends to zero as
`s` grows. This includes zero dimension and infinite source constants. -/
theorem smoothedProbabilityLaw_literatureConstant_le
    (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    {s : ℝ} (hs : 0 < s) :
    Poincare.LocalSlope.Intrinsic.constant (smoothedProbabilityLaw ν s hs) ≤
      Poincare.LocalSlope.Intrinsic.constant ν + ENNReal.ofReal (1 / (2 * s)) := by
  have hsource := (FunctionalInequalities.KLS.IsBorellDensity.compactLogConcave hρ)
    |>.smoothTest_constant_eq_localSlope
  have htarget := (smoothedProbabilityLaw_logConcave hρ hs)
    |>.smoothTest_constant_eq_localSlope
  calc
    Poincare.LocalSlope.Intrinsic.constant (smoothedProbabilityLaw ν s hs) =
        Poincare.SmoothTest.constant (smoothedLaw (ν : Measure V) s) := htarget.symm
    _ ≤ Poincare.SmoothTest.constant (ν : Measure V) +
        ENNReal.ofReal (1 / (2 * s)) := smoothedLaw_smoothTest_constant_le _ hs
    _ = _ := by rw [hsource]

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
