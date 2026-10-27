import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
import FunctionalInequalities.KLS.LogConcave.Poincare
import FunctionalInequalities.Poincare.Convolution
import FunctionalInequalities.Poincare.Gaussian.Multivariate

/-!
# Poincaré upper stability under actual Gaussian convolution

The shared Gaussian characteristic-function identification and Gaussian
Poincaré bound control the actual convolution through the product inequality,
with a vanishing Gaussian variance term.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

set_option linter.style.haveILetI false in
/-- The actual normalized Gaussian convolution has a smooth-test optimum
bounded by the source optimum plus its Gaussian variance. No source moment
assumption or attainment of an optimal constant is used. -/
theorem smoothedLaw_smoothTest_constant_le (ν : Measure V)
    [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 < s) :
    Poincare.SmoothTest.constant (smoothedLaw ν s) ≤
      Poincare.SmoothTest.constant ν + ENNReal.ofReal (1 / (2 * s)) := by
  letI := Probability.Gaussian.law_probability (V := V) hs
  let C : NNReal := ⟨1 / (2 * s), by positivity⟩
  have hC : Poincare.SmoothTest.Holds (Probability.Gaussian.law (V := V) s) (C : ℝ) := by
    change Poincare.SmoothTest.Holds (Probability.Gaussian.law (V := V) s) (1 / (2 * s))
    exact Poincare.SmoothTest.holds_gaussianLaw hs
  have hG : Poincare.SmoothTest.constant (Probability.Gaussian.law (V := V) s) ≤
      ENNReal.ofReal (1 / (2 * s)) := by
    have hcoe : (C : ENNReal) = ENNReal.ofReal (1 / (2 * s)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ 1 / (2 * s) by positivity)]
      rfl
    rw [← hcoe]
    exact Poincare.SmoothTest.constant_le hC
  exact (Poincare.SmoothTest.constant_conv_le_add (μ := ν)
    (ν := Probability.Gaussian.law (V := V) s)).trans (add_le_add le_rfl hG)

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
