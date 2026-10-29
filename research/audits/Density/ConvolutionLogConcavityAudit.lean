import FunctionalInequalities.Probability.BrunnMinkowski

/-! Independent full-signature client for convolution log-concavity from finite-dimensional
Prékopa–Leindler. It asserts neither finite integrals nor smoothness. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace ConvolutionLogConcavityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem convolution_lintegral_logConcave
    {p q : V → ENNReal} (hp : Measurable p) (hq : Measurable q)
    (hpLC : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      p x ^ t * p y ^ (1 - t) ≤ p (t • x + (1 - t) • y))
    (hqLC : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      q x ^ t * q y ^ (1 - t) ≤ q (t • x + (1 - t) • y))
    (a b : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (∫⁻ z, p z * q (a - z) ∂(volume : Measure V)) ^ t *
      (∫⁻ z, p z * q (b - z) ∂(volume : Measure V)) ^ (1 - t) ≤
        ∫⁻ z, p z * q ((t • a + (1 - t) • b) - z) ∂(volume : Measure V) :=
  FunctionalInequalities.Analysis.lintegral_mul_translate_logConcave
    hp hq hpLC hqLC a b ht0 ht1

end ConvolutionLogConcavityAudit

#print axioms ConvolutionLogConcavityAudit.convolution_lintegral_logConcave
