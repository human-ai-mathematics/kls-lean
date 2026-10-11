import FunctionalInequalities.KLS.LogConcave.WeakLimit

/-!
# Audit: weak-limit transfer of the Poincaré bound (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5 (reduction of Theorem 1.1 to
regular laws by a limiting argument). Audited declarations: the weak passage on compactly supported
smooth tests, the cutoff extension to all admissible tests, and the transfer to the literature
constant of a log-concave limit law. Clients instantiate the transfer with a constant sequence and
with the trivial sequence `μs j = μ`. Neither the approximating laws nor Theorem 1.1 is asserted.
-/

open MeasureTheory Filter Topology FunctionalInequalities

namespace WeakLimitAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A constant sequence of laws with a constant Poincaré bound transfers the bound. -/
theorem constant_sequence_client (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ) (C : NNReal)
    (h : Poincare.SmoothTest.Holds (μ : Measure E) (C : ℝ)) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) :=
  KLS.LogConcave.localSlope_constant_le_of_tendsto (fun _ => μ) μ hμ (fun _ => C) C
    tendsto_const_nhds tendsto_const_nhds (fun _ => h)

/-- Constants `C + 1/j` converging to `C` transfer the limit constant. -/
theorem decreasing_constants_client (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : KLS.LogConcave μ) (C : NNReal) (hlim : Tendsto μs atTop (𝓝 μ))
    (hbound : ∀ j, Poincare.SmoothTest.Holds (μs j : Measure E)
      ((C + (1 : NNReal) / (j : NNReal) : NNReal) : ℝ)) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) := by
  refine KLS.LogConcave.localSlope_constant_le_of_tendsto μs μ hμ
    (fun j => C + (1 : NNReal) / (j : NNReal)) C hlim ?_ hbound
  have h1 : Tendsto (fun j : ℕ => (1 : NNReal) / (j : NNReal)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat (𝕜 := NNReal)
  have h2 := (tendsto_const_nhds (x := C) (f := atTop)).add h1
  rwa [add_zero] at h2

end WeakLimitAudit

#print axioms FunctionalInequalities.Poincare.SmoothTest.variance_le_mul_energy_of_tendsto
#print axioms FunctionalInequalities.Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport
#print axioms FunctionalInequalities.Poincare.SmoothTest.tendsto_integral_scaled_mul
#print axioms FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_eq
#print axioms FunctionalInequalities.Poincare.SmoothTest.norm_gradient_scaled_mul_sq_le
#print axioms FunctionalInequalities.Poincare.SmoothTest.tendsto_energy_scaled_mul
#print axioms FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport
#print axioms FunctionalInequalities.KLS.LogConcave.localSlope_constant_le_of_tendsto
#print axioms WeakLimitAudit.constant_sequence_client
#print axioms WeakLimitAudit.decreasing_constants_client
