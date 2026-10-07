import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Buser

/-! Independent full-signature clients for Cheeger stability and general π-Buser. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GaussianBuserPassageAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem cheegerLimit (νn : ℕ → ProbabilityMeasure V) (ν : ProbabilityMeasure V)
    (hac : (ν : Measure V) ≪ volume) (H : ℝ≥0∞) (hH : H ≠ ⊤)
    (hset : ∀ D : Set V, MeasurableSet D →
      Tendsto (fun n => (νn n : Measure V) D) atTop (𝓝 ((ν : Measure V) D)))
    (hbound : ∀ᶠ n in atTop,
      H ≤ FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant (νn n)) :
    H ≤ FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant ν := by
  exact FunctionalInequalities.KLS.Isoperimetry.le_minkowskiConstant_of_setwise_tendsto
    νn ν hac H hH hset hbound

omit [CompleteSpace V] in
theorem actualBorellLaw (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ) :
    (FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal Real.pi *
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν := by
  exact FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.inv_minkowskiConstant_sq_le_pi_literature_of_borell ν hρ

theorem generalAffineLaw (μ : ProbabilityMeasure V)
    (hμ : FunctionalInequalities.KLS.LogConcave μ) :
    FunctionalInequalities.KLS.Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi *
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ := by
  exact FunctionalInequalities.KLS.LogConcave.inverseScale_sq_le_pi_literature hμ

theorem zeroDimension (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    (hμ : FunctionalInequalities.KLS.LogConcave μ) :
    FunctionalInequalities.KLS.Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi *
        FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ := by
  exact generalAffineLaw μ hμ

#print axioms cheegerLimit
#print axioms actualBorellLaw
#print axioms generalAffineLaw
#print axioms zeroDimension

end GaussianBuserPassageAudit
