import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV.Finite
import FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant

/-! Independent clients for the proved metric BV interface. The general
BV--Minkowski identification is intentionally absent. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MetricBVInterfaceAudit

theorem finiteComplement {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [Finite X] (ν : Measure X) (B : Set X) :
    FunctionalInequalities.KLS.MetricBV.perimeter ν Bᶜ =
      FunctionalInequalities.KLS.MetricBV.perimeter ν B := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_compl ν B

theorem singletonPerimeter (ν : Measure Unit) (B : Set Unit) :
    FunctionalInequalities.KLS.MetricBV.perimeter ν B = 0 := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_eq_zero_of_subsingleton ν B

theorem singletonCheeger (ν : ProbabilityMeasure Unit) :
    FunctionalInequalities.KLS.MetricBV.halfConstant ν = ⊤ := by
  exact FunctionalInequalities.KLS.MetricBV.halfConstant_eq_top_of_subsingleton ν

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E]

theorem zeroAffineDimension (μ : ProbabilityMeasure E)
    (h : Module.finrank ℝ (FunctionalInequalities.Probability.affineSupport μ).direction = 0) :
    FunctionalInequalities.KLS.MetricBV.intrinsicHalfConstant μ = ⊤ := by
  exact FunctionalInequalities.KLS.MetricBV.intrinsicHalfConstant_eq_top_of_finrank_zero μ h

#print axioms finiteComplement
#print axioms singletonPerimeter
#print axioms singletonCheeger
#print axioms zeroAffineDimension

end MetricBVInterfaceAudit
