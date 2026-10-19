import FunctionalInequalities.Analysis.MetricBV.Counterexample
import FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for complement symmetry of the metric BV perimeter
beyond finite spaces: the local-slope comparison, the finite-measure theorem, its closed-support
and intrinsic closed-support specializations, a non-finite instance (the standard Gaussian law
on `ℝ`), and the infinite-measure obstruction showing that finiteness cannot be dropped. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MetricBVComplementAudit

theorem slopeComparison {X : Type*} [MetricSpace X] {g a b : X → ℝ} {x : X} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h : ∀ y, dist y x < r₀ → dist (g y) (g x) ≤ dist (a y) (a x) + dist (b y) (b x)) :
    FunctionalInequalities.Energy.LocalSlope.apply g x ≤
      FunctionalInequalities.Energy.LocalSlope.apply a x +
        FunctionalInequalities.Energy.LocalSlope.apply b x := by
  exact FunctionalInequalities.Energy.LocalSlope.apply_le_add hr₀ h

theorem emptyPerimeter {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) :
    FunctionalInequalities.KLS.MetricBV.perimeter ν (∅ : Set X) = 0 := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_empty ν

theorem finiteMeasureComplement {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    FunctionalInequalities.KLS.MetricBV.perimeter ν Bᶜ =
      FunctionalInequalities.KLS.MetricBV.perimeter ν B := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_compl_of_isFiniteMeasure ν B

theorem closedSupportComplement {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (ν : ProbabilityMeasure X) (B : Set (ν : Measure X).support) :
    FunctionalInequalities.KLS.MetricBV.perimeter
        (FunctionalInequalities.KLS.MetricBV.closedSupportLaw ν :
          Measure (ν : Measure X).support) Bᶜ =
      FunctionalInequalities.KLS.MetricBV.perimeter
        (FunctionalInequalities.KLS.MetricBV.closedSupportLaw ν :
          Measure (ν : Measure X).support) B := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_compl_closedSupportLaw ν B

theorem intrinsicComplement {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E)
    (B : Set (FunctionalInequalities.Probability.intrinsicMeasure μ :
      Measure (FunctionalInequalities.Probability.affineSupport μ).direction).support) :
    FunctionalInequalities.KLS.MetricBV.perimeter
        (FunctionalInequalities.KLS.MetricBV.intrinsicClosedSupportLaw μ : Measure _) Bᶜ =
      FunctionalInequalities.KLS.MetricBV.perimeter
        (FunctionalInequalities.KLS.MetricBV.intrinsicClosedSupportLaw μ : Measure _) B := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_compl_intrinsicClosedSupportLaw μ B

/-- A non-finite, unbounded carrier: the standard Gaussian law on the real line. -/
theorem gaussianRealComplement (B : Set ℝ) :
    FunctionalInequalities.KLS.MetricBV.perimeter (ProbabilityTheory.gaussianReal 0 1) Bᶜ =
      FunctionalInequalities.KLS.MetricBV.perimeter (ProbabilityTheory.gaussianReal 0 1) B := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_compl_of_isFiniteMeasure _ B

theorem infiniteMassObstruction {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) (h : ∀ S : Set X, Bornology.IsBounded S → ν Sᶜ = ⊤) :
    FunctionalInequalities.KLS.MetricBV.perimeter ν Set.univ = ⊤ := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_univ_eq_top_of_forall_isBounded ν h

/-- Finiteness of the measure cannot be dropped. -/
theorem lebesgueCounterexample :
    FunctionalInequalities.KLS.MetricBV.perimeter (volume : Measure ℝ) (∅ : Set ℝ)ᶜ ≠
      FunctionalInequalities.KLS.MetricBV.perimeter (volume : Measure ℝ) ∅ := by
  exact FunctionalInequalities.KLS.MetricBV.perimeter_compl_ne_real_volume

#print axioms slopeComparison
#print axioms emptyPerimeter
#print axioms finiteMeasureComplement
#print axioms closedSupportComplement
#print axioms intrinsicComplement
#print axioms gaussianRealComplement
#print axioms infiniteMassObstruction
#print axioms lebesgueCounterexample

end MetricBVComplementAudit
