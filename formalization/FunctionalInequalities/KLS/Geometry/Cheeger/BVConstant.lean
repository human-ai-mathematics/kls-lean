import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV
import FunctionalInequalities.Probability.AffineSupport

/-!
# Metric BV Cheeger constants on the closed intrinsic support

These are infima of quotients of the actual metric BV perimeter. The empty
admissible family has value `⊤`. They are distinct from the existing lower
Minkowski-content infimum until a recovery comparison is proved.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- De Ponti--Mondino's half-mass convention, excluding zero mass. -/
def halfConstant (ν : ProbabilityMeasure X) : ENNReal :=
  ⨅ (B : Set X) (_ : MeasurableSet B)
    (_ : 0 < (ν : Measure X) B) (_ : (ν : Measure X) B ≤ 1 / 2),
      perimeter (ν : Measure X) B / (ν : Measure X) B

/-- The symmetric convention used in the KLS isoperimetry frontend. -/
def symmetricConstant (ν : ProbabilityMeasure X) : ENNReal :=
  ⨅ (B : Set X) (_ : MeasurableSet B)
    (_ : 0 < (ν : Measure X) B) (_ : (ν : Measure X) B < 1),
      perimeter (ν : Measure X) B /
        min ((ν : Measure X) B) (1 - (ν : Measure X) B)

/-- The actual restricted probability law on the closed support of the intrinsic
law, with its induced distance. -/
def intrinsicClosedSupportLaw {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support :=
  closedSupportLaw (Probability.intrinsicMeasure μ)

/-- The literature BV Cheeger constant on the closed intrinsic support. -/
def intrinsicHalfConstant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) : ENNReal :=
  halfConstant (intrinsicClosedSupportLaw μ)

/-- A one-point probability space has no positive-mass half-mass test set. -/
theorem halfConstant_eq_top_of_subsingleton [Subsingleton X]
    (ν : ProbabilityMeasure X) : halfConstant ν = ⊤ := by
  unfold halfConstant
  refine iInf_eq_top.mpr fun B => ?_
  by_cases hB : MeasurableSet B
  · rw [iInf_pos hB]
    rcases Set.eq_empty_or_nonempty B with hBe | ⟨x, hx⟩
    · subst hBe
      simp only [measure_empty]
      exact iInf_neg (lt_irrefl 0)
    · have hBu : B = Set.univ := Set.eq_univ_of_forall fun y => by
        rwa [Subsingleton.elim y x]
      subst hBu
      rw [measure_univ, iInf_pos (by norm_num : (0 : ENNReal) < 1)]
      exact iInf_neg (by norm_num : ¬ (1 : ENNReal) ≤ 1 / 2)
  · exact iInf_neg hB

set_option linter.style.haveILetI false in
/-- Zero-dimensional affine support yields the empty BV Cheeger test family. -/
theorem intrinsicHalfConstant_eq_top_of_finrank_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (μ : ProbabilityMeasure E)
    (h : Module.finrank ℝ (Probability.affineSupport μ).direction = 0) :
    intrinsicHalfConstant μ = ⊤ := by
  haveI : Subsingleton (Probability.affineSupport μ).direction :=
    Module.finrank_zero_iff.mp h
  exact halfConstant_eq_top_of_subsingleton _

end FunctionalInequalities.KLS.MetricBV
