import FunctionalInequalities.Analysis.MetricBV.Basic
import FunctionalInequalities.Analysis.MetricBV.Complement
import FunctionalInequalities.Analysis.MetricBV.Transport
import FunctionalInequalities.Probability.AffineSupport

/-!
# Metric BV Cheeger constants on the closed intrinsic support

These are infima of quotients of the actual metric BV perimeter. The empty
admissible family has value `⊤`. The half-mass and symmetric conventions agree for every
probability measure (`halfConstant_eq_symmetricConstant`), by complement symmetry of the
perimeter for finite measures; in particular on the closed intrinsic support
(`intrinsicHalfConstant_eq_symmetricConstant`). They are distinct from the existing lower
Minkowski-content infimum until a relaxation and recovery comparison is proved.
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

/-- Complement symmetry of the metric BV perimeter on the closed intrinsic support. -/
theorem perimeter_compl_intrinsicClosedSupportLaw {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    perimeter (intrinsicClosedSupportLaw μ : Measure _) Bᶜ =
      perimeter (intrinsicClosedSupportLaw μ : Measure _) B :=
  perimeter_compl_closedSupportLaw _ B

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

section HalfSymmetric

omit [MetricSpace X] [BorelSpace X] in
/-- A mass at most one half is at most the complementary mass. -/
theorem le_one_sub_of_le_half {m : ENNReal} (h : m ≤ 1 / 2) : m ≤ 1 - m := by
  have hm : 1 / 2 ≤ 1 - m := by
    calc (1 : ENNReal) / 2 = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
      _ ≤ 1 - m := tsub_le_tsub_left h 1
  exact h.trans hm

omit [MetricSpace X] [BorelSpace X] in
/-- A mass strictly above one half has complementary mass strictly below one half. -/
theorem one_sub_lt_half_of_half_lt {m : ENNReal} (h : 1 / 2 < m) (h1 : m ≤ 1) :
    1 - m < 1 / 2 := by
  have hm : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top h1
  rw [ENNReal.sub_lt_iff_lt_right hm h1]
  calc (1 : ENNReal) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
    _ < 1 / 2 + m := ENNReal.add_lt_add_left (by simp) h

/-- The half-mass and symmetric BV Cheeger constants coincide for every probability measure
on a metric space. A symmetric test set of mass above one half is replaced by its complement,
which has the same perimeter by `perimeter_compl_of_isFiniteMeasure`; the boundary mass `1/2`,
empty admissible families and infinite perimeters need no separate hypothesis. -/
theorem halfConstant_eq_symmetricConstant (ν : ProbabilityMeasure X) :
    halfConstant ν = symmetricConstant ν := by
  apply le_antisymm
  · refine le_iInf fun B => le_iInf fun hB => le_iInf fun h0 => le_iInf fun h1 => ?_
    by_cases hm : (ν : Measure X) B ≤ 1 / 2
    · rw [min_eq_left (le_one_sub_of_le_half hm)]
      exact (iInf_le _ B).trans ((iInf_le _ hB).trans ((iInf_le _ h0).trans (iInf_le _ hm)))
    · have hlt : 1 / 2 < (ν : Measure X) B := not_le.mp hm
      have hle1 : (ν : Measure X) B ≤ 1 := prob_le_one
      have hC : (ν : Measure X) Bᶜ = 1 - (ν : Measure X) B := prob_compl_eq_one_sub hB
      have hC0 : 0 < (ν : Measure X) Bᶜ := by rw [hC]; exact tsub_pos_of_lt h1
      have hC1 : (ν : Measure X) Bᶜ ≤ 1 / 2 := by
        rw [hC]; exact (one_sub_lt_half_of_half_lt hlt hle1).le
      have hmin : min ((ν : Measure X) B) (1 - (ν : Measure X) B) = 1 - (ν : Measure X) B :=
        min_eq_right ((one_sub_lt_half_of_half_lt hlt hle1).le.trans hlt.le)
      calc halfConstant ν
          ≤ perimeter (ν : Measure X) Bᶜ / (ν : Measure X) Bᶜ :=
            (iInf_le _ Bᶜ).trans ((iInf_le _ hB.compl).trans
              ((iInf_le _ hC0).trans (iInf_le _ hC1)))
        _ = perimeter (ν : Measure X) B / min ((ν : Measure X) B) (1 - (ν : Measure X) B) := by
            rw [perimeter_compl_of_isFiniteMeasure, hC, hmin]
  · refine le_iInf fun B => le_iInf fun hB => le_iInf fun h0 => le_iInf fun hm => ?_
    have h1 : (ν : Measure X) B < 1 :=
      hm.trans_lt (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top |>.trans_eq' (by simp))
    calc symmetricConstant ν
        ≤ perimeter (ν : Measure X) B / min ((ν : Measure X) B) (1 - (ν : Measure X) B) :=
          (iInf_le _ B).trans ((iInf_le _ hB).trans ((iInf_le _ h0).trans (iInf_le _ h1)))
      _ = perimeter (ν : Measure X) B / (ν : Measure X) B := by
          rw [min_eq_left (le_one_sub_of_le_half hm)]

/-- On a one-point probability space the symmetric BV Cheeger constant is `⊤`. -/
theorem symmetricConstant_eq_top_of_subsingleton [Subsingleton X]
    (ν : ProbabilityMeasure X) : symmetricConstant ν = ⊤ := by
  rw [← halfConstant_eq_symmetricConstant, halfConstant_eq_top_of_subsingleton]

end HalfSymmetric

/-- On the closed intrinsic support, the literature half-mass BV Cheeger constant equals the
symmetric one. -/
theorem intrinsicHalfConstant_eq_symmetricConstant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) :
    intrinsicHalfConstant μ = symmetricConstant (intrinsicClosedSupportLaw μ) :=
  halfConstant_eq_symmetricConstant _

end FunctionalInequalities.KLS.MetricBV
