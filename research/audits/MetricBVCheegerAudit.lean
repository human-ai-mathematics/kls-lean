import FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Independent full-signature clients for the equality of the half-mass and symmetric metric
BV Cheeger constants, with its boundary regimes: mass exactly one half, mass in `(1/2, 1)`
handled through the complement, empty admissible families (one-point space, zero intrinsic
dimension), conditional infinite-perimeter quotient checks for individual admissible sets and
for an all-infinite admissible family, an unbounded non-finite carrier and the closed intrinsic
support. No infinite-perimeter set is constructed and no BV--Minkowski identification is
stated. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace MetricBVCheegerAudit

open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem halfEqSymmetric (ν : ProbabilityMeasure X) :
    halfConstant ν = symmetricConstant ν := by
  exact halfConstant_eq_symmetricConstant ν

/-- A set of mass exactly one half is admissible for the half-mass convention. -/
theorem massOneHalf (ν : ProbabilityMeasure X) {B : Set X} (hB : MeasurableSet B)
    (hm : (ν : Measure X) B = 1 / 2) :
    symmetricConstant ν ≤ perimeter (ν : Measure X) B / (1 / 2) := by
  rw [← halfConstant_eq_symmetricConstant, ← hm]
  exact (iInf_le _ B).trans ((iInf_le _ hB).trans ((iInf_le _ (by rw [hm]; simp)).trans
    (iInf_le _ hm.le)))

/-- A set of mass in `(1/2, 1)` bounds the half-mass constant through the complementary mass. -/
theorem massAboveHalf (ν : ProbabilityMeasure X) {B : Set X} (hB : MeasurableSet B)
    (h0 : 1 / 2 < (ν : Measure X) B) (h1 : (ν : Measure X) B < 1) :
    halfConstant ν ≤ perimeter (ν : Measure X) B / (1 - (ν : Measure X) B) := by
  rw [halfConstant_eq_symmetricConstant]
  have hmin : min ((ν : Measure X) B) (1 - (ν : Measure X) B) = 1 - (ν : Measure X) B :=
    min_eq_right ((one_sub_lt_half_of_half_lt h0 h1.le).le.trans h0.le)
  have hpos : 0 < (ν : Measure X) B := (ENNReal.half_pos one_ne_zero).trans h0
  calc symmetricConstant ν
      ≤ perimeter (ν : Measure X) B / min ((ν : Measure X) B) (1 - (ν : Measure X) B) := by
        unfold symmetricConstant
        exact iInf₂_le_of_le B hB (iInf₂_le_of_le hpos h1 le_rfl)
    _ = perimeter (ν : Measure X) B / (1 - (ν : Measure X) B) := by rw [hmin]

/-- Conditional quotient check: an admissible symmetric test set of infinite perimeter has
infinite symmetric quotient, which bounds the constant. This does not construct such a set. -/
theorem infiniteSymmetricQuotient (ν : ProbabilityMeasure X) {B : Set X} (hB : MeasurableSet B)
    (h0 : 0 < (ν : Measure X) B) (h1 : (ν : Measure X) B < 1)
    (hper : perimeter (ν : Measure X) B = ⊤) :
    symmetricConstant ν ≤
        perimeter (ν : Measure X) B / min ((ν : Measure X) B) (1 - (ν : Measure X) B) ∧
      perimeter (ν : Measure X) B / min ((ν : Measure X) B) (1 - (ν : Measure X) B) = ⊤ := by
  refine ⟨?_, ?_⟩
  · unfold symmetricConstant
    exact iInf₂_le_of_le B hB (iInf₂_le_of_le h0 h1 le_rfl)
  · rw [hper]
    exact ENNReal.top_div_of_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
      ((min_le_left _ _).trans h1.le))

/-- Conditional quotient check: an admissible half-mass test set of infinite perimeter has
infinite half-mass quotient, which bounds the constant. This does not construct such a set. -/
theorem infiniteHalfQuotient (ν : ProbabilityMeasure X) {B : Set X} (hB : MeasurableSet B)
    (h0 : 0 < (ν : Measure X) B) (hm : (ν : Measure X) B ≤ 1 / 2)
    (hper : perimeter (ν : Measure X) B = ⊤) :
    halfConstant ν ≤ perimeter (ν : Measure X) B / (ν : Measure X) B ∧
      perimeter (ν : Measure X) B / (ν : Measure X) B = ⊤ := by
  refine ⟨?_, ?_⟩
  · unfold halfConstant
    exact iInf₂_le_of_le B hB (iInf₂_le_of_le h0 hm le_rfl)
  · rw [hper]
    exact ENNReal.top_div_of_ne_top (ne_top_of_le_ne_top (by simp) hm)

/-- If every admissible symmetric test set (measurable, `0 < ν B < 1`) has infinite perimeter,
both constants are infinite. The quantifier excludes the empty set and other inadmissible sets,
so the premise does not contradict `perimeter_empty`. -/
theorem infiniteAdmissibleFamily (ν : ProbabilityMeasure X)
    (h : ∀ B : Set X, MeasurableSet B → 0 < (ν : Measure X) B → (ν : Measure X) B < 1 →
      perimeter (ν : Measure X) B = ⊤) :
    halfConstant ν = ⊤ ∧ symmetricConstant ν = ⊤ := by
  have hs : symmetricConstant ν = ⊤ := by
    refine iInf_eq_top.mpr fun B => iInf_eq_top.mpr fun hB => iInf_eq_top.mpr fun h0 =>
      iInf_eq_top.mpr fun h1 => (infiniteSymmetricQuotient ν hB h0 h1 (h B hB h0 h1)).2
  exact ⟨(halfConstant_eq_symmetricConstant ν).trans hs, hs⟩

/-- Consistency only: the admissible-family premise is satisfiable, here vacuously because a
one-point probability space has no admissible set. This is not an infinite-perimeter example. -/
theorem admissibleFamilyPremiseOnePoint (ν : ProbabilityMeasure Unit) :
    ∀ B : Set Unit, MeasurableSet B → 0 < (ν : Measure Unit) B → (ν : Measure Unit) B < 1 →
      perimeter (ν : Measure Unit) B = ⊤ := by
  intro B _ h0 h1
  exfalso
  rcases Set.eq_empty_or_nonempty B with hBe | ⟨x, hx⟩
  · rw [hBe, measure_empty] at h0
    exact lt_irrefl 0 h0
  · have hBu : B = Set.univ := Set.eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
    rw [hBu, measure_univ] at h1
    exact lt_irrefl 1 h1

/-- A one-point space has no admissible set in either convention. -/
theorem onePoint (ν : ProbabilityMeasure Unit) :
    halfConstant ν = ⊤ ∧ symmetricConstant ν = ⊤ := by
  exact ⟨halfConstant_eq_top_of_subsingleton ν, symmetricConstant_eq_top_of_subsingleton ν⟩

/-- An unbounded, non-finite carrier. -/
theorem gaussianReal :
    halfConstant (⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) =
      symmetricConstant
        (⟨ProbabilityTheory.gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) := by
  exact halfConstant_eq_symmetricConstant _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

theorem intrinsicEquality (μ : ProbabilityMeasure E) :
    intrinsicHalfConstant μ = symmetricConstant (intrinsicClosedSupportLaw μ) := by
  exact intrinsicHalfConstant_eq_symmetricConstant μ

/-- Zero-dimensional affine support: the symmetric convention also has an empty family. -/
theorem intrinsicZeroDimension (μ : ProbabilityMeasure E)
    (h : Module.finrank ℝ (FunctionalInequalities.Probability.affineSupport μ).direction = 0) :
    symmetricConstant (intrinsicClosedSupportLaw μ) = ⊤ := by
  rw [← intrinsicHalfConstant_eq_symmetricConstant]
  exact intrinsicHalfConstant_eq_top_of_finrank_zero μ h

#print axioms halfEqSymmetric
#print axioms massOneHalf
#print axioms massAboveHalf
#print axioms infiniteSymmetricQuotient
#print axioms infiniteHalfQuotient
#print axioms infiniteAdmissibleFamily
#print axioms admissibleFamilyPremiseOnePoint
#print axioms onePoint
#print axioms gaussianReal
#print axioms intrinsicEquality
#print axioms intrinsicZeroDimension

end MetricBVCheegerAudit
