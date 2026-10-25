import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Strict proof clients for ADMG Lemma 2.1's equality of the relaxed lower and upper Minkowski
contents under arbitrary Borel measures at measurable finite-mass targets, with the
near-minimum selection and global-`L¹` lower semicontinuity of the relaxed upper content.
Instances: Lebesgue measure (infinite total mass), counting measure on `ℝ` (not finite on
bounded sets, outside the paper's standing hypothesis), the zero measure, an approximating
sequence with an infinite-mass finite prefix, and a nonmeasurable limit for the
semicontinuity. No perimeter identity is asserted for these measures. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace MinkowskiLemma21ArbitraryMeasureAudit
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The equality written as the two unfolded infima over the unchanged class. -/
theorem unfoldedEquality (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop) =
      ⨅ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => minkowskiContent ν (A.1 n)) atTop :=
  relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_measure_lt_top ν hB hνB

section MinkowskiSemicontinuity

omit [BorelSpace X]
/-- Semicontinuity needs neither measurability nor finite mass of the limit set. -/
theorem semicontinuity (ν : Measure X) (B : Set X) (A : MinkowskiApproximatingSequence ν B) :
    relaxedUpperMinkowskiContent ν B ≤
      liminf (fun n => relaxedUpperMinkowskiContent ν (A.1 n)) atTop :=
  relaxedUpperMinkowskiContent_le_liminf_of_tendsto ν A.2.1 A.2.2

theorem nearMinimum (ν : Measure X) (B : Set X) {a ε : ENNReal}
    (ha : relaxedUpperMinkowskiContent ν B < a) (hε : 0 < ε) :
    ∃ C : Set X, MeasurableSet C ∧
      (∫⁻ x, ‖C.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν) < ε ∧
      upperMinkowskiContent ν C < a :=
  exists_upperApproximation_lt ν B ha hε

end MinkowskiSemicontinuity

/-- Infinite-mass Lebesgue measure on the line. -/
theorem lebesgueInterval : (volume : Measure ℝ) univ = ⊤ ∧
    relaxedUpperMinkowskiContent (volume : Measure ℝ) (Icc 0 1) =
      relaxedMinkowskiContent (volume : Measure ℝ) (Icc 0 1) :=
  ⟨by simp, relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_measure_lt_top volume
    measurableSet_Icc (by simp)⟩

/-- Counting measure on `ℝ` is not finite on bounded Borel sets, so the earlier
finite-on-bounded identity does not apply; the arbitrary-measure equality does. -/
theorem countingMeasure :
    ¬ (∀ s : Set ℝ, Bornology.IsBounded s → MeasurableSet s → (Measure.count : Measure ℝ) s < ⊤) ∧
      relaxedUpperMinkowskiContent (Measure.count : Measure ℝ) ({0} : Set ℝ) =
        relaxedMinkowskiContent (Measure.count : Measure ℝ) ({0} : Set ℝ) := by
  refine ⟨fun h => ?_, relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_measure_lt_top _
    (measurableSet_singleton 0) (by simp)⟩
  have hinf : (Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  have := h (Icc 0 1) (Metric.isBounded_Icc 0 1) measurableSet_Icc
  rw [Measure.count_apply_infinite hinf] at this
  exact lt_irrefl _ this

theorem zeroMeasure {B : Set X} (hB : MeasurableSet B) :
    relaxedUpperMinkowskiContent (0 : Measure X) B = relaxedMinkowskiContent 0 B :=
  relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_measure_lt_top 0 hB (by simp)

/-- An approximating sequence with an infinite-mass first term is admissible, and the
semicontinuity bound applies to it. -/
def withInfinitePrefix : MinkowskiApproximatingSequence (volume : Measure ℝ) (Icc 0 1) :=
  ⟨fun n => if n = 0 then univ else Icc 0 1, fun n => by
    show MeasurableSet (if n = 0 then (univ : Set ℝ) else Icc 0 1)
    split_ifs
    exacts [MeasurableSet.univ, measurableSet_Icc], by
    refine tendsto_atTop_of_eventually_const (i₀ := 1) fun n hn => ?_
    show ∫⁻ x, ‖(if n = 0 then (univ : Set ℝ) else Icc 0 1).indicator (1 : ℝ → ℝ) x -
      (Icc (0 : ℝ) 1).indicator 1 x‖ₑ ∂volume = 0
    rw [if_neg (by omega)]
    simp⟩

theorem infinitePrefix :
    relaxedUpperMinkowskiContent (volume : Measure ℝ) (Icc 0 1) ≤
      liminf (fun n => relaxedUpperMinkowskiContent volume (withInfinitePrefix.1 n)) atTop :=
  relaxedUpperMinkowskiContent_le_liminf_of_tendsto volume withInfinitePrefix.2.1
    withInfinitePrefix.2.2

end MinkowskiLemma21ArbitraryMeasureAudit

#print axioms MinkowskiLemma21ArbitraryMeasureAudit.unfoldedEquality
#print axioms MinkowskiLemma21ArbitraryMeasureAudit.semicontinuity
#print axioms MinkowskiLemma21ArbitraryMeasureAudit.nearMinimum
#print axioms MinkowskiLemma21ArbitraryMeasureAudit.lebesgueInterval
#print axioms MinkowskiLemma21ArbitraryMeasureAudit.countingMeasure
#print axioms MinkowskiLemma21ArbitraryMeasureAudit.zeroMeasure
#print axioms MinkowskiLemma21ArbitraryMeasureAudit.infinitePrefix
