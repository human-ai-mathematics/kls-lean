import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Strict proof client, promoted from external review task 01
(`build/audit/admg-locally-finite-eight-hour/external/claude/InfiniteMassGenericClient.lean`, sha256 prefix `101b10edebab2bca`; hypotheses unchanged).

The finite-measure instance carried by
several elementary public lemmas is superfluous. The following hold for every Borel measure
(including infinite total mass), proved here without `[IsFiniteMeasure ν]`, whereas the library
versions `minkowskiContent_le_upperMinkowskiContent`, `minkowskiContent_empty`,
`upperMinkowskiContent_empty`, `relaxedMinkowskiContent_le_liminf`,
`relaxedMinkowskiContent_le_relaxedUpperMinkowskiContent` require it. This is an API-scope
observation only; it does not affect any accepted endpoint. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace MinkowskiInfiniteMassGenericAudit
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem lower_le_upper (ν : Measure X) (B : Set X) :
    minkowskiContent ν B ≤ upperMinkowskiContent ν B := liminf_le_limsup

omit [BorelSpace X] in
theorem upper_empty (ν : Measure X) : upperMinkowskiContent ν (∅ : Set X) = 0 := by
  unfold upperMinkowskiContent
  simp [Metric.thickening_empty]

omit [BorelSpace X] in
theorem lower_empty (ν : Measure X) : minkowskiContent ν (∅ : Set X) = 0 :=
  le_antisymm ((lower_le_upper ν ∅).trans_eq (upper_empty ν)) bot_le

omit [BorelSpace X] in
theorem relaxed_le_relaxedUpper (ν : Measure X) (B : Set X) :
    relaxedMinkowskiContent ν B ≤ relaxedUpperMinkowskiContent ν B :=
  le_iInf fun A => (iInf_le _ A).trans
    (liminf_le_liminf (Eventually.of_forall fun n => lower_le_upper ν (A.1 n)))

/-- Empty target, infinite-mass Lebesgue measure: both relaxed contents and perimeter vanish
(the relaxed identity at the empty target is recovered at the published scope). -/
theorem emptyTarget_real :
    relaxedMinkowskiContent (volume : Measure ℝ) ∅ = 0 ∧
      relaxedUpperMinkowskiContent (volume : Measure ℝ) ∅ = 0 ∧
      perimeter (volume : Measure ℝ) ∅ = 0 := by
  let hc : MinkowskiApproximatingSequence (volume : Measure ℝ) ∅ :=
    ⟨fun _ => ∅, fun _ => MeasurableSet.empty, by simp⟩
  refine ⟨le_antisymm ((iInf_le _ hc).trans ?_) bot_le,
    le_antisymm ((iInf_le _ hc).trans ?_) bot_le, perimeter_empty _⟩
  · simp [hc, lower_empty]
  · simp [hc, upper_empty]

end MinkowskiInfiniteMassGenericAudit

#print axioms MinkowskiInfiniteMassGenericAudit.lower_le_upper
#print axioms MinkowskiInfiniteMassGenericAudit.lower_empty
#print axioms MinkowskiInfiniteMassGenericAudit.relaxed_le_relaxedUpper
#print axioms MinkowskiInfiniteMassGenericAudit.emptyTarget_real
