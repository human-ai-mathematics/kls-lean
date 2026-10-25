import FunctionalInequalities.Analysis.MetricBV.Basic
import FunctionalInequalities.Analysis.MetricBV.Approximation
import FunctionalInequalities.Analysis.MetricBV.Complement

/-!
# Metric BV subset restriction and closed-support laws
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X]
section SubsetRestriction

/-! ### Restriction to a measurable subset

A test restricts to a test on a subset with its induced metric; its slope does not increase
(`Energy.LocalSlope.apply_comp_le_of_isometry`), so for the pulled-back measure
`ν.comap Subtype.val` neither the cost nor the indicator distance increases, and the perimeter of
the trace `Subtype.val ⁻¹' B` is at most that of `B`. -/

/-- The restriction of a test to a subset, with the induced metric. -/
def Test.restrict (f : Test X) (s : Set X) : Test s where
  toFun := fun z => f z
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    exact ⟨K * 1, hK.comp (LipschitzWith.subtype_val s)⟩
  bounded := f.bounded.subset (by
    rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩)
  boundedSupport := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 f.boundedSupport
    exact Metric.isBounded_iff.2 ⟨C, fun z hz w hw => hC hz hw⟩

theorem cost_restrict_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s) (f : Test X) :
    cost (ν.comap Subtype.val) (f.restrict s) ≤ cost ν f := by
  unfold cost
  calc ∫⁻ z, Energy.LocalSlope.apply (f.restrict s) z ∂(ν.comap Subtype.val)
      ≤ ∫⁻ z : s, Energy.LocalSlope.apply f z ∂(ν.comap Subtype.val) :=
        lintegral_mono fun z => Energy.LocalSlope.apply_comp_le_of_isometry isometry_subtype_coe f z
    _ = ∫⁻ x in s, Energy.LocalSlope.apply f x ∂ν := lintegral_subtype_comap hs _
    _ ≤ ∫⁻ x, Energy.LocalSlope.apply f x ∂ν := setLIntegral_le_lintegral _ _

theorem indicatorDistance_restrict_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s)
    (f : Test X) (B : Set X) :
    indicatorDistance (ν.comap Subtype.val) (f.restrict s) (Subtype.val ⁻¹' B) ≤
      indicatorDistance ν f B := by
  unfold indicatorDistance
  have hpt : ∀ z : s, ‖(f.restrict s) z - (Subtype.val ⁻¹' B).indicator (1 : s → ℝ) z‖ₑ =
      ‖f z - B.indicator (1 : X → ℝ) z‖ₑ := fun z => by
    by_cases hz : (z : X) ∈ B
    · rw [Set.indicator_of_mem (show z ∈ Subtype.val ⁻¹' B from hz), Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ Subtype.val ⁻¹' B from hz),
        Set.indicator_of_notMem hz]
      rfl
  calc ∫⁻ z, ‖(f.restrict s) z - (Subtype.val ⁻¹' B).indicator (1 : s → ℝ) z‖ₑ
        ∂(ν.comap Subtype.val)
      = ∫⁻ z : s, ‖f z - B.indicator (1 : X → ℝ) z‖ₑ ∂(ν.comap Subtype.val) := lintegral_congr hpt
    _ = ∫⁻ x in s, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν :=
        lintegral_subtype_comap hs (fun x => ‖f x - B.indicator (1 : X → ℝ) x‖ₑ)
    _ ≤ ∫⁻ x, ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν := setLIntegral_le_lintegral _ _

/-- The restriction of an actual approximating sequence of `B` approximates the trace of `B`. -/
def ApproximatingSequence.restrict {ν : Measure X} {B : Set X} {s : Set X}
    (hs : MeasurableSet s) (g : ApproximatingSequence ν B) :
    ApproximatingSequence (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) :=
  ⟨fun n => (g.1 n).restrict s,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds g.2 (fun _ => zero_le)
      fun n => indicatorDistance_restrict_le ν hs (g.1 n) B⟩

/-- Restriction to a measurable subset does not increase the perimeter. An empty ambient
approximation class gives `⊤` on the right. -/
theorem perimeter_comap_subtype_le (ν : Measure X) {s : Set X} (hs : MeasurableSet s)
    (B : Set X) :
    perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) ≤ perimeter ν B := by
  show _ ≤ ⨅ g : ApproximatingSequence ν B, liminf (fun n => cost ν (g.1 n)) atTop
  refine le_iInf fun g => ?_
  calc perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B)
      ≤ liminf (fun n => cost (ν.comap (Subtype.val : s → X)) ((g.restrict hs).1 n)) atTop :=
        perimeter_le_sequence _ _ _
    _ ≤ liminf (fun n => cost ν (g.1 n)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => cost_restrict_le ν hs (g.1 n))

/-- Reverse comparison under a nonexpansive retraction onto a full-mass measurable subset: for an
actual approximating sequence of the trace, the composed functions `g n ∘ r` are globally
Lipschitz (in general without bounded support, so not tests); full mass moves their `L¹` errors
and slope integrals to the subset, where they are the trace errors and at most the trace costs,
and the finite-measure Lipschitz bridge bounds the perimeter. An empty trace class gives `⊤`. -/
theorem perimeter_le_comap_subtype_of_retraction (ν : Measure X) [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) (B : Set X) :
    perimeter ν B ≤ perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) := by
  have hres : ν.restrict s = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hfull)
  have hmove : ∀ h : X → ENNReal,
      ∫⁻ x, h x ∂ν = ∫⁻ z : s, h z ∂(ν.comap (Subtype.val : s → X)) := fun h => by
    rw [lintegral_subtype_comap hs h, hres]
  show _ ≤ ⨅ g : ApproximatingSequence (ν.comap (Subtype.val : s → X))
      ((Subtype.val : s → X) ⁻¹' B),
    liminf (fun n => cost (ν.comap (Subtype.val : s → X)) (g.1 n)) atTop
  refine le_iInf fun g => ?_
  have hF : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (fun x => g.1 n (r x)) := fun n => by
    obtain ⟨K, hK⟩ := (g.1 n).lipschitz
    exact ⟨K * 1, hK.comp hr⟩
  have hdist : ∀ n, ∫⁻ x, ‖g.1 n (r x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν =
      indicatorDistance (ν.comap (Subtype.val : s → X)) (g.1 n) ((Subtype.val : s → X) ⁻¹' B) :=
    fun n => by
      rw [hmove (fun x => ‖g.1 n (r x) - B.indicator (1 : X → ℝ) x‖ₑ)]
      unfold indicatorDistance
      refine lintegral_congr fun z => ?_
      simp only [hrs]
      by_cases hz : (z : X) ∈ B
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ Subtype.val ⁻¹' B from hz)]
        rfl
      · rw [Set.indicator_of_notMem hz,
          Set.indicator_of_notMem (show z ∉ Subtype.val ⁻¹' B from hz)]
  have hcost : ∀ n, ∫⁻ x, Energy.LocalSlope.apply (fun x => g.1 n (r x)) x ∂ν ≤
      cost (ν.comap (Subtype.val : s → X)) (g.1 n) := fun n => by
    rw [hmove (fun x => Energy.LocalSlope.apply (fun x => g.1 n (r x)) x)]
    unfold cost
    refine lintegral_mono fun z => ?_
    have h := Energy.LocalSlope.apply_comp_le_of_lipschitzWith_one hr (g.1 n) (z : X)
    rw [hrs] at h
    exact h
  calc perimeter ν B
      ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (fun x => g.1 n (r x)) x ∂ν) atTop :=
        perimeter_le_liminf_of_lipschitz ν hF ((tendsto_congr hdist).2 g.2)
    _ ≤ liminf (fun n => cost (ν.comap (Subtype.val : s → X)) (g.1 n)) atTop :=
        liminf_le_liminf (Eventually.of_forall hcost)

/-- Perimeter equality under a nonexpansive retraction onto a full-mass measurable subset. -/
theorem perimeter_eq_comap_subtype_of_retraction (ν : Measure X) [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfull : ν sᶜ = 0) {r : X → s} (hr : LipschitzWith 1 r)
    (hrs : ∀ z : s, r z = z) (B : Set X) :
    perimeter ν B = perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) :=
  le_antisymm (perimeter_le_comap_subtype_of_retraction ν hs hfull hr hrs B)
    (perimeter_comap_subtype_le ν hs B)

end SubsetRestriction

section ClosedSupport

variable [SecondCountableTopology X]

/-- The actual law on its closed measure support, with the induced metric. -/
def closedSupportLaw (ν : ProbabilityMeasure X) : ProbabilityMeasure (ν : Measure X).support := by
  letI : IsProbabilityMeasure
      (Measure.comap (Subtype.val : (ν : Measure X).support → X) (ν : Measure X)) := by
    refine ⟨?_⟩
    rw [comap_subtype_coe_apply (ν : Measure X).isClosed_support.measurableSet]
    simp only [Set.image_univ, Subtype.range_coe_subtype]
    change (ν : Measure X) (ν : Measure X).support = 1
    have hdiff : (Set.univ : Set X) \ (ν : Measure X).support =
        (ν : Measure X).supportᶜ := by ext x; simp
    rw [measure_eq_measure_of_null_sdiff (Set.subset_univ _)
      (by rw [hdiff]; exact Measure.measure_compl_support)]
    exact measure_univ
  exact ⟨Measure.comap Subtype.val (ν : Measure X), inferInstance⟩

/-- Set masses for the restricted law are measured by the original law on the
corresponding set of points in the closed support. -/
theorem closedSupportLaw_apply (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    (closedSupportLaw ν : Measure (ν : Measure X).support) B =
      (ν : Measure X) (Subtype.val '' B) := by
  change Measure.comap Subtype.val (ν : Measure X) B = _
  exact comap_subtype_coe_apply (ν : Measure X).isClosed_support.measurableSet _ _

/-- The trace of a set on the closed support has the mass of the set: the support carries all
mass. -/
theorem closedSupportLaw_preimage (ν : ProbabilityMeasure X) (B : Set X) :
    (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) =
      (ν : Measure X) B := by
  rw [closedSupportLaw_apply, Subtype.image_preimage_coe, Set.inter_comm,
    measure_inter_conull Measure.measure_compl_support]

/-- Complement symmetry on the closed support of a probability law, whose carrier is in
general neither finite nor bounded. -/
theorem perimeter_compl_closedSupportLaw (ν : ProbabilityMeasure X)
    (B : Set (ν : Measure X).support) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) Bᶜ =
      perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) B :=
  perimeter_compl_of_isFiniteMeasure _ B

/-- Restriction to the closed measure support does not increase the metric BV perimeter. -/
theorem perimeter_closedSupportLaw_le (ν : ProbabilityMeasure X) (B : Set X) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) ≤
      perimeter (ν : Measure X) B :=
  perimeter_comap_subtype_le _ (ν : Measure X).isClosed_support.measurableSet B

end ClosedSupport

end FunctionalInequalities.KLS.MetricBV
