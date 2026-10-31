module

public import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation
public import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-! Strict proof clients for the ADMG Remark 3.5 alternative classes on proper spaces at
measurable finite-mass targets, for arbitrary Borel measures: the target-tail truncation
estimates, the compact-local diagonal perimeter bound, and the identification of the locally
Lipschitz (global `L¹`) and compact-local relaxations with the bounded-support perimeter.
Instances: Lebesgue measure (infinite total mass), counting measure on `ℝ` (not finite on
bounded sets), the zero measure, and the boundary at an infinite-mass target where the
compact-local relaxation vanishes but the perimeter is infinite. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace MetricBVLocalLipschitzTargetTailAudit
open FunctionalInequalities
open FunctionalInequalities.KLS.MetricBV

section Generic

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem compactLocalIdentity (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) :
    (⨅ f : CompactLocallyLipschitzApproximatingSequence ν B,
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop) = perimeter ν B :=
  compactLocallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB

theorem globalLocalIdentity (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) :
    (⨅ f : LocallyLipschitzApproximatingSequence ν B,
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop) = perimeter ν B :=
  locallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB

/-- All four relaxations of Remark 3.4/3.5 and Definition 3.3 agree at the target. -/
theorem allClassesAgree (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    compactLocallyLipschitzRelaxation ν B = locallyLipschitzRelaxation ν B ∧
      locallyLipschitzRelaxation ν B = lipschitzRelaxation ν B ∧
      lipschitzRelaxation ν B = perimeter ν B :=
  ⟨(compactLocallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).trans
      (locallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).symm,
    (locallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).trans
      (lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB).symm,
    lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB⟩

theorem compactLocalBound (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤)
    (f : CompactLocallyLipschitzApproximatingSequence ν B) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact_of_measure_lt_top ν hB hνB f.2.1 f.2.2

theorem truncationCost (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : LocallyLipschitz f)
    {B : Set X} (hB : MeasurableSet B) :
    cost ν (Test.truncateOfLocallyLipschitz x₀ R f hf) ≤
      (∫⁻ x, Energy.LocalSlope.apply f x ∂ν) +
        ((∫⁻ x in Metric.closedBall x₀ (R + 1), ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
          ν (B \ Metric.ball x₀ R)) :=
  cost_truncateOfLocallyLipschitz_le_target_tail ν x₀ R hf hB

theorem truncationDistance (ν : Measure X) (x₀ : X) (R : ℝ) {f : X → ℝ}
    (hf : LocallyLipschitz f) {B : Set X} (hB : MeasurableSet B) :
    indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ R f hf) B ≤
      (∫⁻ x in Metric.closedBall x₀ (R + 1), ‖f x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) +
        ν (B \ Metric.ball x₀ R) :=
  indicatorDistance_truncateOfLocallyLipschitz_le_target_tail ν x₀ R hf hB

theorem zeroMeasure {B : Set X} (hB : MeasurableSet B) :
    compactLocallyLipschitzRelaxation (0 : Measure X) B = perimeter 0 B :=
  compactLocallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top 0 hB (by simp)

end Generic

/-- Pointwise estimates hold for an arbitrary (not even continuous) function. -/
theorem pointwiseArbitrary (B : Set ℝ) (x : ℝ) :
    Energy.LocalSlope.apply (truncateFun (0 : ℝ) 2 (Set.indicator (Set.Ioi 0) 1)) x ≤
        Energy.LocalSlope.apply (Set.indicator (Set.Ioi (0 : ℝ)) 1) x +
          ((Metric.closedBall (0 : ℝ) (2 + 1)).indicator
              (fun y => ‖Set.indicator (Set.Ioi (0 : ℝ)) 1 y - B.indicator (1 : ℝ → ℝ) y‖ₑ) x +
            (B \ Metric.ball 0 2).indicator 1 x) ∧
      ‖truncateFun (0 : ℝ) 2 (Set.indicator (Set.Ioi 0) 1) x - B.indicator (1 : ℝ → ℝ) x‖ₑ ≤
        (Metric.closedBall (0 : ℝ) (2 + 1)).indicator
            (fun y => ‖Set.indicator (Set.Ioi (0 : ℝ)) 1 y - B.indicator (1 : ℝ → ℝ) y‖ₑ) x +
          (B \ Metric.ball 0 2).indicator 1 x :=
  ⟨apply_truncateFun_le_target_tail 0 2 _ B x, enorm_truncateFun_sub_le_target_tail 0 2 _ B x⟩

/-- Lebesgue measure: infinite total mass, interval target. -/
theorem lebesgueInterval : (volume : Measure ℝ) univ = ⊤ ∧
    compactLocallyLipschitzRelaxation (volume : Measure ℝ) (Icc 0 1) =
      perimeter (volume : Measure ℝ) (Icc 0 1) :=
  ⟨by simp, compactLocallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top volume
    measurableSet_Icc (by simp)⟩

/-- Counting measure on `ℝ` is outside the paper's finite-on-bounded hypothesis; the identity at
finite-mass targets still holds. -/
theorem countingMeasure :
    locallyLipschitzRelaxation (Measure.count : Measure ℝ) ({0} : Set ℝ) =
      perimeter Measure.count ({0} : Set ℝ) :=
  locallyLipschitzRelaxation_eq_perimeter_of_measure_lt_top _ (measurableSet_singleton 0)
    (by simp)

/-- The finite-target-mass premise is substantive: at the whole line the constant sequence
gives zero compact-local relaxation while the perimeter is `⊤`. -/
theorem infiniteMassBoundary :
    compactLocallyLipschitzRelaxation (volume : Measure ℝ) univ = 0 ∧
      perimeter (volume : Measure ℝ) univ = ⊤ := by
  constructor
  · let g : CompactLocallyLipschitzApproximatingSequence (volume : Measure ℝ) univ :=
      ⟨fun _ _ => 1, fun _ => (LipschitzWith.const (1 : ℝ)).locallyLipschitz, fun K _ => by simp⟩
    refine le_antisymm ((compactLocallyLipschitzRelaxation_le_liminf _ _ g).trans ?_) bot_le
    simp [g, Energy.LocalSlope.apply_const]
  · apply perimeter_univ_eq_top_of_forall_isBounded
    intro S hS
    obtain ⟨b, hb⟩ := hS.bddAbove
    refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
    exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)

end MetricBVLocalLipschitzTargetTailAudit

#print axioms MetricBVLocalLipschitzTargetTailAudit.compactLocalIdentity
#print axioms MetricBVLocalLipschitzTargetTailAudit.globalLocalIdentity
#print axioms MetricBVLocalLipschitzTargetTailAudit.allClassesAgree
#print axioms MetricBVLocalLipschitzTargetTailAudit.compactLocalBound
#print axioms MetricBVLocalLipschitzTargetTailAudit.truncationCost
#print axioms MetricBVLocalLipschitzTargetTailAudit.truncationDistance
#print axioms MetricBVLocalLipschitzTargetTailAudit.zeroMeasure
#print axioms MetricBVLocalLipschitzTargetTailAudit.pointwiseArbitrary
#print axioms MetricBVLocalLipschitzTargetTailAudit.lebesgueInterval
#print axioms MetricBVLocalLipschitzTargetTailAudit.countingMeasure
#print axioms MetricBVLocalLipschitzTargetTailAudit.infiniteMassBoundary
