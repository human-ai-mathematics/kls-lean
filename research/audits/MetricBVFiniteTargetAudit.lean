import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation

/-! Finite-target-mass bounded-support reduction, without finite total mass or properness.
The actual globally Lipschitz/global-L1 class is unfolded in the reduction client. Real
Lebesgue measure on an interval is a concrete infinite-total-mass instance. The whole-line
counterexample shows that finite target mass cannot be removed from the relaxation identity:
unrestricted globally Lipschitz approximation has zero cost but bounded-support BV is infinite.
No Minkowski relaxation or endpoint is asserted by this client. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MetricBVFiniteTargetAudit
open FunctionalInequalities FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The real approximating class and actual L1 limit, at arbitrary total mass. -/
theorem reduction (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤)
    {f : ℕ → X → ℝ} (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    ∃ g : ℕ → Test X,
      Tendsto (fun n => indicatorDistance ν (g n) B) atTop (𝓝 0) ∧
      liminf (fun n => cost ν (g n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  obtain ⟨g, hg⟩ := exists_approximatingSequence_of_lipschitz_of_measure_lt_top ν hB hνB hf hconv
  exact ⟨g.1, g.2, hg⟩

theorem actualRelaxation (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) :
    (⨅ f : LipschitzApproximatingSequence ν B,
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop) = perimeter ν B :=
  lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν hB hνB

/-- Both errors vanish for the actual fixed-radius construction. -/
theorem fixedRadii (ν : Measure X) (x₀ : X) {B : Set X}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncate x₀ n (f n) (hf n)) B)
      atTop (𝓝 0) ∧
      liminf (fun n : ℕ => cost ν (Test.truncate x₀ n (f n) (hf n))) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
  ⟨tendsto_indicatorDistance_truncate_of_measure_lt_top ν x₀ hB hνB hf hconv,
    liminf_cost_truncate_le_of_measure_lt_top ν x₀ hB hνB hf hconv⟩

/-- An interval of finite mass under an actual infinite-total-mass measure. -/
theorem realInterval :
    (volume : Measure ℝ) univ = ⊤ ∧
      lipschitzRelaxation volume (Icc (0 : ℝ) 1) = perimeter volume (Icc (0 : ℝ) 1) := by
  refine ⟨by simp, lipschitzRelaxation_eq_perimeter_of_measure_lt_top volume measurableSet_Icc ?_⟩
  simp

/-- An actual unbounded finite-mass target: natural-number points have zero Lebesgue mass. -/
theorem unboundedFiniteMassTarget :
    ¬Bornology.IsBounded (Set.range fun n : ℕ => (n : ℝ)) ∧
      (volume : Measure ℝ) (Set.range fun n : ℕ => (n : ℝ)) = 0 ∧
      lipschitzRelaxation volume (Set.range fun n : ℕ => (n : ℝ)) =
        perimeter volume (Set.range fun n : ℕ => (n : ℝ)) := by
  have hc := Set.countable_range (fun n : ℕ => (n : ℝ))
  have hmass := hc.measure_zero (volume : Measure ℝ)
  refine ⟨?_, hmass,
    lipschitzRelaxation_eq_perimeter_of_measure_lt_top volume hc.measurableSet ?_⟩
  · intro hb
    obtain ⟨b, hbound⟩ := hb.bddAbove
    obtain ⟨n, hn⟩ := exists_nat_gt b
    exact (not_le_of_gt hn) (hbound ⟨n, rfl⟩)
  · rw [hmass]
    exact ENNReal.zero_lt_top

/-- A zero measure and arbitrary measurable target (no mass or carrier restriction). -/
theorem zeroMeasure {B : Set X} (hB : MeasurableSet B) :
    lipschitzRelaxation (0 : Measure X) B = perimeter (0 : Measure X) B :=
  lipschitzRelaxation_eq_perimeter_of_measure_lt_top 0 hB (by simp)

/-- Existing finite-measure arbitrary-target scope, including nonmeasurable targets. -/
theorem finiteRegression (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    lipschitzRelaxation ν B = perimeter ν B := lipschitzRelaxation_eq_perimeter ν B

/-- The empty carrier is retained by the new finite-target bridge. -/
theorem emptyCarrier (ν : Measure Empty) :
    lipschitzRelaxation ν (univ : Set Empty) = perimeter ν (univ : Set Empty) :=
  lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν MeasurableSet.univ
    (by simp [Measure.eq_zero_of_isEmpty ν])

/-- The finite-target-mass premise is substantive: the whole real line separates the classes. -/
theorem infiniteMassTargetCounterexample :
    lipschitzRelaxation (volume : Measure ℝ) univ = 0 ∧ perimeter (volume : Measure ℝ) univ = ⊤ := by
  constructor
  · let g : LipschitzApproximatingSequence (volume : Measure ℝ) univ :=
      ⟨fun _ _ => 1, fun _ => ⟨0, LipschitzWith.const 1⟩, by simp⟩
    have h := lipschitzRelaxation_le_liminf (volume : Measure ℝ) univ g
    exact le_antisymm (h.trans_eq (by simp [g, Energy.LocalSlope.apply_const])) bot_le
  · apply perimeter_univ_eq_top_of_forall_isBounded
    intro S hS
    obtain ⟨b, hb⟩ := hS.bddAbove
    refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
    exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)

#print axioms cost_truncate_le_target_tail
#print axioms indicatorDistance_truncate_le_target_tail
#print axioms tendsto_measure_diff_ball
#print axioms perimeter_le_liminf_of_lipschitz_of_measure_lt_top
#print axioms lipschitzRelaxation_eq_perimeter_of_measure_lt_top
#print axioms reduction
#print axioms actualRelaxation
#print axioms fixedRadii
#print axioms realInterval
#print axioms unboundedFiniteMassTarget
#print axioms zeroMeasure
#print axioms finiteRegression
#print axioms emptyCarrier
#print axioms infiniteMassTargetCounterexample
end MetricBVFiniteTargetAudit
