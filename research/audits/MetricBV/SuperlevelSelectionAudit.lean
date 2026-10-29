import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-! Independent full-signature clients for the quantitative superlevel selection of metric BV
tests: the pointwise and integrated indicator errors, the positive-slack selection lemma (no
measurability of the selected function), finiteness of test costs, and the main selection with a
measurable superlevel set. Boundary checks: the measurable-`B` form, the endpoints `t = δ` and
`t = 1 - δ` of the error bound, zero cost, zero error, the zero test, the zero-dimensional space,
and the BV-perimeter form via `perimeter_le_minkowskiContent`. No regular boundary or
differentiability is used; this is not a sequence-level recovery or a Cheeger identification. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVSuperlevelSelectionAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

theorem pointwiseError {X : Type*} (g : X → ℝ) (B : Set X) {δ t : ℝ} (hδ : 0 < δ)
    (hδt : δ ≤ t) (ht : t ≤ 1 - δ) (x : X) :
    ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ≤
      ‖g x - B.indicator (1 : X → ℝ) x‖ₑ / ENNReal.ofReal δ := by
  exact enorm_indicator_superlevel_sub_le g B hδ hδt ht x

theorem integratedError {X : Type*} [MeasurableSpace X] (ν : Measure X) (g : X → ℝ) (B : Set X)
    {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (ht : t ≤ 1 - δ) :
    ∫⁻ x, ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
      (∫⁻ x, ‖g x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) / ENNReal.ofReal δ := by
  exact lintegral_enorm_indicator_superlevel_sub_le ν g B hδ hδt ht

/-- The error bound at both closed endpoints of the level interval. -/
theorem endpointErrors {X : Type*} (g : X → ℝ) (B : Set X) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (x : X) :
    ‖{y | δ ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ≤
        ‖g x - B.indicator (1 : X → ℝ) x‖ₑ / ENNReal.ofReal δ ∧
      ‖{y | 1 - δ ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ≤
        ‖g x - B.indicator (1 : X → ℝ) x‖ₑ / ENNReal.ofReal δ :=
  ⟨enorm_indicator_superlevel_sub_le g B hδ le_rfl (by linarith) x,
    enorm_indicator_superlevel_sub_le g B hδ (by linarith) le_rfl x⟩

theorem sliceSelection {φ : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a < b) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hφ : ∫⁻ t in Set.Ioo a b, φ t ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo a b, φ t ≤ C / ENNReal.ofReal (b - a) + ENNReal.ofReal ε := by
  exact exists_mem_Ioo_le_div_add_of_setLIntegral_le hab hC hφ hε

theorem costFinite {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : Test X) : cost ν f ≠ ⊤ := by
  exact cost_ne_top ν f

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem selection (ν : ProbabilityMeasure V) (f : Test V) (B : Set V) {δ ε : ℝ} (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), MeasurableSet {x | t ≤ f x} ∧
      Isoperimetry.minkowskiContent (ν : Measure V) {x | t ≤ f x} ≤
        cost (ν : Measure V) f / ENNReal.ofReal (1 - 2 * δ) + ENNReal.ofReal ε ∧
      ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        indicatorDistance (ν : Measure V) f B / ENNReal.ofReal δ := by
  exact exists_superlevel_selection (ν : Measure V) f B hδ hδ2 hε

/-- The form with measurable `B`. -/
theorem selectionMeasurable (ν : ProbabilityMeasure V) (f : Test V) {B : Set V}
    (_hB : MeasurableSet B) {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), MeasurableSet {x | t ≤ f x} ∧
      Isoperimetry.minkowskiContent (ν : Measure V) {x | t ≤ f x} ≤
        cost (ν : Measure V) f / ENNReal.ofReal (1 - 2 * δ) + ENNReal.ofReal ε ∧
      ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        indicatorDistance (ν : Measure V) f B / ENNReal.ofReal δ := by
  exact exists_superlevel_selection (ν : Measure V) f B hδ hδ2 hε

/-- Zero cost: the selected superlevel set has content at most `ε`. -/
theorem zeroCost (ν : ProbabilityMeasure V) (f : Test V) (hf : cost (ν : Measure V) f = 0)
    (B : Set V) {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), Isoperimetry.minkowskiContent (ν : Measure V) {x | t ≤ f x} ≤ ENNReal.ofReal ε := by
  obtain ⟨t, ht, -, hc, -⟩ := exists_superlevel_selection (ν : Measure V) f B hδ hδ2 hε
  rw [hf, ENNReal.zero_div, zero_add] at hc
  exact ⟨t, ht, hc⟩

/-- Zero error: the selected superlevel set has zero indicator distance to `B`. -/
theorem zeroError (ν : ProbabilityMeasure V) (f : Test V) (B : Set V)
    (hf : indicatorDistance (ν : Measure V) f B = 0) {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ),
      ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) = 0 := by
  obtain ⟨t, ht, -, -, he⟩ := exists_superlevel_selection (ν : Measure V) f B hδ hδ2 hε
  rw [hf, ENNReal.zero_div] at he
  exact ⟨t, ht, le_antisymm he bot_le⟩

/-- The zero test: every admissible level is positive, so the selected set is empty. -/
theorem zeroTest (ν : ProbabilityMeasure V) (B : Set V) {δ ε : ℝ} (hδ : 0 < δ)
    (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), {x | t ≤ (Test.zero : Test V) x} = ∅ ∧
      Isoperimetry.minkowskiContent (ν : Measure V) {x | t ≤ (Test.zero : Test V) x} ≤ ENNReal.ofReal ε := by
  obtain ⟨t, ht, hc⟩ := zeroCost ν Test.zero (cost_zero _) B hδ hδ2 hε
  refine ⟨t, ht, ?_, hc⟩
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have h0 : t ≤ 0 := hx
  linarith [ht.1]

/-- The zero-dimensional space: every test has zero cost. -/
theorem zeroDimensional (ν : ProbabilityMeasure (Fin 0 → ℝ)) (f : Test (Fin 0 → ℝ))
    (B : Set (Fin 0 → ℝ)) {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), Isoperimetry.minkowskiContent (ν : Measure (Fin 0 → ℝ)) {x | t ≤ f x} ≤ ENNReal.ofReal ε := by
  refine zeroCost ν f ?_ B hδ hδ2 hε
  simp [cost, FunctionalInequalities.Energy.LocalSlope.apply_eq_zero_of_subsingleton]

/-- The BV-perimeter form: the selected set has metric BV perimeter within the same bound. -/
theorem perimeterForm (ν : ProbabilityMeasure V) (f : Test V) (B : Set V) {δ ε : ℝ}
    (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ),
      perimeter (ν : Measure V) {x | t ≤ f x} ≤
        cost (ν : Measure V) f / ENNReal.ofReal (1 - 2 * δ) + ENNReal.ofReal ε ∧
      ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        indicatorDistance (ν : Measure V) f B / ENNReal.ofReal δ := by
  obtain ⟨t, ht, hm, hc, he⟩ := exists_superlevel_selection (ν : Measure V) f B hδ hδ2 hε
  exact ⟨t, ht, (perimeter_le_minkowskiContent (ν : Measure V) hm).trans hc, he⟩

#print axioms pointwiseError
#print axioms integratedError
#print axioms endpointErrors
#print axioms sliceSelection
#print axioms costFinite
#print axioms selection
#print axioms selectionMeasurable
#print axioms zeroCost
#print axioms zeroError
#print axioms zeroTest
#print axioms zeroDimensional
#print axioms perimeterForm

end MetricBVSuperlevelSelectionAudit
