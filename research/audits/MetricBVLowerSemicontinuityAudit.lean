import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBV

/-! Independent full-signature clients for the sequential lower semicontinuity of the metric BV
perimeter under global `L¹` convergence of set indicators, for every Borel measure: the owner
form (measurable approximating sets only), the requested form with a measurable limit set, the
triangle bound, constant sequences, an empty carrier, zero perimeter of null sets, and the
infinite boundary (the whole line under Lebesgue measure on `ℝ`: infinite target and infinite
liminf, and no convergent measurable sets of finite liminf perimeter). This is a relaxation
property, not a BV--Minkowski comparison. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace MetricBVLowerSemicontinuityAudit

open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem lowerSemicontinuity (ν : Measure X) {B : Set X} {Bn : ℕ → Set X}
    (hBn : ∀ n, MeasurableSet (Bn n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(Bn n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => perimeter ν (Bn n)) atTop := by
  exact perimeter_le_liminf_of_tendsto ν hBn hconv

/-- The requested form, with the limit set measurable as well. -/
theorem requestedForm (ν : Measure X) {B : Set X} {Bn : ℕ → Set X} (_hB : MeasurableSet B)
    (hBn : ∀ n, MeasurableSet (Bn n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(Bn n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
      atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => perimeter ν (Bn n)) atTop := by
  exact perimeter_le_liminf_of_tendsto ν hBn hconv

theorem triangleBound (ν : Measure X) (g : Test X) (B : Set X) {C : Set X}
    (hC : MeasurableSet C) :
    indicatorDistance ν g B ≤
      indicatorDistance ν g C + ∫⁻ x, ‖C.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
  exact indicatorDistance_le_add ν g B hC

/-- Consistency: the constant sequence gives the trivial bound. -/
theorem constantSequence (ν : Measure X) {B : Set X} (hB : MeasurableSet B) :
    perimeter ν B ≤ liminf (fun _ : ℕ => perimeter ν B) atTop := by
  exact perimeter_le_liminf_of_tendsto ν (fun _ => hB) (by simp)

/-- A measurable null set has zero perimeter: it is the `L¹` limit of the empty set. -/
theorem nullSet (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (h0 : ν B = 0) :
    perimeter ν B = 0 := by
  have hdist : ∫⁻ x, ‖(∅ : Set X).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν = 0 := by
    have hfun : (fun x => ‖(∅ : Set X).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ) =
        B.indicator 1 := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [hfun, lintegral_indicator_one hB, h0]
  have h := perimeter_le_liminf_of_tendsto ν (Bn := fun _ => (∅ : Set X)) (B := B)
    (fun _ => MeasurableSet.empty) (by simp only [hdist]; exact tendsto_const_nhds)
  simp only [perimeter_empty, liminf_const] at h
  exact le_antisymm h bot_le

/-- Empty carrier: every set has zero perimeter and the bound holds for every sequence. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) (Bn : ℕ → Set Empty) :
    perimeter ν B ≤ liminf (fun n => perimeter ν (Bn n)) atTop := by
  refine perimeter_le_liminf_of_tendsto ν (fun n => Set.toFinite (Bn n) |>.measurableSet) ?_
  simp [Measure.eq_zero_of_isEmpty ν]

theorem lebesgueWholeLineTop : perimeter (volume : Measure ℝ) Set.univ = ⊤ := by
  refine perimeter_univ_eq_top_of_forall_isBounded (volume : Measure ℝ) fun S hS => ?_
  obtain ⟨b, hb⟩ := hS.bddAbove
  refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
  exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)

/-- Infinite target and infinite liminf: the constant whole line under Lebesgue measure. -/
theorem infiniteBoundary :
    perimeter (volume : Measure ℝ) Set.univ ≤
        liminf (fun _ : ℕ => perimeter (volume : Measure ℝ) Set.univ) atTop ∧
      liminf (fun _ : ℕ => perimeter (volume : Measure ℝ) Set.univ) atTop = ⊤ := by
  refine ⟨perimeter_le_liminf_of_tendsto _ (fun _ => MeasurableSet.univ) (by simp), ?_⟩
  rw [liminf_const, lebesgueWholeLineTop]

/-- Consequence: no measurable sets converging to the whole line in `L¹(volume)` have finite
liminf perimeter. -/
theorem noFiniteApproximationOfWholeLine (Bn : ℕ → Set ℝ) (hBn : ∀ n, MeasurableSet (Bn n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(Bn n).indicator (1 : ℝ → ℝ) x -
      (Set.univ : Set ℝ).indicator 1 x‖ₑ) atTop (𝓝 0)) :
    liminf (fun n => perimeter (volume : Measure ℝ) (Bn n)) atTop = ⊤ := by
  have h := perimeter_le_liminf_of_tendsto (volume : Measure ℝ) hBn hconv
  rw [lebesgueWholeLineTop] at h
  exact top_le_iff.mp h

#print axioms lowerSemicontinuity
#print axioms requestedForm
#print axioms triangleBound
#print axioms constantSequence
#print axioms nullSet
#print axioms emptyCarrier
#print axioms lebesgueWholeLineTop
#print axioms infiniteBoundary
#print axioms noFiniteApproximationOfWholeLine

end MetricBVLowerSemicontinuityAudit
