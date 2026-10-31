module

public import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Strict clients for the actual lower-content relaxation at measurable finite-mass
targets under measures finite on bounded Borel sets. All convergence is global indicator
L1. The recovery client exposes bounded sets, finite masses, finite contents and the actual
limits. A convergent sequence may have an infinite-mass finite prefix. Neither the upper
endpoint nor the intervening radius-liminf coarea chain is asserted. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace MetricBVLocallyFiniteLowerAudit
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem actualInfimum (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
      liminf (fun n => minkowskiContent ν (A.1 n)) atTop) = perimeter ν B :=
  relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB

theorem actualRecovery (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) (hP : perimeter ν B < ⊤) :
    ∃ A : ℕ → Set X, (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Bornology.IsBounded (A n)) ∧ (∀ n, ν (A n) < ⊤) ∧
      (∀ n, minkowskiContent ν (A n) < ⊤) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
        atTop (𝓝 0) ∧ Tendsto (fun n => minkowskiContent ν (A n)) atTop (𝓝 (perimeter ν B)) :=
  exists_minkowskiRecovery_of_finite_on_bounded ν hν hB hνB hP

theorem arbitraryClassLower (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) (A : MinkowskiApproximatingSequence ν B) :
    perimeter ν B ≤ liminf (fun n => minkowskiContent ν (A.1 n)) atTop :=
  perimeter_le_liminf_minkowskiContent_of_measure_lt_top ν hB hνB A.2.1 A.2.2

theorem infinitePerimeter (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) (hP : perimeter ν B = ⊤) :
    relaxedMinkowskiContent ν B = ⊤ ∧
      ∀ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => minkowskiContent ν (A.1 n)) atTop = ⊤ :=
  ⟨(actualInfimum ν hν hB hνB).trans hP,
    fun A => top_le_iff.mp (hP ▸ arbitraryClassLower ν hB hνB A)⟩

/-- At a finite measure the relaxation identity holds for every target. -/
theorem finiteRegression (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    relaxedMinkowskiContent ν B = perimeter ν B := relaxedMinkowskiContent_eq_perimeter ν B

/-- Infinite total mass, nonempty finite-mass target, actual global-L1 infimum. -/
theorem realInterval : (volume : Measure ℝ) univ = ⊤ ∧
    relaxedMinkowskiContent volume (Set.Icc (0 : ℝ) 1) = perimeter volume (Set.Icc (0 : ℝ) 1) :=
  ⟨by simp, actualInfimum volume (fun s hs _ => hs.measure_lt_top) measurableSet_Icc (by simp)⟩

/-- The broader result is not restricted to bounded targets. -/
theorem unboundedNullTarget :
    ¬Bornology.IsBounded (Set.range fun n : ℕ => (n : ℝ)) ∧
      relaxedMinkowskiContent volume (Set.range fun n : ℕ => (n : ℝ)) =
        perimeter volume (Set.range fun n : ℕ => (n : ℝ)) := by
  have hc := Set.countable_range (fun n : ℕ => (n : ℝ))
  refine ⟨?_, actualInfimum volume (fun s hs _ => hs.measure_lt_top) hc.measurableSet ?_⟩
  · intro hb
    obtain ⟨b, hbound⟩ := hb.bddAbove
    obtain ⟨n, hn⟩ := exists_nat_gt b
    exact (not_le_of_gt hn) (hbound ⟨n, rfl⟩)
  · rw [hc.measure_zero (volume : Measure ℝ)]
    exact ENNReal.zero_lt_top

/-- At null targets the actual infimum vanishes, including unbounded ones. -/
theorem nullTarget (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B = 0) : relaxedMinkowskiContent ν B = 0 := by
  have hp : perimeter ν B = 0 := by
    have hconv : Tendsto (fun _ : ℕ => indicatorDistance ν Test.zero B) atTop (𝓝 0) := by
      have he : indicatorDistance ν Test.zero B = 0 := by
        unfold indicatorDistance
        have hpt : ∀ x, ‖Test.zero x - B.indicator (1 : X → ℝ) x‖ₑ = B.indicator 1 x := by
          intro x
          by_cases hx : x ∈ B
          · simp [Test.zero, hx]
          · simp [Test.zero, hx]
        simp_rw [hpt]
        rw [lintegral_indicator_one hB, hνB]
      simp only [he]
      exact tendsto_const_nhds
    exact le_antisymm (by simpa using perimeter_le_sequence ν B ⟨fun _ => Test.zero, hconv⟩) bot_le
  exact (actualInfimum ν hν hB (hνB ▸ ENNReal.zero_lt_top)).trans hp

/-- A finite prefix is allowed to have infinite mass. -/
def intervalWithInfinitePrefix : ℕ → Set ℝ := fun n => if n = 0 then univ else Set.Icc 0 1

theorem infinitePrefix :
    (volume : Measure ℝ) (intervalWithInfinitePrefix 0) = ⊤ ∧
      perimeter volume (Set.Icc (0 : ℝ) 1) ≤
        liminf (fun n => minkowskiContent volume (intervalWithInfinitePrefix n)) atTop := by
  have hA : ∀ n, MeasurableSet (intervalWithInfinitePrefix n) := by
    intro n
    by_cases hn : n = 0
    · simp [intervalWithInfinitePrefix, hn]
    · simp [intervalWithInfinitePrefix, hn]
  have hconv :
    Tendsto
      (fun n =>
        ∫⁻ x,
          ‖(intervalWithInfinitePrefix n).indicator (1 : ℝ → ℝ) x -
              (Set.Icc (0 : ℝ) 1).indicator 1 x‖ₑ ∂volume)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp [intervalWithInfinitePrefix, hn.ne']
  exact
    ⟨by simp [intervalWithInfinitePrefix],
      perimeter_le_liminf_minkowskiContent_of_measure_lt_top volume measurableSet_Icc (by simp)
        hA hconv⟩

theorem zeroMeasure {B : Set X} (hB : MeasurableSet B) :
    relaxedMinkowskiContent (0 : Measure X) B = 0 := nullTarget 0 (by simp) hB (by simp)

theorem emptyCarrier (ν : Measure Empty) {B : Set Empty} (hB : MeasurableSet B) :
    relaxedMinkowskiContent ν B = 0 :=
  nullTarget ν (by simp [Measure.eq_zero_of_isEmpty ν]) hB (by simp [Measure.eq_zero_of_isEmpty ν])

#print axioms exists_superlevel_selection_of_finite_on_bounded
#print axioms perimeter_le_liminf_minkowskiContent_of_measure_lt_top
#print axioms exists_minkowskiRecovery_of_finite_on_bounded
#print axioms relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded
#print axioms actualInfimum
#print axioms actualRecovery
#print axioms arbitraryClassLower
#print axioms infinitePerimeter
#print axioms finiteRegression
#print axioms realInterval
#print axioms unboundedNullTarget
#print axioms nullTarget
#print axioms infinitePrefix
#print axioms zeroMeasure
#print axioms emptyCarrier
end MetricBVLocallyFiniteLowerAudit
