module

public import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Strict clients for finite-neighborhood radius transfer, actual bounded open upper
recovery, and the global-indicator-L1 infimum, over the class without termwise finiteness, at
finite-mass Borel targets.
The measure may have infinite total mass and the space need not be proper. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace MetricBVLocallyFiniteUpperAudit
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem actualInfimum (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    (⨅ A : MinkowskiApproximatingSequence ν B,
      liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop) = perimeter ν B :=
  relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded ν hν hB hνB

theorem actualRecovery (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) (hP : perimeter ν B < ⊤) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ (∀ n, MeasurableSet (U n)) ∧
      (∀ n, Bornology.IsBounded (U n)) ∧ (∀ n, ν (U n) < ⊤) ∧
      (∀ n, upperMinkowskiContent ν (U n) < ⊤) ∧
      Tendsto (fun n => ∫⁻ x, ‖(U n).indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
        atTop (𝓝 0) ∧
      Tendsto (fun n => upperMinkowskiContent ν (U n)) atTop (𝓝 (perimeter ν B)) :=
  exists_upperMinkowskiRecovery_of_finite_on_bounded ν hν hB hνB hP

/-- The radius-local premise is proved from finite target mass and finite lower content. -/
theorem actualRadii (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) (hc : minkowskiContent ν B < ⊤) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ n, MeasurableSet (thickening (s n) B)) ∧ (∀ n, ν (thickening (s n) B) < ⊤) ∧
      Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) B).indicator (1 : X → ℝ) x -
        B.indicator 1 x‖ₑ ∂ν) atTop (𝓝 0) ∧
      limsup (fun n => upperMinkowskiContent ν (thickening (s n) B)) atTop ≤
        minkowskiContent ν B :=
  exists_upperRecovery_of_measure_lt_top ν hB hνB hc

section RestrictedMass

omit [BorelSpace X]
theorem finiteNeighborhood (ν : Measure X) {B : Set X} (hνB : ν B < ⊤)
    (hc : minkowskiContent ν B < ⊤) : ∃ r : ℝ, 0 < r ∧ ν (thickening r B) < ⊤ :=
  exists_measure_thickening_lt_top ν hνB hc

theorem actualRestrictedQuotient (ν : Measure X) {B U : Set X} (hU : MeasurableSet U)
    {r : ℝ} (hr : 0 < r) (hsub : thickening r B ⊆ U) :
    upperMinkowskiContent (ν.restrict U) B = upperMinkowskiContent ν B :=
  upperMinkowskiContent_restrict_of_thickening_subset ν hU hr hsub

end RestrictedMass

theorem arbitraryClassLower (ν : Measure X) {B : Set X} (hB : MeasurableSet B)
    (hνB : ν B < ⊤) (A : MinkowskiApproximatingSequence ν B) :
    perimeter ν B ≤ liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop :=
  perimeter_le_liminf_upperMinkowskiContent_of_measure_lt_top ν hB hνB A.2.1 A.2.2

theorem infinitePerimeter (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) (hP : perimeter ν B = ⊤) :
    relaxedUpperMinkowskiContent ν B = ⊤ ∧
      ∀ A : MinkowskiApproximatingSequence ν B,
        liminf (fun n => upperMinkowskiContent ν (A.1 n)) atTop = ⊤ :=
  ⟨(actualInfimum ν hν hB hνB).trans hP,
    fun A => top_le_iff.mp (hP ▸ arbitraryClassLower ν hB hνB A)⟩

theorem realInterval : (volume : Measure ℝ) univ = ⊤ ∧
    relaxedUpperMinkowskiContent volume (Set.Icc (0 : ℝ) 1) =
      perimeter volume (Set.Icc (0 : ℝ) 1) :=
  ⟨by simp, actualInfimum volume (fun s hs _ => hs.measure_lt_top) measurableSet_Icc (by simp)⟩

theorem unboundedNullTarget :
    ¬Bornology.IsBounded (Set.range fun n : ℕ => (n : ℝ)) ∧
      relaxedUpperMinkowskiContent volume (Set.range fun n : ℕ => (n : ℝ)) =
        perimeter volume (Set.range fun n : ℕ => (n : ℝ)) := by
  have hc := Set.countable_range (fun n : ℕ => (n : ℝ))
  refine ⟨?_, actualInfimum volume (fun s hs _ => hs.measure_lt_top) hc.measurableSet ?_⟩
  · intro hb
    obtain ⟨b, hbound⟩ := hb.bddAbove
    obtain ⟨n, hn⟩ := exists_nat_gt b
    exact (not_le_of_gt hn) (hbound ⟨n, rfl⟩)
  · rw [hc.measure_zero (volume : Measure ℝ)]
    exact ENNReal.zero_lt_top

/-- The class imposes no termwise finiteness: its first set may have infinite mass. -/
theorem infinitePrefix :
    let A : ℕ → Set ℝ := fun n => if n = 0 then univ else Set.Icc 0 1
    (volume : Measure ℝ) (A 0) = ⊤ ∧
      perimeter volume (Set.Icc (0 : ℝ) 1) ≤
        liminf (fun n => upperMinkowskiContent volume (A n)) atTop := by
  dsimp
  have hA : ∀ n : ℕ, MeasurableSet (if n = 0 then (univ : Set ℝ) else Set.Icc 0 1) := by
    intro n
    split_ifs <;> simp
  have hconv :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ x,
          ‖(if n = 0 then (univ : Set ℝ) else Set.Icc 0 1).indicator (1 : ℝ → ℝ) x -
              (Set.Icc (0 : ℝ) 1).indicator 1 x‖ₑ ∂volume)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp [hn.ne']
  exact
    ⟨by simp,
      perimeter_le_liminf_upperMinkowskiContent_of_measure_lt_top volume measurableSet_Icc
        (by simp) hA hconv⟩

theorem finiteRegression (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    relaxedUpperMinkowskiContent ν B = perimeter ν B :=
  relaxedUpperMinkowskiContent_eq_perimeter ν B

theorem probabilityRegression (ν : Measure X) [IsProbabilityMeasure ν] (B : Set X) :
    relaxedUpperMinkowskiContent ν B = relaxedMinkowskiContent ν B :=
  relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent ν B

omit [BorelSpace X] in
theorem zeroMeasure (B : Set X) : relaxedUpperMinkowskiContent (0 : Measure X) B = 0 :=
  relaxedUpperMinkowskiContent_zero_measure B

theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) :
    relaxedUpperMinkowskiContent ν B = 0 := by
  rw [Measure.eq_zero_of_isEmpty ν]
  exact relaxedUpperMinkowskiContent_zero_measure B

#print axioms exists_upperMinkowskiRecovery_of_finite_on_bounded
#print axioms exists_thickening_approx_of_measure_lt_top
#print axioms relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded
#print axioms relaxedUpperMinkowskiContent_eq_relaxedMinkowskiContent_of_finite_on_bounded
#print axioms actualInfimum
#print axioms actualRecovery
#print axioms actualRadii
#print axioms finiteNeighborhood
#print axioms actualRestrictedQuotient
#print axioms arbitraryClassLower
#print axioms infinitePerimeter
#print axioms realInterval
#print axioms unboundedNullTarget
#print axioms infinitePrefix
#print axioms finiteRegression
#print axioms probabilityRegression
#print axioms zeroMeasure
#print axioms emptyCarrier
end MetricBVLocallyFiniteUpperAudit
