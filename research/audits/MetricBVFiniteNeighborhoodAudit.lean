import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-! Strict clients for radius-local restriction, positive-level coarea, the nonnegative
content/slope bound, and perimeter below content at measurable finite-mass targets.
No properness or sigma-finiteness is assumed by the generic clients. The real-volume
client has infinite total mass. This is the direct coarea upper bound, not the full
radius-liminf chain of ADMG Lemma 3.2 or a Minkowski recovery identity. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology
namespace MetricBVFiniteNeighborhoodAudit
open FunctionalInequalities
open FunctionalInequalities.KLS.Isoperimetry
open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem radiusLocal (ν : Measure X) {B U : Set X} (hU : MeasurableSet U)
    {δ : ℝ} (hδ : 0 < δ) (hsub : Metric.thickening δ B ⊆ U) :
    minkowskiContent (ν.restrict U) B = minkowskiContent ν B :=
  minkowskiContent_restrict_of_thickening_subset ν hU hδ hsub

theorem wholeCarrier (ν : Measure X) : minkowskiContent ν (Set.univ : Set X) = 0 :=
  minkowskiContent_univ ν

variable [BorelSpace X]

theorem positiveLevels (ν : Measure X) {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {δ : ℝ} (hδ : 0 < δ) (hfin : ν (Metric.thickening δ {x | 0 < u x}) < ⊤) :
    ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂ν :=
  setLIntegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood ν hK hδ hfin

theorem nonnegativeLevels (ν : Measure X) {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : ∀ x, 0 ≤ u x) {δ : ℝ} (hδ : 0 < δ)
    (hfin : ν (Metric.thickening δ {x | 0 < u x}) < ⊤) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂ν :=
  lintegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood ν hK hu hδ hfin

theorem finiteOnBounded (ν : Measure X)
    (hν : ∀ s : Set X, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu : Bornology.IsBounded {x | 0 < u x}) :
    ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂ν :=
  setLIntegral_minkowskiContent_superlevel_le_localSlope_of_bounded_positive ν hν hK hu

theorem finiteTarget (ν : Measure X) {B : Set X} (hB : MeasurableSet B) (hνB : ν B < ⊤) :
    perimeter ν B ≤ minkowskiContent ν B :=
  perimeter_le_minkowskiContent_of_measure_lt_top ν hB hνB

/-- The old arbitrary-Lipschitz finite-total-mass coarea scope is retained. -/
theorem finiteRegression (ν : Measure X) [IsFiniteMeasure ν] {u : X → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) {B : Set X} (hB : MeasurableSet B) :
    (∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂ν) ∧ perimeter ν B ≤ minkowskiContent ν B :=
  ⟨lintegral_minkowskiContent_superlevel_le_localSlope ν hK, perimeter_le_minkowskiContent ν hB⟩

theorem zeroFunction (ν : Measure X) :
    (∫⁻ t, minkowskiContent ν {_x : X | t ≤ (0 : ℝ)} ∂(volume : Measure ℝ)) = 0 := by
  have hfin : ν (Metric.thickening 1 {_x : X | 0 < (0 : ℝ)}) < ⊤ := by simp
  have h := nonnegativeLevels ν (u := fun _ => 0) (LipschitzWith.const 0)
    (fun _ => le_rfl) zero_lt_one hfin
  exact le_antisymm (by simpa only [Energy.LocalSlope.apply_const, lintegral_zero] using h) zero_le

/-- A negative function has empty positive support; only its positive-level integral is used. -/
theorem negativeFunction (ν : Measure X) :
    (∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {_x : X | t ≤ (-1 : ℝ)}
      ∂(volume : Measure ℝ)) = 0 := by
  have hfin : ν (Metric.thickening 1 {_x : X | 0 < (-1 : ℝ)}) < ⊤ := by norm_num
  have h := positiveLevels ν (u := fun _ => -1) (LipschitzWith.const (-1)) zero_lt_one hfin
  exact le_antisymm (by simpa only [Energy.LocalSlope.apply_const, lintegral_zero] using h) zero_le

/-- Concrete infinite-total-mass test client, without an artificial finite measure. -/
theorem realVolumeTest (f : Test ℝ) :
    (volume : Measure ℝ) Set.univ = ⊤ ∧
      (∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent volume {x | t ≤ f x}
        ∂(volume : Measure ℝ)) ≤ cost volume f ∧ cost volume f < ⊤ := by
  obtain ⟨K, hK⟩ := f.lipschitz
  have hpos : Bornology.IsBounded {x : ℝ | 0 < f x} :=
    f.boundedSupport.subset fun x hx => (show f x ≠ 0 from ne_of_gt hx)
  exact ⟨by simp, finiteOnBounded volume (fun s hs _ => hs.measure_lt_top) hK hpos,
    (cost_ne_top_of_support_measure volume f f.boundedSupport.closure.measure_lt_top.ne).lt_top⟩

theorem realInterval : (volume : Measure ℝ) Set.univ = ⊤ ∧
    perimeter volume (Set.Icc (0 : ℝ) 1) ≤ minkowskiContent volume (Set.Icc (0 : ℝ) 1) :=
  ⟨by simp, finiteTarget volume measurableSet_Icc (by simp)⟩

theorem zeroMeasure {B : Set X} (hB : MeasurableSet B) :
    perimeter (0 : Measure X) B ≤ minkowskiContent (0 : Measure X) B :=
  finiteTarget 0 hB (by simp)

theorem emptyCarrier (ν : Measure Empty) {B : Set Empty} (hB : MeasurableSet B) :
    perimeter ν B ≤ minkowskiContent ν B :=
  finiteTarget ν hB (by simp [Measure.eq_zero_of_isEmpty ν])

#print axioms minkowskiContent_restrict_of_thickening_subset
#print axioms setLIntegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood
#print axioms lintegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood
#print axioms perimeter_le_minkowskiContent_of_measure_lt_top
#print axioms radiusLocal
#print axioms wholeCarrier
#print axioms positiveLevels
#print axioms nonnegativeLevels
#print axioms finiteOnBounded
#print axioms finiteTarget
#print axioms finiteRegression
#print axioms zeroFunction
#print axioms negativeFunction
#print axioms realVolumeTest
#print axioms realInterval
#print axioms zeroMeasure
#print axioms emptyCarrier
end MetricBVFiniteNeighborhoodAudit
