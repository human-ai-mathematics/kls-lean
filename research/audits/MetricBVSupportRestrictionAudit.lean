import FunctionalInequalities.Analysis.MetricBV.Transport
import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-! Independent full-signature clients for the restriction of metric BV tests, approximating
sequences and perimeters to a measurable subset, in particular to the closed measure support:
`perimeter (closedSupportLaw ν) (Subtype.val ⁻¹' B) ≤ perimeter ν B`. Checks: the isometry slope
lemma, the measurable-`B` form, a proper closed support (the two-atom law `(δ₀ + δ₁)/2` on `ℝ`,
whose support contains `0` but not `1/2`) where the ambient perimeter of `Iic (1/2)` is zero and
hence so is the restricted one, the empty set, top ambient perimeter, and the whole space. No
reverse inequality or constant equality on the closed support is claimed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVSupportRestrictionAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

theorem isometrySlope {X Y : Type*} [MetricSpace X] [MetricSpace Y] {e : Y → X}
    (he : Isometry e) (f : X → ℝ) (y : Y) :
    FunctionalInequalities.Energy.LocalSlope.apply (f ∘ e) y ≤
      FunctionalInequalities.Energy.LocalSlope.apply f (e y) := by
  exact FunctionalInequalities.Energy.LocalSlope.apply_comp_le_of_isometry he f y

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem restrictCost (ν : Measure X) {s : Set X} (hs : MeasurableSet s) (f : Test X) :
    cost (ν.comap Subtype.val) (f.restrict s) ≤ cost ν f := by
  exact cost_restrict_le ν hs f

theorem restrictDistance (ν : Measure X) {s : Set X} (hs : MeasurableSet s) (f : Test X)
    (B : Set X) :
    indicatorDistance (ν.comap Subtype.val) (f.restrict s) (Subtype.val ⁻¹' B) ≤
      indicatorDistance ν f B := by
  exact indicatorDistance_restrict_le ν hs f B

/-- The restricted sequence consists of the restricted tests. -/
theorem restrictSequence {ν : Measure X} {B s : Set X} (hs : MeasurableSet s)
    (g : ApproximatingSequence ν B) (n : ℕ) : ((g.restrict hs).1 n) = (g.1 n).restrict s :=
  rfl

theorem subsetPerimeter (ν : Measure X) {s : Set X} (hs : MeasurableSet s) (B : Set X) :
    perimeter (ν.comap (Subtype.val : s → X)) ((Subtype.val : s → X) ⁻¹' B) ≤ perimeter ν B := by
  exact perimeter_comap_subtype_le ν hs B

variable [SecondCountableTopology X]

theorem supportPerimeter (ν : ProbabilityMeasure X) (B : Set X) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) ≤
      perimeter (ν : Measure X) B := by
  exact perimeter_closedSupportLaw_le ν B

/-- The requested form, with `B` measurable. -/
theorem supportPerimeterMeasurable (ν : ProbabilityMeasure X) {B : Set X}
    (_hB : MeasurableSet B) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) ≤
      perimeter (ν : Measure X) B := by
  exact perimeter_closedSupportLaw_le ν B

/-- The empty set restricts to the empty set, of zero perimeter on the support. -/
theorem emptySet (ν : ProbabilityMeasure X) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support)
      (Subtype.val ⁻¹' (∅ : Set X)) = 0 := by
  have h := perimeter_closedSupportLaw_le ν ∅
  rw [perimeter_empty] at h
  exact le_antisymm h bot_le

/-- Top ambient perimeter: the bound holds and is vacuous. -/
theorem topAmbient (ν : ProbabilityMeasure X) {B : Set X}
    (htop : perimeter (ν : Measure X) B = ⊤) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support) (Subtype.val ⁻¹' B) ≤ ⊤ :=
  htop ▸ perimeter_closedSupportLaw_le ν B

/-- The whole space: its trace on the support has zero perimeter (the ambient whole space of a
probability law has zero perimeter, via the constant one). -/
theorem wholeSpace (ν : ProbabilityMeasure X) :
    perimeter (closedSupportLaw ν : Measure (ν : Measure X).support)
      (Subtype.val ⁻¹' (Set.univ : Set X)) = 0 := by
  have h0 : perimeter (ν : Measure X) Set.univ = 0 := by
    have h := perimeter_le_liminf_of_lipschitz (ν : Measure X) (B := Set.univ)
      (f := fun _ _ => (1 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 1⟩) (by simp)
    simp only [FunctionalInequalities.Energy.LocalSlope.apply_const, lintegral_zero,
      liminf_const] at h
    exact le_antisymm h bot_le
  have h := perimeter_closedSupportLaw_le ν Set.univ
  rw [h0] at h
  exact le_antisymm h bot_le

/-- The two-atom law `(δ₀ + δ₁)/2` on `ℝ`. -/
def twoAtom : ProbabilityMeasure ℝ :=
  ⟨(2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1), ⟨by
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩⟩

theorem twoAtom_apply_eq (S : Set ℝ) :
    (twoAtom : Measure ℝ) S = (2 : ℝ≥0∞)⁻¹ * (Measure.dirac (0 : ℝ) S + Measure.dirac 1 S) := rfl

/-- The support of the two-atom law is proper: it contains `0` but not `1/2`. -/
theorem twoAtomSupport :
    (0 : ℝ) ∈ (twoAtom : Measure ℝ).support ∧ (1 / 2 : ℝ) ∉ (twoAtom : Measure ℝ).support := by
  constructor
  · by_contra h
    obtain ⟨t, ht, hzero⟩ :=
      Filter.eventually_smallSets.1 (Measure.notMem_support_iff.1 h)
    have h0 := hzero t subset_rfl
    rw [twoAtom_apply_eq, Measure.dirac_apply_of_mem (mem_of_mem_nhds ht)] at h0
    have : (2 : ℝ≥0∞)⁻¹ * (1 + Measure.dirac (1 : ℝ) t) ≠ 0 :=
      mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) (by simp)
    exact this h0
  · refine Measure.notMem_support_iff.2 (Filter.eventually_smallSets.2
      ⟨Metric.ball (1 / 2) (1 / 4), Metric.ball_mem_nhds _ (by norm_num), fun u hu => ?_⟩)
    refine le_antisymm ((measure_mono hu).trans ?_) bot_le
    rw [twoAtom_apply_eq, Measure.dirac_apply' _ measurableSet_ball,
      Measure.dirac_apply' _ measurableSet_ball]
    have h0 : (0 : ℝ) ∉ Metric.ball (1 / 2 : ℝ) (1 / 4) := by
      simp only [Metric.mem_ball, Real.dist_eq, not_lt]
      rw [abs_of_neg (by norm_num)]
      norm_num
    have h1 : (1 : ℝ) ∉ Metric.ball (1 / 2 : ℝ) (1 / 4) := by
      simp only [Metric.mem_ball, Real.dist_eq, not_lt]
      rw [abs_of_pos (by norm_num)]
      norm_num
    rw [Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]
    simp

/-- On the proper support of the two-atom law, the trace of `Iic (1/2)` has zero perimeter: the
ambient set has zero Minkowski content, hence zero perimeter, and restriction does not increase
it. -/
theorem twoAtomRestriction :
    perimeter (closedSupportLaw twoAtom : Measure (twoAtom : Measure ℝ).support)
      (Subtype.val ⁻¹' Set.Iic (1 / 2 : ℝ)) = 0 := by
  set B : Set ℝ := Set.Iic (1 / 2) with hBdef
  have hBm : MeasurableSet B := measurableSet_Iic
  have hmass : (twoAtom : Measure ℝ) B = 2⁻¹ := by
    rw [twoAtom_apply_eq, Measure.dirac_apply' _ hBm, Measure.dirac_apply' _ hBm]
    simp [hBdef]
    norm_num
  have hc : Isoperimetry.minkowskiContent (twoAtom : Measure ℝ) B = 0 := by
    refine le_antisymm ?_ bot_le
    refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with r hr
    have hsub : Metric.thickening r B ⊆ Set.Iio (1 / 2 + r) := fun x hx => by
      obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.mp hx
      have hz' : z ≤ 1 / 2 := hz
      have := (abs_lt.mp (by simpa [Real.dist_eq] using hdz)).2
      show x < 1 / 2 + r
      linarith
    have hIio : (twoAtom : Measure ℝ) (Set.Iio (1 / 2 + r)) = 2⁻¹ := by
      rw [twoAtom_apply_eq, Measure.dirac_apply' _ measurableSet_Iio,
        Measure.dirac_apply' _ measurableSet_Iio]
      have h0 : (0 : ℝ) ∈ Set.Iio (1 / 2 + r) := by simp only [Set.mem_Iio]; linarith [hr.1]
      have h1 : (1 : ℝ) ∉ Set.Iio (1 / 2 + r) := by
        simp only [Set.mem_Iio, not_lt]; linarith [hr.2]
      rw [Set.indicator_of_mem h0, Set.indicator_of_notMem h1]
      simp
    have hthick : (twoAtom : Measure ℝ) (Metric.thickening r B) ≤ 2⁻¹ :=
      (measure_mono hsub).trans hIio.le
    rw [hmass, tsub_eq_zero_of_le hthick, ENNReal.zero_div]
  have hp : perimeter (twoAtom : Measure ℝ) B = 0 :=
    le_antisymm ((perimeter_le_minkowskiContent (twoAtom : Measure ℝ) hBm).trans_eq hc) bot_le
  have h := perimeter_closedSupportLaw_le twoAtom B
  rw [hp] at h
  exact le_antisymm h bot_le

#print axioms isometrySlope
#print axioms restrictCost
#print axioms restrictDistance
#print axioms restrictSequence
#print axioms subsetPerimeter
#print axioms supportPerimeter
#print axioms supportPerimeterMeasurable
#print axioms emptySet
#print axioms topAmbient
#print axioms wholeSpace
#print axioms twoAtomSupport
#print axioms twoAtomRestriction

end MetricBVSupportRestrictionAudit
