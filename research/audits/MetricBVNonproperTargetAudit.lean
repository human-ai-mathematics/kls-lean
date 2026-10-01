import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski
import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation

/-! Strict proof client, promoted from external review task 01
(`build/audit/admg-locally-finite-eight-hour/external/claude/NonproperUnboundedTargetClient.lean`, sha256 prefix `51acc67faee3d39f`; hypotheses unchanged).

A concrete instance of the published
Theorem 3.6 scope exercising simultaneously:

* the carrier `P = Ioi (0 : ℝ)` with its subtype metric is provably **not proper**;
* Lebesgue measure on `P` has **infinite total mass** and is finite on bounded Borel sets
  (proved directly, not from compact-set finiteness);
* the target `T = ⋃ n, [n+1, n+1+2⁻ⁿ]` is **unbounded** with **positive finite** mass
  (the existing unbounded clients use the null target `range (↑) : ℕ → ℝ`).

Both relaxed contents are identified with the Definition 3.3 globally Lipschitz relaxation
and with the bounded-support perimeter on this instance. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace MetricBVNonproperTargetAudit
open FunctionalInequalities.KLS.MetricBV

abbrev P := Set.Ioi (0 : ℝ)

theorem not_properSpace : ¬ ProperSpace P := by
  intro hP
  let c : P := ⟨1, by norm_num⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall c 1).exists_isMinOn
    ⟨c, Metric.mem_closedBall_self zero_le_one⟩ continuous_subtype_val.continuousOn
  have hpos : (0 : ℝ) < x₀.1 := x₀.2
  have hle : |x₀.1 - 1| ≤ 1 := by
    have := Metric.mem_closedBall.1 hx₀
    rwa [Subtype.dist_eq, Real.dist_eq] at this
  have hle2 : x₀.1 ≤ 2 := by linarith [(abs_le.1 hle).2]
  let y : P := ⟨x₀.1 / 2, by simp only [Set.mem_Ioi]; linarith⟩
  have hy : y ∈ Metric.closedBall c 1 := by
    rw [Metric.mem_closedBall, Subtype.dist_eq, Real.dist_eq]
    show |x₀.1 / 2 - 1| ≤ 1
    rw [abs_le]; constructor <;> linarith
  have := hmin hy
  change x₀.1 ≤ x₀.1 / 2 at this
  linarith

theorem measurableSet_Ioi_zero : MeasurableSet (Set.Ioi (0 : ℝ)) := measurableSet_Ioi

/-- Lebesgue measure on the carrier (the subtype comap of `volume`). -/
def ν : Measure P := Measure.comap ((↑) : P → ℝ) volume

theorem volume_apply (s : Set P) : ν s = volume ((↑) '' s : Set ℝ) :=
  comap_subtype_coe_apply measurableSet_Ioi_zero _ s

theorem volume_univ : ν univ = ⊤ := by
  rw [volume_apply, Subtype.coe_image_univ]
  exact Real.volume_Ioi

/-- Finiteness on bounded Borel sets, proved from boundedness of the image in `ℝ`. -/
theorem finite_on_bounded (s : Set P) (hs : Bornology.IsBounded s) (_ : MeasurableSet s) :
    ν s < ⊤ := by
  rw [volume_apply]
  exact (isometry_subtype_coe.lipschitz.isBounded_image hs).measure_lt_top

/-- The unbounded target in `ℝ`. -/
def T : Set ℝ := ⋃ n : ℕ, Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 1 + (2⁻¹ : ℝ) ^ n)

/-- Its trace on the carrier. -/
def B : Set P := (↑) ⁻¹' T

theorem measurableSet_B : MeasurableSet B :=
  measurable_subtype_coe (MeasurableSet.iUnion fun _ => measurableSet_Icc)

theorem image_B : ((↑) '' B : Set ℝ) = T := by
  rw [B, Subtype.image_preimage_coe, Set.inter_eq_right]
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  simp only [Set.mem_Ioi]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith [hn.1]

theorem volume_T_le : volume T ≤ 2 := by
  refine (measure_iUnion_le _).trans (le_of_eq ?_)
  have h : ∀ n : ℕ, volume (Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 1 + (2⁻¹ : ℝ) ^ n)) =
      (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    rw [Real.volume_Icc, add_sub_cancel_left,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  simp_rw [h]
  exact ENNReal.tsum_geometric_two

theorem volume_B_lt_top : ν B < ⊤ := by
  rw [volume_apply, image_B]
  exact volume_T_le.trans_lt (by norm_num)

theorem volume_B_pos : 0 < ν B := by
  rw [volume_apply, image_B]
  have h0 : Set.Icc ((0 : ℕ) + 1 : ℝ) ((0 : ℕ) + 1 + (2⁻¹ : ℝ) ^ (0 : ℕ)) ⊆ T :=
    Set.subset_iUnion (fun n : ℕ => Set.Icc ((n : ℝ) + 1) ((n : ℝ) + 1 + (2⁻¹ : ℝ) ^ n)) 0
  refine lt_of_lt_of_le ?_ (measure_mono h0)
  rw [Real.volume_Icc]
  norm_num

theorem not_isBounded_B : ¬ Bornology.IsBounded B := by
  intro hb
  obtain ⟨b, hbound⟩ := (isometry_subtype_coe.lipschitz.isBounded_image hb).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have hmem : ((n : ℝ) + 1) ∈ ((↑) '' B : Set ℝ) := by
    rw [image_B]
    refine Set.mem_iUnion.2 ⟨n, le_rfl, ?_⟩
    have : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ n := by positivity
    linarith
  have := hbound hmem
  linarith

/-- The published Theorem 3.6 scope on this nonproper, infinite-mass carrier with an
unbounded positive-mass target: both relaxed contents equal the Definition 3.3 relaxation
and the bounded-support perimeter. -/
theorem theorem36_instance :
    ¬ ProperSpace P ∧ ν univ = ⊤ ∧ ¬ Bornology.IsBounded B ∧
      0 < ν B ∧ ν B < ⊤ ∧
      relaxedMinkowskiContent ν B = lipschitzRelaxation ν B ∧
      relaxedUpperMinkowskiContent ν B = lipschitzRelaxation ν B ∧
      lipschitzRelaxation ν B = perimeter ν B := by
  have hL := lipschitzRelaxation_eq_perimeter_of_measure_lt_top ν
    measurableSet_B volume_B_lt_top
  refine ⟨not_properSpace, volume_univ, not_isBounded_B, volume_B_pos, volume_B_lt_top,
    ?_, ?_, hL⟩
  · rw [hL]
    exact relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded ν finite_on_bounded
      measurableSet_B volume_B_lt_top
  · rw [hL]
    exact relaxedUpperMinkowskiContent_eq_perimeter_of_finite_on_bounded ν finite_on_bounded
      measurableSet_B volume_B_lt_top

end MetricBVNonproperTargetAudit

#print axioms MetricBVNonproperTargetAudit.not_properSpace
#print axioms MetricBVNonproperTargetAudit.finite_on_bounded
#print axioms MetricBVNonproperTargetAudit.volume_B_lt_top
#print axioms MetricBVNonproperTargetAudit.not_isBounded_B
#print axioms MetricBVNonproperTargetAudit.theorem36_instance
