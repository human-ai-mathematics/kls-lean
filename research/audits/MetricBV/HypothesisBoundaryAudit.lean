module

public import FunctionalInequalities.KLS.Geometry.Perimeter.RelaxedMinkowski

/-! Strict proof client: two hypothesis boundaries of the published-scope Minkowski identities.

1. `ν B < ⊤` cannot be dropped from `relaxedMinkowskiContent_eq_perimeter_of_finite_on_bounded`
   (nor its upper analogue): for Lebesgue measure on `ℝ` and `B = univ`, the ENNReal truncated
   content convention (`⊤ - ⊤ = 0`, outside the paper's domain `m(A) < ∞`) makes both relaxed
   contents `0`, while the bounded-support perimeter is `⊤`.
2. Finiteness on compact sets does not supply the `hν` premise on a nonproper carrier: on
   `P = Ioi (0 : ℝ)`, the measure `∑ₙ δ_{1/(n+1)}` is finite on compacts
   (`IsFiniteMeasureOnCompacts`) but gives infinite mass to the bounded Borel set
   `{x | x ≤ 1}`. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace MetricBVHypothesisBoundaryAudit
open FunctionalInequalities.KLS.MetricBV
open FunctionalInequalities.KLS.Isoperimetry

theorem perimeter_univ_real : perimeter (volume : Measure ℝ) univ = ⊤ := by
  apply perimeter_univ_eq_top_of_forall_isBounded
  intro S hS
  obtain ⟨b, hb⟩ := hS.bddAbove
  refine top_le_iff.mp ((Real.volume_Ioi (a := b)).symm.le.trans (measure_mono fun x hx => ?_))
  exact fun hxS => not_le.mpr (Set.mem_Ioi.mp hx) (hb hxS)

theorem upperMinkowskiContent_univ_real : upperMinkowskiContent (volume : Measure ℝ) univ = 0 := by
  unfold upperMinkowskiContent
  have he :
    (fun r : ℝ =>
        ((volume : Measure ℝ) (Metric.thickening r (univ : Set ℝ)) - volume (univ : Set ℝ)) /
          ENNReal.ofReal r) =ᶠ[𝓝[>] (0 : ℝ)]
      fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Set.eq_univ_of_univ_subset (Metric.self_subset_thickening hr (univ : Set ℝ))]
    simp
  rw [limsup_congr he, limsup_const]

/-- The constant approximating sequence `univ`. -/
def constUniv : MinkowskiApproximatingSequence (volume : Measure ℝ) univ :=
  ⟨fun _ => univ, fun _ => MeasurableSet.univ, by simp⟩

/-- At an infinite-mass target both relaxed contents vanish while the perimeter is `⊤`, and
Lebesgue measure is finite on bounded Borel sets: only the dropped `ν B < ⊤` premise fails. -/
theorem infiniteMassTarget :
    (∀ s : Set ℝ, Bornology.IsBounded s → MeasurableSet s → (volume : Measure ℝ) s < ⊤) ∧
      (volume : Measure ℝ) univ = ⊤ ∧
      relaxedMinkowskiContent (volume : Measure ℝ) univ = 0 ∧
      relaxedUpperMinkowskiContent (volume : Measure ℝ) univ = 0 ∧
      perimeter (volume : Measure ℝ) univ = ⊤ := by
  refine ⟨fun s hs _ => hs.measure_lt_top, by simp, ?_, ?_, perimeter_univ_real⟩
  · refine le_antisymm ((iInf_le _ constUniv).trans ?_) bot_le
    simp [constUniv, minkowskiContent_univ]
  · refine le_antisymm ((iInf_le _ constUniv).trans ?_) bot_le
    simp [constUniv, upperMinkowskiContent_univ_real]

/-- Hence the published identity is false without the finite-target-mass premise. -/
theorem not_forall_relaxed_eq_perimeter :
    ¬ ∀ B : Set ℝ, MeasurableSet B →
      relaxedMinkowskiContent (volume : Measure ℝ) B = perimeter volume B := by
  intro h
  obtain ⟨-, -, h0, -, htop⟩ := infiniteMassTarget
  have := h univ MeasurableSet.univ
  rw [h0, htop] at this
  exact ENNReal.zero_ne_top this

/-! ### Finite on compacts, not finite on bounded sets, on a nonproper carrier -/

abbrev P := Set.Ioi (0 : ℝ)

/-- The points `1/(n+1)`, accumulating only at the missing endpoint `0`. -/
def pt (n : ℕ) : P := ⟨1 / ((n : ℝ) + 1), by simp only [Set.mem_Ioi]; positivity⟩

/-- Counting measure on the points `pt n`. -/
def μ : Measure P := Measure.sum fun n => Measure.dirac (pt n)

theorem μ_apply {s : Set P} (hs : MeasurableSet s) : μ s = ∑' n, s.indicator 1 (pt n) := by
  simp only [μ, Measure.sum_apply _ hs, Measure.dirac_apply' _ hs]

instance : IsFiniteMeasureOnCompacts μ := by
  refine ⟨fun K hK => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne continuous_subtype_val.continuousOn
  have hpos : (0 : ℝ) < x₀.1 := x₀.2
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / x₀.1)
  rw [μ_apply hK.isClosed.measurableSet, tsum_eq_sum (s := Finset.range N)]
  · exact ENNReal.sum_lt_top.2 fun n _ => by by_cases h : pt n ∈ K <;> simp [Set.indicator, h]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [Set.indicator_of_notMem]
    intro hmem
    have hle : x₀.1 ≤ 1 / ((n : ℝ) + 1) := hmin hmem
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 1 / x₀.1 < (n : ℝ) + 1 := by linarith
    have h2 : 1 / ((n : ℝ) + 1) < x₀.1 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at h1
      linarith
    linarith

/-- The bounded Borel set `{x ≤ 1}` contains every point, so it has infinite mass. -/
theorem not_finite_on_bounded :
    ¬∀ s : Set P, Bornology.IsBounded s → MeasurableSet s → μ s < ⊤ := by
  intro h
  let S : Set P := {x | x.1 ≤ 1}
  have hS : MeasurableSet S :=
    measurableSet_le continuous_subtype_val.measurable measurable_const
  have hb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := pt 0) (r := 1)).subset fun x hx => ?_
    rw [Metric.mem_closedBall, Subtype.dist_eq, Real.dist_eq]
    have h0 : (0 : ℝ) < x.1 := x.2
    have h1 : x.1 ≤ 1 := hx
    have hp : (pt 0).1 = 1 := by simp [pt]
    rw [hp, abs_le]; constructor <;> linarith
  have hall : ∀ n, pt n ∈ S := fun n => by
    show 1 / ((n : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have htop : μ S = ⊤ := by
    rw [μ_apply hS]
    simp only [Set.indicator_of_mem (hall _), Pi.one_apply]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  exact (h S hb hS).ne htop

theorem compactFiniteness_insufficient :
    IsFiniteMeasureOnCompacts μ ∧ ¬ ProperSpace P ∧
      ¬ ∀ s : Set P, Bornology.IsBounded s → MeasurableSet s → μ s < ⊤ := by
  refine ⟨inferInstance, fun hP => ?_, not_finite_on_bounded⟩
  -- a proper carrier would make compact finiteness give bounded finiteness
  have := hP
  exact not_finite_on_bounded fun s hs _ => hs.measure_lt_top

end MetricBVHypothesisBoundaryAudit

#print axioms MetricBVHypothesisBoundaryAudit.infiniteMassTarget
#print axioms MetricBVHypothesisBoundaryAudit.not_forall_relaxed_eq_perimeter
#print axioms MetricBVHypothesisBoundaryAudit.not_finite_on_bounded
#print axioms MetricBVHypothesisBoundaryAudit.compactFiniteness_insufficient
