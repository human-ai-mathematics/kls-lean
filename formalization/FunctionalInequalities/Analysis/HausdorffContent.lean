import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Scalewise Hausdorff cover costs and measurability of compact slices

Metric-space layer of the coarea route, depending on Mathlib only.  Mathlib's `μH[d]` is the
supremum over scales of an infimum over countable covers of that scale
(`Measure.hausdorffMeasure_apply`).  This module names that scalewise infimum `coverCost`, adds the
variant `openCoverCost` restricted to covers by **open** sets, and proves the two facts the coarea
route needs about them:

* `iSup_openCoverCost_eq_hausdorffMeasure`: the open-cover costs have the same scalewise supremum,
  `⨆ n, openCoverCost d (n + 1)⁻¹ A = μH[d] A`, for every set `A` and every `0 ≤ d`.  The
  inequality `≥` is immediate because open covers are covers; the inequality `≤` thickens an
  arbitrary near-optimal cover into an open one, which costs an arbitrarily small amount by
  `Metric.ediam_thickening_le` together with a summable choice of thickening radii
  (`ENNReal.exists_pos_sum_of_countable`).  Each `openCoverCost` on its own is generally **larger**
  than the `coverCost` of the same scale, so the equality genuinely needs the scale limit; this is
  why the route's note forbids claiming semicontinuity of `μH[d]` itself.

* `upperSemicontinuous_openCoverCost_slice`: at a **fixed** scale, the open-cover cost of the slice
  of a compact set by a level of a continuous function is upper semicontinuous in the level.  Here
  the restriction to open covers is what makes the argument work: an open cover of one slice still
  covers all nearby slices, because the compact part of the set outside the cover keeps the
  function at a positive distance from the level (`isOpen_setOf_slice_subset`).

Together they give `measurable_hausdorffMeasure_inter_levelSet`: for `S` compact and `u`
continuous, `t ↦ μH[d] (S ∩ {u = t})` is Borel measurable — a countable supremum of upper
semicontinuous functions.  `S` is not assumed to have finite measure in any dimension, `u` is not
assumed Lipschitz, `d = 0` is allowed (the cover cost keeps Mathlib's `Nonempty` guard, so empty
pieces cost `0` rather than `0 ^ (0 : ℝ) = 1`), and nothing here is a statement about the
measurability of slices of a noncompact set.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

section Content

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The cost of a countable family for the `d`-dimensional Hausdorff gauge, with Mathlib's
`Nonempty` guard: an empty piece costs `0` even when `d = 0`. -/
def familyCost (d : ℝ) (T : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d

/-- The scalewise Hausdorff cover cost: the infimum of `familyCost` over countable covers whose
pieces have diameter at most `r`.  This is the inner infimum of
`Measure.hausdorffMeasure_apply`. -/
def coverCost (d : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ i, T i) (_ : ∀ i, Metric.ediam (T i) ≤ r), familyCost d T

/-- The scalewise Hausdorff cover cost computed with **open** covers only.  At a fixed scale it is
generally larger than `coverCost`; only the scale limits agree
(`iSup_openCoverCost_eq_hausdorffMeasure`). -/
def openCoverCost (d : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (T : ℕ → Set X) (_ : ∀ i, IsOpen (T i)) (_ : A ⊆ ⋃ i, T i)
    (_ : ∀ i, Metric.ediam (T i) ≤ r), familyCost d T

theorem hausdorffMeasure_eq_iSup_coverCost (d : ℝ) (A : Set X) :
    μH[d] A = ⨆ (r : ℝ≥0∞) (_ : 0 < r), coverCost d r A :=
  Measure.hausdorffMeasure_apply d A

omit [MeasurableSpace X] [BorelSpace X] in
theorem coverCost_le {d : ℝ} {r : ℝ≥0∞} {A : Set X} {T : ℕ → Set X} (hcov : A ⊆ ⋃ i, T i)
    (hdiam : ∀ i, Metric.ediam (T i) ≤ r) : coverCost d r A ≤ familyCost d T :=
  iInf_le_of_le T (iInf_le_of_le hcov (iInf_le_of_le hdiam le_rfl))

omit [MeasurableSpace X] [BorelSpace X] in
theorem openCoverCost_le {d : ℝ} {r : ℝ≥0∞} {A : Set X} {T : ℕ → Set X}
    (hopen : ∀ i, IsOpen (T i)) (hcov : A ⊆ ⋃ i, T i) (hdiam : ∀ i, Metric.ediam (T i) ≤ r) :
    openCoverCost d r A ≤ familyCost d T :=
  iInf_le_of_le T (iInf_le_of_le hopen (iInf_le_of_le hcov (iInf_le_of_le hdiam le_rfl)))

omit [MeasurableSpace X] [BorelSpace X] in
theorem openCoverCost_lt_iff {d : ℝ} {r c : ℝ≥0∞} {A : Set X} :
    openCoverCost d r A < c ↔ ∃ T : ℕ → Set X, (∀ i, IsOpen (T i)) ∧ A ⊆ ⋃ i, T i ∧
      (∀ i, Metric.ediam (T i) ≤ r) ∧ familyCost d T < c := by
  constructor
  · intro h
    obtain ⟨T, h⟩ := iInf_lt_iff.1 h
    obtain ⟨hopen, h⟩ := iInf_lt_iff.1 h
    obtain ⟨hcov, h⟩ := iInf_lt_iff.1 h
    obtain ⟨hdiam, hcost⟩ := iInf_lt_iff.1 h
    exact ⟨T, hopen, hcov, hdiam, hcost⟩
  · rintro ⟨T, hopen, hcov, hdiam, hcost⟩
    exact (openCoverCost_le hopen hcov hdiam).trans_lt hcost

omit [MeasurableSpace X] [BorelSpace X] in
/-- Smaller scales allow fewer covers, so the cover cost is antitone in the scale. -/
theorem coverCost_mono_scale {d : ℝ} {r r' : ℝ≥0∞} (h : r' ≤ r) (A : Set X) :
    coverCost d r A ≤ coverCost d r' A :=
  le_iInf fun _T => le_iInf fun hcov => le_iInf fun hdiam =>
    coverCost_le hcov fun i => (hdiam i).trans h

omit [MeasurableSpace X] [BorelSpace X] in
theorem coverCost_le_openCoverCost {d : ℝ} {r : ℝ≥0∞} (A : Set X) :
    coverCost d r A ≤ openCoverCost d r A :=
  le_iInf fun _T => le_iInf fun _ => le_iInf fun hcov => le_iInf fun hdiam =>
    coverCost_le hcov hdiam

/-- Every scalewise cover cost is at most `μH[d]`, since `μH[d]` is their supremum. -/
theorem coverCost_le_hausdorffMeasure {d : ℝ} {r : ℝ≥0∞} (hr : 0 < r) (A : Set X) :
    coverCost d r A ≤ μH[d] A := by
  rw [hausdorffMeasure_eq_iSup_coverCost]
  exact le_iSup₂ (f := fun r (_ : 0 < r) => coverCost d r A) r hr

/-- Near-optimal covers at every positive scale.  The `coverCost` form of the extraction used by
`Analysis/HausdorffSlicing.lean`; both read off `Measure.hausdorffMeasure_apply`. -/
theorem exists_cover_familyCost_lt {d : ℝ} {r c : ℝ≥0∞} {A : Set X} (hr : 0 < r)
    (hc : μH[d] A < c) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧ familyCost d T < c := by
  obtain ⟨T, h⟩ := iInf_lt_iff.1 ((coverCost_le_hausdorffMeasure hr A).trans_lt hc)
  obtain ⟨hcov, h⟩ := iInf_lt_iff.1 h
  obtain ⟨hdiam, hcost⟩ := iInf_lt_iff.1 h
  exact ⟨T, hcov, hdiam, hcost⟩

/-- Thickening radii that raise the cost of one cover piece by at most a prescribed amount and stay
inside a prescribed room. -/
theorem exists_thickening_radius {d : ℝ} (hd : 0 ≤ d) {δ : ℝ≥0∞} (hδ : δ ≠ ∞) {σ R : ℝ≥0∞}
    (hσ : σ ≠ 0) (hR : R ≠ 0) :
    ∃ b : ℝ≥0, 0 < b ∧ 2 * (b : ℝ≥0∞) ≤ R ∧ (δ + 2 * (b : ℝ≥0∞)) ^ d ≤ δ ^ d + σ := by
  have hmul : Tendsto (fun b : ℝ≥0 => 2 * (b : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞))
      (ENNReal.continuous_coe.tendsto (0 : ℝ≥0)) (Or.inr (by simp))
    simpa using h
  have hcont : Tendsto (fun b : ℝ≥0 => (δ + 2 * (b : ℝ≥0∞)) ^ d) (𝓝 0) (𝓝 (δ ^ d)) := by
    have h := (ENNReal.continuous_rpow_const (y := d)).tendsto (δ + 0)
    have h2 := h.comp (hmul.const_add δ)
    simpa [Function.comp_def] using h2
  have h1 : ∀ᶠ b : ℝ≥0 in 𝓝[>] 0, (δ + 2 * (b : ℝ≥0∞)) ^ d ≤ δ ^ d + σ :=
    (hcont.eventually_le_const
      (ENNReal.lt_add_right (ENNReal.rpow_ne_top_of_nonneg hd hδ) hσ)).filter_mono
        nhdsWithin_le_nhds
  have h2 : ∀ᶠ b : ℝ≥0 in 𝓝[>] 0, 2 * (b : ℝ≥0∞) ≤ R :=
    (hmul.eventually_le_const (pos_iff_ne_zero.2 hR)).filter_mono nhdsWithin_le_nhds
  obtain ⟨b, ⟨hb₁, hb₂⟩, hbpos⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  exact ⟨b, hbpos, hb₂, hb₁⟩

/-- Every open-cover cost at a positive scale is at most `μH[d]`: thicken a near-optimal cover by
summably small radii.  The room left by the scale absorbs the diameter increase, and
`ENNReal.exists_pos_sum_of_countable` absorbs the cost increase. -/
theorem openCoverCost_le_hausdorffMeasure {d : ℝ} (hd : 0 ≤ d) {r : ℝ≥0∞} (hr : 0 < r)
    (A : Set X) : openCoverCost d r A ≤ μH[d] A := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε htop => ?_
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
  set r₀ : ℝ≥0∞ := min (r / 2) 1 with hr₀
  have hr₀pos : 0 < r₀ := lt_min (ENNReal.half_pos hr.ne') one_pos
  have hr₀top : r₀ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hr₀add : r₀ + r₀ ≤ r := by
    calc r₀ + r₀ ≤ r / 2 + r / 2 := by gcongr <;> exact min_le_left _ _
      _ = r := ENNReal.add_halves r
  obtain ⟨C, hCcov, hCdiam, hCcost⟩ := exists_cover_familyCost_lt (d := d) (A := A) hr₀pos
    (ENNReal.lt_add_right htop.ne (ENNReal.half_pos hε0).ne')
  obtain ⟨σ, hσpos, hσsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ε := (ε : ℝ≥0∞) / 2) (ENNReal.half_pos hε0).ne' ℕ
  choose b hbpos hbR hbcost using fun i => exists_thickening_radius hd
    (ne_top_of_le_ne_top hr₀top (hCdiam i)) (σ := (σ i : ℝ≥0∞)) (R := r₀)
    (ENNReal.coe_ne_zero.2 (hσpos i).ne') hr₀pos.ne'
  set U : ℕ → Set X := fun i => Metric.thickening (b i : ℝ) (C i) with hU
  have hUopen : ∀ i, IsOpen (U i) := fun i => Metric.isOpen_thickening
  have hUsub : ∀ i, C i ⊆ U i := fun i =>
    Metric.self_subset_thickening (by exact_mod_cast hbpos i) (C i)
  have hUdiam : ∀ i, Metric.ediam (U i) ≤ r := fun i =>
    (Metric.ediam_thickening_le (b i)).trans
      (le_trans (add_le_add (hCdiam i) (hbR i)) hr₀add)
  have hUcost : familyCost d U ≤ familyCost d C + ∑' i, (σ i : ℝ≥0∞) := by
    simp only [familyCost]
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rcases (C i).eq_empty_or_nonempty with hCi | hCi
    · simp [hU, hCi, Metric.thickening_empty]
    · have hUi : (U i).Nonempty := hCi.mono (hUsub i)
      rw [iSup_pos hUi, iSup_pos hCi]
      exact (ENNReal.rpow_le_rpow (Metric.ediam_thickening_le (b i)) hd).trans (hbcost i)
  calc openCoverCost d r A
      ≤ familyCost d U :=
        openCoverCost_le hUopen (hCcov.trans (Set.iUnion_mono hUsub)) hUdiam
    _ ≤ familyCost d C + ∑' i, (σ i : ℝ≥0∞) := hUcost
    _ ≤ (μH[d] A + (ε : ℝ≥0∞) / 2) + (ε : ℝ≥0∞) / 2 := add_le_add hCcost.le hσsum.le
    _ = μH[d] A + (ε : ℝ≥0∞) := by rw [add_assoc, ENNReal.add_halves]

/-- The open-cover costs have the same scale limit as the cover costs: their supremum over the
scales `(n + 1)⁻¹` is `μH[d]`. -/
theorem iSup_openCoverCost_eq_hausdorffMeasure {d : ℝ} (hd : 0 ≤ d) (A : Set X) :
    ⨆ n : ℕ, openCoverCost d ((n : ℝ≥0∞) + 1)⁻¹ A = μH[d] A := by
  refine le_antisymm (iSup_le fun n => openCoverCost_le_hausdorffMeasure hd
    (ENNReal.inv_pos.2 (by simp)) A) ?_
  rw [hausdorffMeasure_eq_iSup_coverCost]
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hρ.ne'
  refine le_trans (coverCost_mono_scale ?_ A) (le_trans (coverCost_le_openCoverCost A)
    (le_iSup (fun n : ℕ => openCoverCost d ((n : ℝ≥0∞) + 1)⁻¹ A) n))
  exact le_trans (ENNReal.inv_le_inv.2 (by simp)) hn.le

end Content

section Slice

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- An open set containing one level slice of a compact set contains all nearby level slices: the
compact remainder outside it keeps the function at a positive distance from the level. -/
theorem isOpen_setOf_slice_subset {S U : Set X} {u : X → ℝ} (hS : IsCompact S) (hU : IsOpen U)
    (hu : Continuous u) : IsOpen {t : ℝ | S ∩ {x | u x = t} ⊆ U} := by
  refine isOpen_iff_mem_nhds.2 fun t ht => ?_
  rcases (S \ U).eq_empty_or_nonempty with he | hne
  · have huniv : {t : ℝ | S ∩ {x | u x = t} ⊆ U} = Set.univ := by
      refine Set.eq_univ_of_forall fun s x hx => ?_
      by_contra hxU
      exact (Set.eq_empty_iff_forall_notMem.1 he) x ⟨hx.1, hxU⟩
    rw [huniv]
    exact Filter.univ_mem
  · obtain ⟨x₀, hx₀, hmin⟩ := (hS.diff hU).exists_isMinOn hne
      ((continuous_abs.comp (hu.sub continuous_const)).continuousOn)
    have hne₀ : u x₀ ≠ t := fun h => hx₀.2 (ht ⟨hx₀.1, h⟩)
    have hρ : 0 < |u x₀ - t| := abs_pos.2 (sub_ne_zero.2 hne₀)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hρ) fun s hs x hx => ?_
    by_contra hxU
    have hle : |u x₀ - t| ≤ |u x - t| := isMinOn_iff.1 hmin x ⟨hx.1, hxU⟩
    rw [hx.2] at hle
    exact absurd (Real.dist_eq s t ▸ Metric.mem_ball.1 hs) (not_lt.2 hle)

omit [MeasurableSpace X] [BorelSpace X] in
/-- At a fixed scale, the open-cover cost of the level slices of a compact set is upper
semicontinuous in the level.  Restricting to open covers is what makes this true: the same cover
serves all nearby slices. -/
theorem upperSemicontinuous_openCoverCost_slice (d : ℝ) (r : ℝ≥0∞) {S : Set X} {u : X → ℝ}
    (hS : IsCompact S) (hu : Continuous u) :
    UpperSemicontinuous fun t : ℝ => openCoverCost d r (S ∩ {x | u x = t}) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  refine isOpen_iff_mem_nhds.2 fun t ht => ?_
  obtain ⟨T, hopen, hcov, hdiam, hcost⟩ := openCoverCost_lt_iff.1 ht
  refine Filter.mem_of_superset
    ((isOpen_setOf_slice_subset hS (isOpen_iUnion hopen) hu).mem_nhds hcov) fun s hs => ?_
  exact (openCoverCost_le hopen hs hdiam).trans_lt hcost

/-- **Compact slices are measurable.**  For `S` compact and `u` continuous, the `d`-dimensional
Hausdorff measure of the level slices of `S` is a Borel measurable function of the level.

No Lipschitz hypothesis on `u`, no finiteness of any measure of `S`, and `d = 0` is allowed. This
is a statement about compact `S` only: it asserts nothing for a general Borel set. -/
theorem measurable_hausdorffMeasure_inter_levelSet {d : ℝ} (hd : 0 ≤ d) {S : Set X} {u : X → ℝ}
    (hS : IsCompact S) (hu : Continuous u) :
    Measurable fun t : ℝ => μH[d] (S ∩ {x | u x = t}) := by
  have hrw : (fun t : ℝ => μH[d] (S ∩ {x | u x = t}))
      = fun t : ℝ => ⨆ n : ℕ, openCoverCost d ((n : ℝ≥0∞) + 1)⁻¹ (S ∩ {x | u x = t}) := by
    funext t
    exact (iSup_openCoverCost_eq_hausdorffMeasure hd _).symm
  rw [hrw]
  exact Measurable.iSup fun n =>
    (upperSemicontinuous_openCoverCost_slice d _ hS hu).measurable

end Slice

end FunctionalInequalities.Analysis
