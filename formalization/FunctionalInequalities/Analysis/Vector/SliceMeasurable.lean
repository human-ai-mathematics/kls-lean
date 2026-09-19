import FunctionalInequalities.Analysis.HausdorffContent
import FunctionalInequalities.Analysis.Vector.HausdorffSlicing
import FunctionalInequalities.Analysis.LevelSet
import FunctionalInequalities.KLS.Geometry.Surface.Slicing
import FunctionalInequalities.Analysis.Graph.OpenIntegral

/-!
# Compact slices and weighted slice measurability in codimension `m`

The last structural gap in the codimension-`m` slicing layer.  `Analysis/HausdorffContent.lean`
proves that the scalewise **open**-cover costs have `μH[d]` as their scale limit, and that at a
fixed scale the open-cover cost of the slices of a compact set is upper semicontinuous in the
**real** level.  The cover-cost half is about the ambient space only and is reused verbatim; only
the slice half mentions the target, and this module redoes it for a metric target.

The argument is unchanged: an open set containing one slice of a compact set contains all nearby
slices, because the compact remainder outside it keeps the map at a positive distance from the
level.  In the real-valued case that distance is `|u x - t|`; here it is `dist (u x) t`, and nothing
else in the proof changes.  A countable supremum of upper semicontinuous functions is measurable,
which gives `measurable_hausdorffMeasure_inter_levelSet_vector`.

With the Eilenberg inequality of `Analysis/Vector/HausdorffSlicing.lean` this completes the chain the
coarea route needs, exactly as `KLS/Geometry/Surface/Slicing.lean` does in codimension one: inner
regularity exhausts a Borel set by compacts up to a Lebesgue-null remainder, the compact pieces are
handled by upper semicontinuity and the remainder by null slicing, and increasing simple functions
carry the result to an arbitrary measurable weight.  The conclusion,
`aemeasurable_setLIntegral_inter_levelSet_vector`, is weighted slice measurability **with no
regularity hypothesis on `u`** — only a Lipschitz bound on the set.

**No coarea formula is proved here**, and nothing about the critical set: what this removes is the
regularity hypothesis from the *measurability* half, not from the coarea equality.
-/

noncomputable section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

section Slice

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {W : Type*} [MetricSpace W]

omit [MeasurableSpace X] [BorelSpace X] in
/-- An open set containing one level slice of a compact set contains all nearby level slices: the
compact remainder outside it keeps the map at a positive distance from the level.  The real-valued
case uses `|u x - t|`; here it is `dist (u x) t`, and nothing else changes. -/
theorem isOpen_setOf_slice_subset_vector {S U : Set X} {u : X → W} (hS : IsCompact S)
    (hU : IsOpen U) (hu : Continuous u) : IsOpen {t : W | S ∩ {x | u x = t} ⊆ U} := by
  refine isOpen_iff_mem_nhds.2 fun t ht => ?_
  rcases (S \ U).eq_empty_or_nonempty with he | hne
  · have huniv : {t : W | S ∩ {x | u x = t} ⊆ U} = Set.univ := by
      refine Set.eq_univ_of_forall fun s x hx => ?_
      by_contra hxU
      exact (Set.eq_empty_iff_forall_notMem.1 he) x ⟨hx.1, hxU⟩
    rw [huniv]
    exact Filter.univ_mem
  · obtain ⟨x₀, hx₀, hmin⟩ := (hS.diff hU).exists_isMinOn hne
      ((continuous_dist.comp (hu.prodMk continuous_const)).continuousOn)
    have hne₀ : u x₀ ≠ t := fun h => hx₀.2 (ht ⟨hx₀.1, h⟩)
    have hρ : 0 < dist (u x₀) t := dist_pos.2 hne₀
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hρ) fun s hs x hx => ?_
    by_contra hxU
    have hle : dist (u x₀) t ≤ dist (u x) t := isMinOn_iff.1 hmin x ⟨hx.1, hxU⟩
    rw [hx.2] at hle
    exact absurd (Metric.mem_ball.1 hs) (not_lt.2 hle)

omit [MeasurableSpace X] [BorelSpace X] in
/-- At a fixed scale, the open-cover cost of the level slices of a compact set is upper
semicontinuous in the level, for a metric target.  Restricting to open covers is what makes this
true: the same cover serves all nearby slices. -/
theorem upperSemicontinuous_openCoverCost_slice_vector (d : ℝ) (r : ℝ≥0∞) {S : Set X} {u : X → W}
    (hS : IsCompact S) (hu : Continuous u) :
    UpperSemicontinuous fun t : W => openCoverCost d r (S ∩ {x | u x = t}) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  refine isOpen_iff_mem_nhds.2 fun t ht => ?_
  obtain ⟨T, hopen, hcov, hdiam, hcost⟩ := openCoverCost_lt_iff.1 ht
  refine Filter.mem_of_superset
    ((isOpen_setOf_slice_subset_vector hS (isOpen_iUnion hopen) hu).mem_nhds hcov) fun s hs => ?_
  exact (openCoverCost_le hopen hs hdiam).trans_lt hcost

/-- **Compact slices are measurable in codimension `m`.**  For `S` compact and `u` continuous with
values in a metric space, the `d`-dimensional Hausdorff measure of the level slices of `S` is a
Borel measurable function of the level.

No Lipschitz hypothesis on `u`, no finiteness of any measure of `S`, and `d = 0` is allowed.  This
is a statement about compact `S` only. -/
theorem measurable_hausdorffMeasure_inter_levelSet_vector [MeasurableSpace W]
    [OpensMeasurableSpace W] {d : ℝ} (hd : 0 ≤ d) {S : Set X} {u : X → W}
    (hS : IsCompact S) (hu : Continuous u) :
    Measurable fun t : W => μH[d] (S ∩ {x | u x = t}) := by
  have hrw : (fun t : W => μH[d] (S ∩ {x | u x = t}))
      = fun t : W => ⨆ n : ℕ, openCoverCost d ((n : ℝ≥0∞) + 1)⁻¹ (S ∩ {x | u x = t}) := by
    funext t
    exact (iSup_openCoverCost_eq_hausdorffMeasure hd _).symm
  rw [hrw]
  exact Measurable.iSup fun n =>
    (upperSemicontinuous_openCoverCost_slice_vector d _ hS hu).measurable

end Slice

/-! ### The normalized convention, and Borel sets -/

section Normalized

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] in
/-- Compact slices are measurable in the normalized convention: only a positive scalar is
added. -/
theorem measurable_hausdorffNormalized_inter_levelSet_vector (k : ℕ) {S : Set V} {u : V → W}
    (hS : IsCompact S) (hu : Continuous u) :
    Measurable fun t : W => KLS.hausdorffNormalized V k (S ∩ {x | u x = t}) := by
  have hrw : (fun t : W => KLS.hausdorffNormalized V k (S ∩ {x | u x = t}))
      = fun t : W => ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k)
          * μH[(k : ℝ)] (S ∩ {x | u x = t}) := by
    funext t
    rw [KLS.hausdorffNormalized, Measure.smul_apply, smul_eq_mul]
  rw [hrw]
  exact measurable_const.mul
    (measurable_hausdorffMeasure_inter_levelSet_vector (Nat.cast_nonneg k) hS hu)

omit [FiniteDimensional ℝ W] in
/-- A Lebesgue-null set is null in the top normalized dimension. -/
theorem hausdorffNormalized_finrank_eq_zero_of_volume_eq_zero {N : Set V}
    (h : (volume : Measure V) N = 0) : KLS.hausdorffNormalized V (finrank ℝ V) N = 0 := by
  rw [hausdorffNormalized_eq_zero_iff, hausdorffMeasure_finrank_eq_smul_volume V,
    Measure.smul_apply, smul_eq_mul, h, mul_zero]

/-- **Borel sets have almost everywhere measurable slices in codimension `m`.**  For `S` measurable
and `u` continuous and Lipschitz on `S`, the slice function is almost everywhere equal to an
explicit measurable function: the supremum of the slice measures of an increasing sequence of
compact subsets of `S`.

Both ingredients are used and neither suffices alone: the compact pieces are handled by
`measurable_hausdorffNormalized_inter_levelSet_vector` and the Lebesgue-null remainder by the
Eilenberg null slicing.  **No regularity of `u` is assumed** — only a Lipschitz bound on `S`. -/
theorem aemeasurable_hausdorffNormalized_inter_levelSet_vector {u : V → W} {K : ℝ≥0} {S : Set V}
    {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hc : Continuous u)
    (hu : LipschitzOnWith K u S) (hS : MeasurableSet S) :
    AEMeasurable (fun t : W => KLS.hausdorffNormalized V k (S ∩ {x | u x = t}))
      (volume : Measure W) := by
  obtain ⟨C, hCcompact, hCsub, hCnull⟩ := KLS.exists_isCompact_seq_volume_sdiff_eq_zero hS
  have hAcompact : ∀ n, IsCompact (Set.accumulate C n) := fun n => by
    rw [Set.accumulate_def]
    exact (Set.finite_Iic n).isCompact_biUnion fun i _ => hCcompact i
  refine ⟨fun t => ⨆ n, KLS.hausdorffNormalized V k (Set.accumulate C n ∩ {x | u x = t}),
    Measurable.iSup fun n =>
      measurable_hausdorffNormalized_inter_levelSet_vector k (hAcompact n) hc, ?_⟩
  have hnull : KLS.hausdorffNormalized V (k + finrank ℝ W) (S \ ⋃ n, C n) = 0 := by
    rw [hk]
    exact hausdorffNormalized_finrank_eq_zero_of_volume_eq_zero hCnull
  filter_upwards [ae_hausdorffNormalized_inter_levelSet_eq_zero_vector
    (hu.mono Set.sdiff_subset) hnull] with t ht
  have hWsub : (⋃ n, C n) ⊆ S := Set.iUnion_subset hCsub
  have hacc : ∀ n, Set.accumulate (fun i => C i ∩ {x | u x = t}) n
      = Set.accumulate C n ∩ {x | u x = t} := by
    intro n
    simp only [Set.accumulate_def, Set.iUnion_inter]
  have hW : KLS.hausdorffNormalized V k ((⋃ n, C n) ∩ {x | u x = t})
      = ⨆ n, KLS.hausdorffNormalized V k (Set.accumulate C n ∩ {x | u x = t}) := by
    rw [Set.iUnion_inter, measure_iUnion_eq_iSup_accumulate]
    exact iSup_congr fun n => by rw [hacc n]
  refine le_antisymm ?_ (hW ▸ measure_mono (Set.inter_subset_inter_left _ hWsub))
  calc KLS.hausdorffNormalized V k (S ∩ {x | u x = t})
      ≤ KLS.hausdorffNormalized V k ((S \ ⋃ n, C n) ∩ {x | u x = t})
          + KLS.hausdorffNormalized V k ((⋃ n, C n) ∩ {x | u x = t}) := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        rw [← Set.union_inter_distrib_right, Set.sdiff_union_of_subset hWsub]
    _ = ⨆ n, KLS.hausdorffNormalized V k (Set.accumulate C n ∩ {x | u x = t}) := by
        rw [ht, zero_add, hW]

/-- **Measurable weights, almost everywhere measurable slice integrals, in codimension `m`.**  The
weighted form, by increasing simple functions: each simple weight turns the slice integral into a
finite sum of slice measures of the measurable sets `S ∩ s ⁻¹' {c}`, and two monotone limits recover
the general weight.

No integrability, finiteness or boundedness of `g` is assumed, and `g = ∞` is allowed.  **No
regularity of `u` is assumed** — this is the statement that removes the regularity hypothesis from
the measurability half of the codimension-`m` coarea layer. -/
theorem aemeasurable_setLIntegral_inter_levelSet_vector {u : V → W} {K : ℝ≥0} {S : Set V}
    {g : V → ℝ≥0∞} {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hc : Continuous u)
    (hu : LipschitzOnWith K u S) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) := by
  have hstep : ∀ n : ℕ, AEMeasurable (fun t : W =>
      (SimpleFunc.eapprox g n).lintegral
        ((KLS.hausdorffNormalized V k).restrict (S ∩ {x | u x = t}))) (volume : Measure W) := by
    intro n
    have hrw : (fun t : W => (SimpleFunc.eapprox g n).lintegral
          ((KLS.hausdorffNormalized V k).restrict (S ∩ {x | u x = t})))
        = ∑ c ∈ (SimpleFunc.eapprox g n).range, fun t : W =>
            c * KLS.hausdorffNormalized V k
              ((S ∩ SimpleFunc.eapprox g n ⁻¹' {c}) ∩ {x | u x = t}) := by
      funext t
      rw [SimpleFunc.lintegral, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hset : (SimpleFunc.eapprox g n ⁻¹' {c}) ∩ (S ∩ {x | u x = t})
          = (S ∩ SimpleFunc.eapprox g n ⁻¹' {c}) ∩ {x | u x = t} := by
        ext x; simp only [Set.mem_inter_iff]; tauto
      rw [Measure.restrict_apply ((SimpleFunc.eapprox g n).measurableSet_preimage _), hset]
    rw [hrw]
    exact Finset.aemeasurable_sum _ fun c _ =>
      (aemeasurable_hausdorffNormalized_inter_levelSet_vector hk hc
        (hu.mono Set.inter_subset_left)
        (hS.inter ((SimpleFunc.eapprox g n).measurableSet_preimage {c}))).const_mul c
  have hsup : (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      = fun t : W => ⨆ n : ℕ, (SimpleFunc.eapprox g n).lintegral
          ((KLS.hausdorffNormalized V k).restrict (S ∩ {x | u x = t})) := by
    funext t
    exact lintegral_eq_iSup_eapprox_lintegral hg
  rw [hsup]
  exact AEMeasurable.iSup hstep

/-- **Weighted slices on an open `C¹` domain are almost everywhere measurable, in codimension `m`,
with no regularity hypothesis.**  The map is `C¹` on the open set only, and the Borel set is any
measurable subset of it; local `C¹` representatives and disjoint Borel pieces reduce the statement
to the Lipschitz-on-a-set form above.

This is the codimension-`m` analogue of
`KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`.  **It asserts no coarea equality**,
and unlike the chart route of `Analysis/Vector/RegularCoarea.lean` it needs **no surjectivity of the
differential**: the critical part of `O` is covered by the statement. -/
theorem aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector {O S : Set V} {u : V → W}
    {g : V → ℝ≥0∞} {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · simp [hSe]
  choose ρ w hρ hballO hwC hwEq using fun z : O =>
    Analysis.exists_contDiff_one_eqOn_ball hO hu z.2
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : O => Metric.ball (z : V) (ρ z)) (fun _ => Metric.isOpen_ball)
  have hOcov : ⋃ z : O, Metric.ball (z : V) (ρ z) = O :=
    Set.Subset.antisymm (Set.iUnion_subset fun z => hballO z) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hρ ⟨y, hy⟩)⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, Metric.ball (z : V) (ρ z) := by
      rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set V := fun n => Metric.ball ((σ n : O) : V) (ρ (σ n))
  have hBcov : O ⊆ ⋃ n, B n := by
    rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  set P : ℕ → Set V := disjointed fun n => S ∩ B n with hP
  have hPmeas : ∀ n, MeasurableSet (P n) :=
    MeasurableSet.disjointed fun n => hS.inter Metric.isOpen_ball.measurableSet
  have hPdisj : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPsub : ∀ n, P n ⊆ B n := fun n =>
    (disjointed_subset _ n).trans Set.inter_subset_right
  have hPunion : ⋃ n, P n = S := by
    rw [hP, iUnion_disjointed, ← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left (hSO.trans hBcov)
  have hslice : ∀ n t, P n ∩ {x | u x = t} = P n ∩ {x | w (σ n) x = t} := by
    intro n t
    ext x
    constructor <;> rintro ⟨hx, ht⟩ <;>
      exact ⟨hx, by simpa [hwEq (σ n) (hPsub n hx)] using ht⟩
  have hm : ∀ n, AEMeasurable
      (fun t : W => ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) := by
    intro n
    obtain ⟨L, hL⟩ := (hwC (σ n)).contDiffOn.exists_lipschitzOnWith
      (by simp) (convex_closedBall ((σ n : O) : V) (ρ (σ n)))
      (isCompact_closedBall ((σ n : O) : V) (ρ (σ n)))
    simp_rw [hslice]
    exact aemeasurable_setLIntegral_inter_levelSet_vector hk (hwC (σ n)).continuous
      (hL.mono fun x hx => Metric.ball_subset_closedBall (hPsub n hx)) (hPmeas n) hg
  have heq : ∀ t, (∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      = ∑' n, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k) := by
    intro t
    rw [← hPunion, Set.iUnion_inter]
    apply lintegral_iUnion
    · intro n
      rw [hslice]
      exact (hPmeas n).inter ((hwC (σ n)).continuous.measurable (measurableSet_singleton t))
    · intro i j hij
      exact (hPdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  simp_rw [heq]
  exact AEMeasurable.tsum hm

end Normalized

end FunctionalInequalities.Analysis
