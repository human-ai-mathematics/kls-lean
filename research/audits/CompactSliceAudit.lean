import FunctionalInequalities.Analysis.Hausdorff.SurfaceSlicing

/-!
# Strict audit client for compact-slice measurability (obligation `L3`)

Independent client of `Analysis/Hausdorff/SurfaceSlicing.lean` and `Analysis/Hausdorff/Content.lean`.
`target` states the route's `L3` quantifier for quantifier and proves it;
`target_of_not_finiteDimensional` proves the same conclusion with both `[CompleteSpace V]` and
`[FiniteDimensional ℝ V]` dropped, so the library statement is strictly stronger than `L3` asks.

The consumers are not repetitions of the proof.  `eilenberg_compact` packages `L1` with `L3` into
the statement `L4`/`L5` will build on: for compact `S` and Lipschitz `u` the slice function is
measurable **and** its Lebesgue integral obeys the Eilenberg bound.  `exp_not_lipschitz` applies
`L3` to a continuous function that is not globally Lipschitz, and `measurableSet_slice_lt` uses it
as a measurability statement.  The final group computes both sides of `eilenberg_compact` on the
unit interval of the line, where the fibre measure is `ℋ⁰`: the integral of the slice function is
exactly `1`, the Eilenberg bound is `2`, and neither side is vacuous.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace CompactSliceAudit

/-! ### The obligation itself -/

-- The statement text of `L3` in `research/decisions/2026-09-15-weighted-coarea-route.md`.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
    Measurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t})))

/-- The round's target, proved. -/
theorem target : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
    Measurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t})) := by
  intro V _ _ _ _ _ _ u S hu hS
  exact measurable_surfaceMeasure_inter_levelSet hu hS

/-- The same conclusion without `[CompleteSpace V]` and without `[FiniteDimensional ℝ V]`:
`surfaceMeasure` only reads `Module.finrank`, so no finite-dimensionality is needed. -/
theorem target_of_not_finiteDimensional : ∀ {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
    Measurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t})) := by
  intro V _ _ _ _ u S hu hS
  exact measurable_surfaceMeasure_inter_levelSet hu hS

/-! ### Consumers -/

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `L1` and `L3` together, in the form `L4`/`L5` will consume: for a compact set and a function
Lipschitz on it, the slice function is measurable **and** satisfies the Eilenberg bound.  The
integral on the left is a genuine integral of a measurable function, which is exactly what the
majorant bound alone does not provide. -/
theorem eilenberg_compact {u : V → ℝ} {K : ℝ≥0} {S : Set V} (hu : LipschitzOnWith K u S)
    (hc : Continuous u) (hS : IsCompact S) :
    Measurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) ∧
      (∫⁻ t, surfaceMeasure V (S ∩ {x | u x = t}) ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S := by
  refine ⟨measurable_surfaceMeasure_inter_levelSet hc hS, ?_⟩
  obtain ⟨F, _, hFdom, hFint⟩ := exists_measurable_majorant hu
  exact (lintegral_mono hFdom).trans hFint

omit [FiniteDimensional ℝ V] in
/-- Used as a measurability statement: the levels whose slice is small form a measurable set. -/
theorem measurableSet_slice_lt {u : V → ℝ} {S : Set V} (hu : Continuous u) (hS : IsCompact S)
    (c : ℝ≥0∞) : MeasurableSet {t : ℝ | surfaceMeasure V (S ∩ {x | u x = t}) < c} :=
  measurable_surfaceMeasure_inter_levelSet hu hS measurableSet_Iio

end Consumers

/-- No Lipschitz hypothesis on `u`: the exponential is continuous and not globally Lipschitz. -/
theorem exp_not_lipschitz :
    Measurable (fun t : ℝ => surfaceMeasure ℝ (Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | Real.exp x = t})) :=
  measurable_surfaceMeasure_inter_levelSet Real.continuous_exp isCompact_Icc

/-! ### Both sides are computed on the unit interval of the line -/

/-- On the line the fibre measure is `ℋ⁰`, the counting measure. -/
theorem surfaceMeasure_real_singleton (t : ℝ) : surfaceMeasure ℝ ({t} : Set ℝ) = 1 := by
  have hn : Module.finrank ℝ ℝ = 1 := by simp
  rw [surfaceMeasure, hn, show (1 : ℕ) - 1 = 0 from rfl, hausdorffNormalized,
    Measure.smul_apply, smul_eq_mul, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton]
  simp [unitBallVolume]

theorem slice_Icc (t : ℝ) :
    surfaceMeasure ℝ (Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | id x = t})
      = (Set.Icc (0 : ℝ) 1).indicator (fun _ => 1) t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · have hset : Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | id x = t} = {t} := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, id]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ ht, h⟩⟩
    rw [hset, surfaceMeasure_real_singleton, Set.indicator_of_mem ht]
  · have hset : Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | id x = t} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ht ?_
      exact hx.2 ▸ hx.1
    rw [hset, measure_empty, Set.indicator_of_notMem ht]

/-- The left-hand side of `eilenberg_compact` is exactly `1` here: one point per level of the unit
interval, and the levels form a set of Lebesgue measure one. -/
theorem lintegral_slice_Icc :
    (∫⁻ t, surfaceMeasure ℝ (Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | id x = t}) ∂(volume : Measure ℝ))
      = 1 := by
  rw [lintegral_congr slice_Icc, lintegral_indicator_const measurableSet_Icc,
    Real.volume_Icc]
  norm_num

/-- The right-hand side is `2`, so the Eilenberg bound holds with room to spare and neither side is
vacuous. -/
theorem eilenberg_bound_Icc :
    (∫⁻ t, surfaceMeasure ℝ (Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | id x = t}) ∂(volume : Measure ℝ))
      ≤ (eilenbergConstant ℝ : ℝ≥0∞) * (1 : ℝ≥0) * volume (Set.Icc (0 : ℝ) 1) :=
  (eilenberg_compact (K := 1) LipschitzWith.id.lipschitzOnWith continuous_id isCompact_Icc).2

/-! ### The Eilenberg-round statements are preserved -/

theorem preserved_exists_measurable_majorant :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V] {u : V → ℝ} {K : ℝ≥0} {S : Set V},
      LipschitzOnWith K u S →
      ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
        (∀ t, surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
        (∫⁻ t, F t ∂(volume : Measure ℝ))
          ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S := by
  intro V _ _ _ _ _ u K S hu
  exact exists_measurable_majorant (u := u) (K := K) (S := S) hu

theorem preserved_analysis_exists_measurable_majorant :
    ∀ {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
      {u : X → ℝ} {K : ℝ≥0} {S : Set X} {d : ℝ}, 0 ≤ d → LipschitzOnWith K u S →
      ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
        (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
        (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ 2 * (K : ℝ≥0∞) * μH[d + 1] S := by
  intro X _ _ _ u K S d hd hu
  exact Analysis.exists_measurable_majorant (u := u) (K := K) (S := S) (d := d) hd hu

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.familyCost
#print axioms FunctionalInequalities.Analysis.coverCost
#print axioms FunctionalInequalities.Analysis.openCoverCost
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_eq_iSup_coverCost
#print axioms FunctionalInequalities.Analysis.coverCost_le
#print axioms FunctionalInequalities.Analysis.openCoverCost_le
#print axioms FunctionalInequalities.Analysis.openCoverCost_lt_iff
#print axioms FunctionalInequalities.Analysis.coverCost_mono_scale
#print axioms FunctionalInequalities.Analysis.coverCost_le_openCoverCost
#print axioms FunctionalInequalities.Analysis.coverCost_le_hausdorffMeasure
#print axioms FunctionalInequalities.Analysis.exists_cover_familyCost_lt
#print axioms FunctionalInequalities.Analysis.exists_thickening_radius
#print axioms FunctionalInequalities.Analysis.openCoverCost_le_hausdorffMeasure
#print axioms FunctionalInequalities.Analysis.iSup_openCoverCost_eq_hausdorffMeasure
#print axioms FunctionalInequalities.Analysis.isOpen_setOf_slice_subset
#print axioms FunctionalInequalities.Analysis.upperSemicontinuous_openCoverCost_slice
#print axioms FunctionalInequalities.Analysis.measurable_hausdorffMeasure_inter_levelSet
#print axioms FunctionalInequalities.KLS.measurable_surfaceMeasure_inter_levelSet
#print axioms CompactSliceAudit.target
#print axioms CompactSliceAudit.target_of_not_finiteDimensional
#print axioms CompactSliceAudit.eilenberg_compact
#print axioms CompactSliceAudit.measurableSet_slice_lt
#print axioms CompactSliceAudit.exp_not_lipschitz
#print axioms CompactSliceAudit.surfaceMeasure_real_singleton
#print axioms CompactSliceAudit.slice_Icc
#print axioms CompactSliceAudit.lintegral_slice_Icc
#print axioms CompactSliceAudit.eilenberg_bound_Icc
#print axioms CompactSliceAudit.preserved_exists_measurable_majorant
#print axioms CompactSliceAudit.preserved_analysis_exists_measurable_majorant

end CompactSliceAudit
