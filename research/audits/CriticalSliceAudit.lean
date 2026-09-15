import FunctionalInequalities.KLS.Geometry.CriticalSlice

/-!
# Strict audit client for the critical slices of a `C¹` function (obligation `L10`)

Independent client of `KLS/Geometry/CriticalSlice.lean`.  `target` states the route's `L10`
quantifier for quantifier and proves it; `target_of_not_completeSpace` drops the unused
`[CompleteSpace V]`.

**`L10` is not Sard's theorem.**  Sard asserts that the set of critical *values* is Lebesgue-null
in `ℝ`, needs regularity `C^(finrank)` in general, and remains an unproved obligation
(`Analysis.sard` in `KLS/WIP/AnalyticPrerequisites.lean`, which this client does not import and
does not touch).  `L10` is about the codimension-one measure of the critical *part of each slice*.
`constant_exceptional_level` makes the difference concrete: for a constant function the critical
set is everything, so the slice at the attained value is the whole line and has **nonzero** surface
measure — the conclusion really is only almost everywhere, and the exceptional slice can be large.

`ae_slice_eq_regular` is the form obligation `L11` will consume: almost every slice may be computed
after discarding the critical set.  `not_lipschitz` applies `L10` to a `C¹` function that is not
globally Lipschitz.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace CriticalSliceAudit

/-! ### The obligation itself -/

-- The statement text of `L10` in `research/decisions/2026-09-15-weighted-coarea-route.md`.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ}, ContDiff ℝ 1 u →
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0)

/-- The round's target, proved. -/
theorem target : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ}, ContDiff ℝ 1 u →
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  intro V _ _ _ _ _ _ u hu
  exact ae_surfaceMeasure_critical_inter_levelSet_eq_zero hu

/-- The same conclusion without `[CompleteSpace V]`. -/
theorem target_of_not_completeSpace : ∀ {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ}, ContDiff ℝ 1 u →
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  intro V _ _ _ _ _ u hu
  exact ae_surfaceMeasure_critical_inter_levelSet_eq_zero hu

/-! ### Consumers -/

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The form obligation `L11` consumes: almost every slice is unchanged by discarding the critical
set.  No measurability, boundedness or finiteness of `S` is assumed. -/
theorem ae_slice_eq_regular (S : Set V) {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (S ∩ {x | u x = t})
      = surfaceMeasure V ((S \ {x : V | fderiv ℝ u x = 0}) ∩ {x | u x = t}) := by
  filter_upwards [ae_surfaceMeasure_critical_inter_levelSet_eq_zero (V := V) hu] with t ht
  refine le_antisymm ?_ (measure_mono (Set.inter_subset_inter_left _ Set.sdiff_subset))
  have hsplit : S ∩ {x | u x = t}
      = ((S \ {x : V | fderiv ℝ u x = 0}) ∩ {x | u x = t})
        ∪ ((S ∩ {x : V | fderiv ℝ u x = 0}) ∩ {x | u x = t}) := by
    rw [← Set.union_inter_distrib_right, Set.sdiff_union_inter]
  have hnull : surfaceMeasure V ((S ∩ {x : V | fderiv ℝ u x = 0}) ∩ {x | u x = t}) = 0 :=
    measure_mono_null (Set.inter_subset_inter_left _ Set.inter_subset_right) ht
  calc surfaceMeasure V (S ∩ {x | u x = t})
      ≤ surfaceMeasure V ((S \ {x : V | fderiv ℝ u x = 0}) ∩ {x | u x = t})
        + surfaceMeasure V ((S ∩ {x : V | fderiv ℝ u x = 0}) ∩ {x | u x = t}) := by
        rw [hsplit]; exact measure_union_le _ _
    _ = _ := by rw [hnull, add_zero]

end Consumers

/-! ### The exceptional level is real, and this is not Sard -/

theorem surfaceMeasure_real_singleton (t : ℝ) : surfaceMeasure ℝ ({t} : Set ℝ) = 1 := by
  have hn : Module.finrank ℝ ℝ = 1 := by simp
  rw [surfaceMeasure, hn, show (1 : ℕ) - 1 = 0 from rfl, hausdorffNormalized,
    Measure.smul_apply, smul_eq_mul, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton]
  simp [unitBallVolume]

/-- A constant function on the line: the critical set is everything, so the slice at the attained
value is the whole line, whose surface measure is nonzero.  `L10` therefore cannot be strengthened
from "almost every level" to "every level", and the critical set itself carries no smallness. -/
theorem constant_exceptional_level :
    surfaceMeasure ℝ ({x : ℝ | fderiv ℝ (fun _ : ℝ => (0 : ℝ)) x = 0}
      ∩ {x : ℝ | (fun _ : ℝ => (0 : ℝ)) x = 0}) ≠ 0 := by
  have hset : {x : ℝ | fderiv ℝ (fun _ : ℝ => (0 : ℝ)) x = 0}
      ∩ {x : ℝ | (fun _ : ℝ => (0 : ℝ)) x = 0} = Set.univ := by
    ext x; simp
  rw [hset]
  intro hzero
  have h1 : surfaceMeasure ℝ ({(0 : ℝ)} : Set ℝ) = 0 :=
    measure_mono_null (Set.subset_univ _) hzero
  rw [surfaceMeasure_real_singleton] at h1
  exact one_ne_zero h1

/-- `L10` for a `C¹` function that is not globally Lipschitz: no Lipschitz hypothesis is used, the
Eilenberg bound being applied only on the pieces where the derivative is small. -/
theorem not_lipschitz :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure ℝ ({x : ℝ | fderiv ℝ Real.exp x = 0} ∩ {x : ℝ | Real.exp x = t}) = 0 :=
  ae_surfaceMeasure_critical_inter_levelSet_eq_zero Real.contDiff_exp

/-! ### The Eilenberg-round statement is preserved -/

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

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.KLS.isClosed_critical
#print axioms FunctionalInequalities.KLS.exists_lipschitzOnWith_critical_cover
#print axioms FunctionalInequalities.KLS.ae_surfaceMeasure_critical_ball_eq_zero
#print axioms FunctionalInequalities.KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero
#print axioms CriticalSliceAudit.target
#print axioms CriticalSliceAudit.target_of_not_completeSpace
#print axioms CriticalSliceAudit.ae_slice_eq_regular
#print axioms CriticalSliceAudit.surfaceMeasure_real_singleton
#print axioms CriticalSliceAudit.constant_exceptional_level
#print axioms CriticalSliceAudit.not_lipschitz
#print axioms CriticalSliceAudit.preserved_exists_measurable_majorant

end CriticalSliceAudit
