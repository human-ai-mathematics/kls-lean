import FunctionalInequalities.Analysis.Hausdorff.SurfaceSlicing
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Strict audit client for Borel slices and measurable weights

Independent client of `Analysis/Hausdorff/SurfaceSlicing.lean`.  `target_L4`, `target_L5` and
`target_T1` state the obligations `L4` and `L5` and the first original target `T1` of
`research/audits/Coarea/WeightedRouteStatements.lean` quantifier for quantifier and
prove them; `target_L4_of_lipschitzOnWith` and `target_L5_of_lipschitzOnWith` prove the same
conclusions with `[CompleteSpace V]` dropped and global Lipschitz weakened to continuity plus
Lipschitz **on `S` only**, so the library statements are strictly stronger than the route asks.

`target_T1` preserves the contract of
`FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet`; the current implementation is in
`Analysis/Hausdorff/SurfaceSlicing.lean`. This client checks the route signature and its consumers.

The consumers are not repetitions of the proof.  `eilenberg_borel` packages the Eilenberg majorant
with the measurability of Borel slices into the Eilenberg bound for a measurable set with an
almost-everywhere measurable integrand.  `weighted_one` checks that the weighted statement at
weight `1` returns the unweighted one.  `infinite_volume` applies both statements to an unbounded
measurable set of infinite volume, and `top_weight` to a weight that is identically `∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace BorelSliceAudit

/-! ### The obligations themselves -/

-- The statement text of obligation `L4` of `Coarea/WeightedRouteStatements.lean`.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzWith K u → MeasurableSet S →
    AEMeasurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t}))
      (volume : Measure ℝ))

-- The statement text of obligation `L5` of `Coarea/WeightedRouteStatements.lean`.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ))

-- The exact statement text of target `T1` of `Coarea/WeightedRouteStatements.lean`.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ))

/-- Almost-everywhere measurability of Borel-set slices, proved. -/
theorem target_L4 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzWith K u → MeasurableSet S →
    AEMeasurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t}))
      (volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K S hu hS
  exact aemeasurable_surfaceMeasure_inter_levelSet hu.continuous hu.lipschitzOnWith hS

/-- Almost-everywhere measurability of weighted Borel-set slices, proved. -/
theorem target_L5 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K S g hu hS hg
  exact aemeasurable_setLIntegral_inter_levelSet hu.continuous hu.lipschitzOnWith hS hg

/-- The first original target: the contract of
`FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet`. -/
theorem target_T1 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ u K hu g hg
  have h := aemeasurable_setLIntegral_inter_levelSet (S := Set.univ) hu.continuous
    hu.lipschitzOnWith MeasurableSet.univ hg
  simpa using h

/-- `target_L4` with `[CompleteSpace V]` dropped and global Lipschitz weakened to continuity
plus Lipschitz on `S` only. -/
theorem target_L4_of_lipschitzOnWith : ∀ {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}, Continuous u → LipschitzOnWith K u S →
    MeasurableSet S →
    AEMeasurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t}))
      (volume : Measure ℝ) := by
  intro V _ _ _ _ _ u K S hc hu hS
  exact aemeasurable_surfaceMeasure_inter_levelSet hc hu hS

/-- `target_L5` with the same weakening. -/
theorem target_L5_of_lipschitzOnWith : ∀ {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞}, Continuous u → LipschitzOnWith K u S →
    MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  intro V _ _ _ _ _ u K S g hc hu hS hg
  exact aemeasurable_setLIntegral_inter_levelSet hc hu hS hg

/-! ### Consumers -/

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Eilenberg majorant and Borel-slice measurability together: for a measurable set the slice
function is almost everywhere measurable **and** its integral obeys the Eilenberg bound. -/
theorem eilenberg_borel {u : V → ℝ} {K : ℝ≥0} {S : Set V} (hc : Continuous u)
    (hu : LipschitzOnWith K u S) (hS : MeasurableSet S) :
    AEMeasurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) (volume : Measure ℝ) ∧
      (∫⁻ t, surfaceMeasure V (S ∩ {x | u x = t}) ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S := by
  refine ⟨aemeasurable_surfaceMeasure_inter_levelSet hc hu hS, ?_⟩
  obtain ⟨F, _, hFdom, hFint⟩ := exists_measurable_majorant hu
  exact (lintegral_mono hFdom).trans hFint

omit [FiniteDimensional ℝ V] in
/-- The weighted statement at weight `1` returns the unweighted one: the slice integral of the
constant weight is the slice measure. -/
theorem weighted_one (S : Set V) (u : V → ℝ) (t : ℝ) :
    (∫⁻ _y in S ∩ {x | u x = t}, (1 : ℝ≥0∞) ∂(surfaceMeasure V))
      = surfaceMeasure V (S ∩ {x | u x = t}) := by
  simp

end Consumers

/-- No finiteness or boundedness of `S`: an unbounded measurable set of infinite volume. -/
theorem infinite_volume :
    AEMeasurable (fun t : ℝ => surfaceMeasure ℝ (Set.Ici (0 : ℝ) ∩ {x : ℝ | id x = t}))
      (volume : Measure ℝ) :=
  aemeasurable_surfaceMeasure_inter_levelSet continuous_id
    (LipschitzWith.id.lipschitzOnWith) measurableSet_Ici

/-- No finiteness of the weight: `g` is identically `∞`. -/
theorem top_weight :
    AEMeasurable (fun t : ℝ =>
        ∫⁻ _y in Set.Ici (0 : ℝ) ∩ {x : ℝ | id x = t}, (∞ : ℝ≥0∞) ∂(surfaceMeasure ℝ))
      (volume : Measure ℝ) :=
  aemeasurable_setLIntegral_inter_levelSet continuous_id
    (LipschitzWith.id.lipschitzOnWith) measurableSet_Ici measurable_const

/-! ### Null-slicing contracts, restated verbatim -/

theorem preserved_measurable_surfaceMeasure_inter_levelSet :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
      [BorelSpace V] {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
      Measurable fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t}) := by
  intro V _ _ _ _ u S hu hS
  exact measurable_surfaceMeasure_inter_levelSet (u := u) (S := S) hu hS

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

theorem preserved_ae_surfaceMeasure_inter_levelSet_eq_zero :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V] {u : V → ℝ} {K : ℝ≥0} {N : Set V},
      LipschitzOnWith K u N → (volume : Measure V) N = 0 →
      ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0 := by
  intro V _ _ _ _ _ u K N hu hN
  exact ae_surfaceMeasure_inter_levelSet_eq_zero (u := u) (K := K) (N := N) hu hN

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.KLS.exists_isCompact_seq_volume_sdiff_eq_zero
#print axioms FunctionalInequalities.KLS.aemeasurable_surfaceMeasure_inter_levelSet
#print axioms FunctionalInequalities.KLS.aemeasurable_setLIntegral_inter_levelSet
#print axioms BorelSliceAudit.target_L4
#print axioms BorelSliceAudit.target_L5
#print axioms BorelSliceAudit.target_T1
#print axioms BorelSliceAudit.target_L4_of_lipschitzOnWith
#print axioms BorelSliceAudit.target_L5_of_lipschitzOnWith
#print axioms BorelSliceAudit.eilenberg_borel
#print axioms BorelSliceAudit.weighted_one
#print axioms BorelSliceAudit.infinite_volume
#print axioms BorelSliceAudit.top_weight
#print axioms BorelSliceAudit.preserved_measurable_surfaceMeasure_inter_levelSet
#print axioms BorelSliceAudit.preserved_exists_measurable_majorant
#print axioms BorelSliceAudit.preserved_ae_surfaceMeasure_inter_levelSet_eq_zero

end BorelSliceAudit
