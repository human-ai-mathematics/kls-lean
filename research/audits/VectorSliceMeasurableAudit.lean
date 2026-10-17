import FunctionalInequalities.Analysis.Vector.Slice.Measurable
import FunctionalInequalities.KLS.Geometry.Slice.OpenMeasurable
import Mathlib.Analysis.InnerProductSpace.PiL2
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Scope audit for codimension-`m` compact slices and weighted slice measurability

**What is proved.**  `measurable_hausdorffMeasure_inter_levelSet_vector`: for `S` compact and `u`
continuous into a metric space, the `d`-dimensional Hausdorff measure of the level slices is Borel
measurable in the level.  With the Eilenberg inequality of the previous round this completes the
chain: `aemeasurable_setLIntegral_inter_levelSet_vector` is weighted slice measurability for a map
Lipschitz on a Borel set, and
`aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector` localizes it to a map that is `C¹`
on an open set only.  **Neither needs the differential to be surjective**, so unlike the chart route
of `Analysis/Vector/Coarea/Regular.lean` these statements cover the **critical** part of the domain.

**`m = 1` gives back the proved scalar statements.**  `scalar_compact_slices` reproduces
`Analysis.measurable_hausdorffMeasure_inter_levelSet` and `scalar_open_slices` reproduces
`KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`, both discharged from the
codimension-`m` versions.  One honest difference is recorded: the codimension-`m` statements carry
the hypothesis `k + finrank W = finrank V`, so the scalar recovery needs `1 ≤ finrank V`, whereas
the scalar statement also covers a zero-dimensional ambient space.

**What is not proved.**  *No coarea formula.*  What this removes is the regularity hypothesis from
the **measurability** half of the codimension-`m` coarea layer, not from the coarea **equality**,
which still holds only where the differential is surjective.  The critical part of the coarea
formula needs a codimension-`m` Sard or critical-slice argument, which is not proved.  Sharp
finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched.
-/

noncomputable section

open Set MeasureTheory Module Filter FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff

namespace VectorSliceMeasurableAudit

section Restatements

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] in
/-- **Compact slices, restated from scratch.**  No Lipschitz hypothesis, no finiteness. -/
theorem compact_slices {d : ℝ} (hd : 0 ≤ d) {S : Set V} {u : V → W} (hS : IsCompact S)
    (hu : Continuous u) :
    Measurable fun t : W => μH[d] (S ∩ {x | u x = t}) :=
  measurable_hausdorffMeasure_inter_levelSet_vector hd hS hu

/-- **Weighted slice measurability, restated from scratch**, with no regularity hypothesis: only a
Lipschitz bound on the Borel set.  The weight may be unbounded or identically `∞`. -/
theorem weighted_slices {u : V → W} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hc : Continuous u) (hu : LipschitzOnWith K u S)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) :=
  aemeasurable_setLIntegral_inter_levelSet_vector hk hc hu hS hg

/-- **The critical part is covered.**  A constant map has nowhere surjective differential once the
target is positive-dimensional, so the chart route says nothing about it; the slice measurability
proved here applies unchanged. -/
theorem constant_map {S : Set V} {g : V → ℝ≥0∞} {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V)
    (c : W) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | (fun _ : V => c) x = t}, g y
        ∂(KLS.hausdorffNormalized V k)) (volume : Measure W) :=
  aemeasurable_setLIntegral_inter_levelSet_vector hk continuous_const
    (LipschitzWith.const c).lipschitzOnWith hS hg

/-- **An identically infinite weight** is inside the statement. -/
theorem infinite_weight {u : V → W} {K : ℝ≥0} {S : Set V} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hc : Continuous u) (hu : LipschitzOnWith K u S)
    (hS : MeasurableSet S) :
    AEMeasurable (fun t : W => ∫⁻ _ in S ∩ {x | u x = t}, (⊤ : ℝ≥0∞)
        ∂(KLS.hausdorffNormalized V k)) (volume : Measure W) :=
  aemeasurable_setLIntegral_inter_levelSet_vector hk hc hu hS measurable_const

/-- **`C¹` on an open set only, restated from scratch**, with no regularity hypothesis and no
regularity outside `O`. -/
theorem open_domain_slices {O S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) :=
  aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector hk hO hu hS hSO hg

/-- **A zero-dimensional target** is inside the statement: the fibre dimension is the whole
dimension. -/
theorem zero_dimensional_target [Subsingleton W] {O S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y
        ∂(KLS.hausdorffNormalized V (finrank ℝ V))) (volume : Measure W) := by
  refine aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector ?_ hO hu hS hSO hg
  rw [show finrank ℝ W = 0 from Module.finrank_zero_of_subsingleton, Nat.add_zero]

end Restatements

/-! ### `m = 1` is the proved scalar theory -/

section CodimensionOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **`m = 1` is the proved scalar compact-slice measurability**,
`Analysis.measurable_hausdorffMeasure_inter_levelSet`, reproduced verbatim. -/
theorem scalar_compact_slices {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} (hd : 0 ≤ d) {S : Set X} {u : X → ℝ} (hS : IsCompact S) (hu : Continuous u) :
    Measurable fun t : ℝ => μH[d] (S ∩ {x | u x = t}) :=
  measurable_hausdorffMeasure_inter_levelSet_vector hd hS hu

/-- **`m = 1` is the proved scalar weighted slice measurability**,
`KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`, reproduced verbatim from the
codimension-`m` version.  The extra hypothesis `1 ≤ finrank V` is the honest difference: the
codimension-`m` statements assume the fibre dimension and the codimension add up to the ambient
dimension, so a zero-dimensional ambient space — which the scalar statement also covers — is outside
their reach. -/
theorem scalar_open_slices {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞} (hn : 1 ≤ finrank ℝ V)
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  have hk : (finrank ℝ V - 1) + finrank ℝ ℝ = finrank ℝ V := by
    rw [finrank_self]; omega
  have h := aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector (V := V) (W := ℝ)
    (k := finrank ℝ V - 1) hk hO hu hS hSO hg
  exact h

end CodimensionOne

end VectorSliceMeasurableAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.isOpen_setOf_slice_subset_vector
#print axioms FunctionalInequalities.Analysis.upperSemicontinuous_openCoverCost_slice_vector
#print axioms FunctionalInequalities.Analysis.measurable_hausdorffMeasure_inter_levelSet_vector
#print axioms FunctionalInequalities.Analysis.measurable_hausdorffNormalized_inter_levelSet_vector
#print axioms FunctionalInequalities.Analysis.hausdorffNormalized_finrank_eq_zero_of_volume_eq_zero
#print axioms FunctionalInequalities.Analysis.aemeasurable_hausdorffNormalized_inter_levelSet_vector
#print axioms FunctionalInequalities.Analysis.aemeasurable_setLIntegral_inter_levelSet_vector
#print axioms FunctionalInequalities.Analysis.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector
#print axioms VectorSliceMeasurableAudit.compact_slices
#print axioms VectorSliceMeasurableAudit.weighted_slices
#print axioms VectorSliceMeasurableAudit.constant_map
#print axioms VectorSliceMeasurableAudit.infinite_weight
#print axioms VectorSliceMeasurableAudit.open_domain_slices
#print axioms VectorSliceMeasurableAudit.zero_dimensional_target
#print axioms VectorSliceMeasurableAudit.scalar_compact_slices
#print axioms VectorSliceMeasurableAudit.scalar_open_slices

/-! The repository's scalar statements, for comparison; they are proved independently. -/
#print axioms FunctionalInequalities.Analysis.measurable_hausdorffMeasure_inter_levelSet
#print axioms FunctionalInequalities.KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn
