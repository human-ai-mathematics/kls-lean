import FunctionalInequalities.Analysis.Vector.Slice.Hausdorff
import FunctionalInequalities.Analysis.Hausdorff.Slicing
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the codimension-`m` Eilenberg slicing inequality

**What is proved.**  `exists_measurable_majorant_vector` is the Eilenberg slicing inequality for a
Lipschitz map into an `m`-dimensional target, in measurable-majorant form: the slice function
`t ↦ μH[d] (S ∩ {u = t})` is dominated by a measurable `F` with
`∫⁻ F ≤ volume (closedBall 0 1) · K ^ m · μH[d + m] S`.  Its null case,
`ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`, and the normalized form the coarea layer
consumes are proved with it.

**`m = 1` is the repository's proved scalar bound, constant included.**  For the real line
`volume (closedBall 0 1) = 2` and `K ^ 1 = K`, so the constant is exactly the `2 K` of
`Analysis.exists_measurable_majorant`; `codimension_one_majorant` reproduces that statement and
discharges it from the codimension-`m` theorem.

**What is not proved.**  The chain from here to unconditional weighted slice measurability is **not
completed** here: it also needs compact-slice measurability in codimension `m`, the analogue of
`Analysis.measurable_hausdorffMeasure_inter_levelSet`, which is stated for a real-valued function
and is not generalized here.  The critical set is not treated, and the **general** codimension-`m`
coarea formula is not proved here.
-/

noncomputable section

open Set MeasureTheory Module Filter FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal

namespace VectorHausdorffSlicingAudit

section Restatements

variable {X W : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **The Eilenberg inequality, restated independently** and discharged through named arguments.
`S` is not assumed measurable, bounded or nonempty, and `u` is Lipschitz on `S` only. -/
theorem eilenberg {u : X → W} {K : ℝ≥0} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u S) :
    ∃ F : W → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure W))
        ≤ (volume : Measure W) (Metric.closedBall (0 : W) 1) * (K : ℝ≥0∞) ^ (finrank ℝ W)
            * μH[d + (finrank ℝ W : ℝ)] S :=
  exists_measurable_majorant_vector hd hu

/-- **`K = 0` is inside the statement**: a map constant on `S` gives the bound `0` when the target
is positive-dimensional. -/
theorem zero_lipschitz_constant {u : X → W} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith 0 u S) (hpos : 0 < finrank ℝ W) :
    ∃ F : W → ℝ≥0∞, Measurable F ∧ (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure W)) = 0 := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant_vector hd hu
  refine ⟨F, hFmeas, hFdom, le_antisymm ?_ (by simp)⟩
  refine hFint.trans ?_
  rw [show ((0 : ℝ≥0) : ℝ≥0∞) ^ (finrank ℝ W) = (0 : ℝ≥0∞) from by
    rw [ENNReal.coe_zero]
    exact zero_pow (show finrank ℝ W ≠ 0 by omega)]
  simp

/-- **`d = 0` is inside the statement**: the fibre dimension may be zero. -/
theorem zero_fibre_dimension {u : X → W} {K : ℝ≥0} {S : Set X} (hu : LipschitzOnWith K u S) :
    ∃ F : W → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[(0 : ℝ)] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure W))
        ≤ (volume : Measure W) (Metric.closedBall (0 : W) 1) * (K : ℝ≥0∞) ^ (finrank ℝ W)
            * μH[(0 : ℝ) + (finrank ℝ W : ℝ)] S :=
  exists_measurable_majorant_vector le_rfl hu

/-- **A zero-dimensional target is inside the statement**, and there the inequality degenerates to
`∫⁻ F ≤ volume univ · μH[d] S`, with `K` playing no role. -/
theorem zero_dimensional_target {u : X → EuclideanSpace ℝ (Fin 0)} {K : ℝ≥0} {S : Set X} {d : ℝ}
    (hd : 0 ≤ d) (hu : LipschitzOnWith K u S) :
    ∃ F : EuclideanSpace ℝ (Fin 0) → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure (EuclideanSpace ℝ (Fin 0))))
        ≤ (volume : Measure (EuclideanSpace ℝ (Fin 0)))
              (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1) * μH[d] S := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant_vector hd hu
  refine ⟨F, hFmeas, hFdom, hFint.trans (le_of_eq ?_)⟩
  rw [show finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 from finrank_euclideanSpace_fin]
  simp

/-- **Null slicing**, restated independently. -/
theorem null_slicing {u : X → W} {K : ℝ≥0} {N : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u N) (hN : μH[d + (finrank ℝ W : ℝ)] N = 0) :
    ∀ᵐ t ∂(volume : Measure W), μH[d] (N ∩ {x | u x = t}) = 0 :=
  ae_hausdorffMeasure_inter_levelSet_eq_zero_vector hd hu hN

end Restatements

/-! ### `m = 1` is the proved scalar bound, constant included -/

section CodimensionOne

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- On the real line the unit ball has measure `2`, so the codimension-`m` constant
`volume (closedBall 0 1) · K ^ m` is the scalar `2 K`. -/
theorem volume_unit_closedBall_real :
    (volume : Measure ℝ) (Metric.closedBall (0 : ℝ) 1) = 2 := by
  rw [Real.volume_closedBall]
  norm_num

/-- **`m = 1` is the proved scalar Eilenberg bound**, `Analysis.exists_measurable_majorant`,
reproduced verbatim — constant `2 K` included — and discharged from the codimension-`m`
theorem. -/
theorem codimension_one_majorant {u : X → ℝ} {K : ℝ≥0} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ 2 * (K : ℝ≥0∞) * μH[d + 1] S := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant_vector hd hu
  refine ⟨F, hFmeas, hFdom, hFint.trans (le_of_eq ?_)⟩
  rw [volume_unit_closedBall_real, finrank_self, pow_one]
  norm_num

end CodimensionOne

end VectorHausdorffSlicingAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.exists_measurable_majorant_of_eqOn_vector
#print axioms FunctionalInequalities.Analysis.exists_cover_familyCost_lt
#print axioms FunctionalInequalities.Analysis.exists_levelBall
#print axioms FunctionalInequalities.Analysis.exists_measurable_majorant_vector
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero_vector
#print axioms FunctionalInequalities.Analysis.hausdorffNormalized_eq_zero_iff
#print axioms FunctionalInequalities.Analysis.ae_hausdorffNormalized_inter_levelSet_eq_zero_vector
#print axioms VectorHausdorffSlicingAudit.eilenberg
#print axioms VectorHausdorffSlicingAudit.zero_lipschitz_constant
#print axioms VectorHausdorffSlicingAudit.zero_fibre_dimension
#print axioms VectorHausdorffSlicingAudit.zero_dimensional_target
#print axioms VectorHausdorffSlicingAudit.null_slicing
#print axioms VectorHausdorffSlicingAudit.volume_unit_closedBall_real
#print axioms VectorHausdorffSlicingAudit.codimension_one_majorant

/-! The repository's scalar Eilenberg bound, for comparison; it is proved independently. -/
#print axioms FunctionalInequalities.Analysis.exists_measurable_majorant
