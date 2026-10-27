import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Pi

/-!
# Coordinate detection on finite real products

A nonzero continuous linear functional on a finite product of real lines is
nonzero on a standard coordinate vector, for the ordinary product topology and
norm. This shared coordinate fact supports the smooth, finite-regularity and
planar Sard charts used in regular-value and coarea constructions. It has no
Euclidean-norm, differentiability or measure premise; empty finite indices are
allowed (the nonzero-functional premise then cannot hold).
-/
noncomputable section
namespace FunctionalInequalities.Analysis.PiCoordinates

/-- A nonzero functional on a finite real product detects a standard coordinate. -/
theorem exists_apply_single_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : (ι → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) : ∃ i : ι, α (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra h
  push Not at h
  refine hα (ContinuousLinearMap.ext fun v => ?_)
  have hv : v = ∑ i : ι, v i • Pi.single i (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  simp [map_sum, h]


end FunctionalInequalities.Analysis.PiCoordinates
