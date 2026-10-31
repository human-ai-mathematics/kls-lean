module

public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Affine

/-!
# Hölder caps of functions vanishing off a ball

`holderWith_of_holderOnWith_closedBall_zero_off_ball`: a map in a real normed space that satisfies
`HolderOnWith C α f (closedBall c R)` and vanishes off the open ball `ball c R` satisfies the same
global cap `HolderWith C α f`. A mixed pair (one point inside, one outside) is handled by the
intermediate value theorem on the segment, which yields a sphere point no farther away than the
outside point.

Generic support for the local-source cutoffs in Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 4.4, pp. 57–59 (extension by
zero
of a compactly supported Hölder source). The constant is not enlarged; no statement about general
supports or other extension operators is made.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal
namespace FunctionalInequalities.Analysis

private theorem exists_sphere_point_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c x y : E} {R : ℝ} (hx : x ∈ ball c R) (hy : y ∉ ball c R) :
    ∃ z ∈ sphere c R, dist x z ≤ dist x y := by
  let p : ℝ → E := AffineMap.lineMap x y
  have hp : Continuous (fun t => dist (p t) c) :=
    (AffineMap.lineMap_continuous (p := x) (q := y) :
          Continuous (AffineMap.lineMap x y : ℝ → E)).dist
      continuous_const
  have hI : R ∈ Icc (dist (p 0) c) (dist (p 1) c) := by
    simp only [p, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    exact ⟨hx.le, le_of_not_gt hy⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hp.continuousOn hI
  refine ⟨p t, he, ?_⟩
  change dist x (AffineMap.lineMap x y t) ≤ dist x y
  rw [dist_comm, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 dist_nonneg

/-- A Hölder function on the closed ball that vanishes off the open ball
has the same global Hölder cap. Useful for GT2001 local-source cutoffs. -/
theorem holderWith_of_holderOnWith_closedBall_zero_off_ball {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] {f : E → F} {c : E} {R : ℝ} {C α : ℝ≥0}
    (h : HolderOnWith C α f (closedBall c R)) (hzero : ∀ y ∉ ball c R, f y = 0) :
    HolderWith C α f := by
  have hcross :
    ∀ x ∈ ball c R, ∀ y ∉ ball c R, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    intro x hx y hy
    obtain ⟨z, hz, hxy⟩ := exists_sphere_point_dist_le hx hy
    have hz0 : f z = 0 :=
      hzero z
        (by
          change ¬dist z c < R
          rw [show dist z c = R from hz]
          exact lt_irrefl R)
    have hzcl : z ∈ closedBall c R := by exact (show dist z c = R from hz).le
    simpa only [hz0, hzero y hy] using h.dist_le_of_le (ball_subset_closedBall hx) hzcl hxy
  have hreal (x y : E) : dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    by_cases hx : x ∈ ball c R
    · by_cases hy : y ∈ ball c R
      · exact h.dist_le (ball_subset_closedBall hx) (ball_subset_closedBall hy)
      · exact hcross x hx y hy
    · by_cases hy : y ∈ ball c R
      · simpa only [dist_comm] using hcross y hy x hx
      · rw [hzero x hx, hzero y hy, dist_self]
        positivity
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg, ←
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (hreal x y)
end FunctionalInequalities.Analysis
