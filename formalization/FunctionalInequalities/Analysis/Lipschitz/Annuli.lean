import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Group.Basic

/-! # The half-open annuli of a normed space

`X3` of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`: the bookkeeping that
turns a *local* hypothesis into a countable sum.  The sets `k ≤ ‖x‖ < k + 1` are measurable,
pairwise disjoint, cover the space, and each of them sits inside the **open** ball of radius
`k + 1`, which is therefore a neighbourhood of each of its points — the last clause is what lets a
statement true near every point of the piece be used on the whole piece.

This is the codimension-`m` copy of the decomposition used by
`KLS/Geometry/LocallyLipschitzCoarea.lean`, isolated here because the vector assembly needs the
same four facts.  Nothing about the dimension, the inner product or the measure is used: only the
norm, and for measurability the Borel structure.
-/

noncomputable section

open Metric Set Topology

namespace FunctionalInequalities.Analysis

/-- The half-open annulus `{x | k ≤ ‖x‖ < k + 1}`, written as a difference of balls. -/
def annulus (V : Type*) [NormedAddCommGroup V] (k : ℕ) : Set V :=
  ball (0 : V) (k + 1) \ ball (0 : V) k

/-- The annulus is contained in the open ball that bounds it. -/
theorem annulus_subset_ball {V : Type*} [NormedAddCommGroup V] (k : ℕ) :
    annulus V k ⊆ ball (0 : V) ((k : ℝ) + 1) :=
  sdiff_subset

/-- Each annulus is measurable: it is a difference of two open balls. -/
theorem measurableSet_annulus {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    [OpensMeasurableSpace V] (k : ℕ) : MeasurableSet (annulus V k) :=
  measurableSet_ball.diff measurableSet_ball

/-- Distinct annuli are disjoint. -/
theorem pairwise_disjoint_annulus (V : Type*) [NormedAddCommGroup V] :
    Pairwise fun i j : ℕ => Disjoint (annulus V i) (annulus V j) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (annulus V i) (annulus V j) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro x ⟨hx1, -⟩ ⟨-, hx2⟩
    exact hx2 (ball_subset_ball (by exact_mod_cast Nat.succ_le_of_lt hij) hx1)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- The annuli cover the space: `⌊‖x‖⌋₊` is the index of the one containing `x`. -/
theorem iUnion_annulus (V : Type*) [NormedAddCommGroup V] : (⋃ k : ℕ, annulus V k) = univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌊‖x‖⌋₊, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using Nat.lt_floor_add_one ‖x‖
  · simpa only [mem_ball, dist_zero_right, not_lt] using Nat.floor_le (norm_nonneg x)

/-- The open ball of radius `k + 1` is a neighbourhood of every point of the `k`-th annulus. -/
theorem ball_mem_nhds_of_mem_annulus {V : Type*} [NormedAddCommGroup V] {k : ℕ} {x : V}
    (hx : x ∈ annulus V k) : ball (0 : V) ((k : ℝ) + 1) ∈ 𝓝 x :=
  isOpen_ball.mem_nhds (annulus_subset_ball k hx)

end FunctionalInequalities.Analysis
