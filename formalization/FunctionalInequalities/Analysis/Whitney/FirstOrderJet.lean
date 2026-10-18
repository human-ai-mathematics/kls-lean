import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-! # The first-order jet condition of the Whitney extension problem

Property compact Whitney extension of the weighted coarea route asks for the converse of what is proved here: that a
compatible first-order jet `(f, F)` on a compact set extends to a globally `C¹` function with
exactly those values and derivatives.  **compact Whitney extension itself is not proved in this module**, and the pinned
Mathlib contains no Whitney extension theorem — only the unrelated `WhitneyEmbedding` for manifolds
and `Continuous.exists_contDiff_approx_and_eqOn`, which requires the function to be `C^n` on a
whole *neighbourhood* of the closed set and therefore cannot start from jet data on the set alone.

What is proved here is that compact Whitney extension's hypothesis is **necessary**, so the jet condition it assumes is
exactly the right one: if some globally `C¹` function realizes the jet on a compact `S`, then the
uniform first-order remainder estimate

`∀ ε > 0, ∃ δ > 0, ∀ x y ∈ S, ‖y - x‖ < δ → ‖f y - f x - F x (y - x)‖ ≤ ε ‖y - x‖`

holds.  Together with compact Whitney extension this makes the estimate a characterization, and it is the exact
interface between compact Whitney jets — which must *produce* this estimate on compact pieces of a Lipschitz
function — and compact Whitney extension, which *consumes* it.

The proof is the mean value inequality along segments.  Compactness enters twice: it makes the
closed unit thickening of `S` compact in a finite-dimensional space, so the continuous derivative
is *uniformly* continuous there, and it lets the segment between two nearby points of `S` stay
inside that thickening.  Neither `f` nor `F` is assumed continuous: their behaviour on `S` is
forced by the realizing function.
-/

noncomputable section

open Metric Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

section Jet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The first-order jet condition of compact Whitney extension is necessary.**  If a globally `C¹` function realizes
the values `f` and the derivatives `F` on a compact set `S`, then the uniform first-order remainder
estimate of compact Whitney extension holds on `S`.

compact Whitney extension is the converse — that the estimate suffices to build such a function — and is **not** proved
here. -/
theorem uniform_jet_remainder_of_contDiff {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ}
    (hS : IsCompact S) {v : V → ℝ} (hv : ContDiff ℝ 1 v)
    (hvf : Set.EqOn v f S) (hvF : ∀ x ∈ S, fderiv ℝ v x = F x) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  -- The closed unit thickening of a compact set is compact in a finite-dimensional space.
  have hKcompact : IsCompact (Metric.cthickening 1 S) :=
    Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
      (hS.isBounded.cthickening)
  -- Hence the derivative is uniformly continuous there.
  obtain ⟨δ₀, hδ₀, hunif⟩ :=
    Metric.uniformContinuousOn_iff.1
      (hKcompact.uniformContinuousOn_of_continuous hcont.continuousOn) ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun x hx y hy hxy => ?_⟩
  -- The segment from `x` to `y` stays in the thickening and close to `x`.
  have hseg : ∀ z ∈ segment ℝ x y, z ∈ Metric.cthickening 1 S ∧ dist z x < δ₀ := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hzx : a • x + b • y - x = b • (y - x) := by
      have ha' : a = 1 - b := by linarith
      rw [ha']
      module
    have hdist : dist (a • x + b • y) x = b * ‖y - x‖ := by
      rw [dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have hble : b * ‖y - x‖ ≤ ‖y - x‖ := by
      nlinarith [norm_nonneg (y - x), hb, hab, ha]
    refine ⟨?_, ?_⟩
    · refine Metric.mem_cthickening_of_dist_le _ x 1 S hx ?_
      exact le_trans (hdist ▸ hble) (le_of_lt (lt_of_lt_of_le hxy (min_le_right _ _)))
    · exact hdist ▸ lt_of_le_of_lt hble (lt_of_lt_of_le hxy (min_le_left _ _))
  -- Mean value inequality for `v` minus its linearization at `x`.
  have hxK : x ∈ Metric.cthickening 1 S := Metric.self_subset_cthickening _ hx
  have hbound : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt (fun w => v w - fderiv ℝ v x w) (fderiv ℝ v z - fderiv ℝ v x)
        (segment ℝ x y) z := by
    intro z _
    exact ((hv.differentiable one_ne_zero z).hasFDerivAt.sub
      (fderiv ℝ v x).hasFDerivAt).hasFDerivWithinAt
  have hnorm : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ v z - fderiv ℝ v x‖ ≤ ε := by
    intro z hz
    have := hunif z (hseg z hz).1 x hxK (hseg z hz).2
    rw [dist_eq_norm] at this
    exact this.le
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hbound hnorm (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  -- Rewrite the realizing function into the jet data.
  have hgoal : ‖v y - fderiv ℝ v x y - (v x - fderiv ℝ v x x)‖ ≤ ε * ‖y - x‖ := hmv
  have hrw : v y - fderiv ℝ v x y - (v x - fderiv ℝ v x x)
      = f y - f x - F x (y - x) := by
    rw [hvf hx, hvf hy, hvF x hx, map_sub]
    ring
  rw [hrw] at hgoal
  exact hgoal

end Jet

end FunctionalInequalities.Analysis
