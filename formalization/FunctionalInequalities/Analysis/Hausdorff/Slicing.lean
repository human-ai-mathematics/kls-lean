module

public import FunctionalInequalities.Analysis.Vector.Slice.Hausdorff
public import FunctionalInequalities.Analysis.Hausdorff.Content
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Eilenberg slicing bound for Hausdorff measures along a Lipschitz real function

Metric-space layer of the coarea formula, depending on Mathlib only.  The main result
`exists_measurable_majorant` is the Eilenberg inequality in the form needed for coarea: for `u`
Lipschitz *on `S` only*, the slice function `t ↦ μH[d] (S ∩ {u = t})` admits a **measurable**
majorant `F` with `∫⁻ F ≤ 2 K μH[d + 1] S`.  Both the majorant's measurability and the constant
are part of the conclusion: the slice function itself is not known to be measurable, so a bound
stated for it alone could not be integrated, and deducing `f = 0` a.e. from `∫⁻ f = 0` needs `f`
measurable.  `ae_hausdorffMeasure_inter_levelSet_eq_zero` — the null special case — is a corollary.

The proof is a covering argument, not an application of Rademacher's theorem: differentiability
almost everywhere says nothing about individual level sets.  For each scale `k` the infimum formula
`Measure.hausdorffMeasure_apply` supplies a countable cover `T k` of `S` with diameters at most
`(k + 1)⁻¹` and total `(d + 1)`-dimensional cover cost at most `μH[d + 1] S + (k + 1)⁻¹`
(`exists_cover_familyCost_lt`).  Each cover piece meeting `S` has its `u`-image inside an explicit
closed
interval of length `2 K (diameter of the piece)`, because `u` is Lipschitz on `S`; only points of
`S` are ever compared (`exists_levelSlab`).  Summing the pieces whose interval contains `t` gives
the majorant at scale `k`, measurable by construction, with Lebesgue integral at most
`2 K (μH[d + 1] S + (k + 1)⁻¹)`, while `Measure.hausdorffMeasure_le_liminf_tsum` bounds
`μH[d] (S ∩ {u = t})` by the `liminf` of the majorants pointwise.  Fatou's lemma on the majorants
then gives the stated integral bound in the limit.

Degenerate data are covered by explicit branches rather than excluded.  `K = 0` makes `u` constant
on `S`, and the one-point majorant of `exists_measurable_majorant_of_eqOn` has integral zero, which
is what the bound then demands; this also settles `μH[d + 1] S = ∞` with `K = 0`, where the
covering argument has no finite-cost cover to start from.  `μH[d + 1] S = ∞` with `K ≠ 0` makes the
bound `∞`.  `d = 0` (the fibre count of a one-dimensional ambient space) keeps
`ediam ^ (0 : ℝ) = 1` for a single-point piece, which is exactly why the majorant sums the pieces
whose interval contains `t` instead of all pieces: an empty piece would otherwise contribute
`0 ^ (0 : ℝ) = 1`.  Zero-diameter pieces and empty pieces are therefore harmless, `S` is not
assumed measurable, bounded, or nonempty, and `u` is not assumed globally Lipschitz,
differentiable, or measurable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

section HausdorffSlicing

/-- A function constant on `S` has an explicit majorant of integral zero, for **any** measure on
the ambient space: the whole slice family is concentrated on the single level attained on `S`, and
a single real level is Lebesgue-null.  No measurability or finiteness of `S` or of `μ` is used, and
the majorant is `∞` on that level, so nothing is assumed about the size of `S`. -/
theorem exists_measurable_majorant_of_eqOn {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    {u : Y → ℝ} {S : Set Y} (h : ∀ x ∈ S, ∀ y ∈ S, u x = u y) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧ (∀ t, μ (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) = 0 := by
  exact exists_measurable_majorant_of_eqOn_vector h
variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A `μH[d]`-null set admits countable covers of arbitrarily small diameter whose total
`d`-dimensional cover cost is arbitrarily small.  The null case of `exists_cover_familyCost_lt`. -/
theorem exists_cover_of_hausdorffMeasure_eq_zero {d : ℝ} {N : Set X} (hN : μH[d] N = 0)
    {r c : ℝ≥0∞} (hr : 0 < r) (hc : 0 < c) :
    ∃ T : ℕ → Set X, N ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c :=
  exists_cover_familyCost_lt hr (hN.trans_lt hc)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Level slabs of a cover.  For a function Lipschitz on `N` and a cover family `T` of finite
diameters, there are measurable subsets of the level axis that contain the `u`-image of every
cover piece intersected with `S`, of Lebesgue measure at most `2 K` times the piece diameter.

Only points of `N` enter the Lipschitz estimate, and `K = 0` or a zero-diameter piece just gives a
one-point slab.  Pieces disjoint from `S` get the empty slab, which is what keeps the majorant of
`exists_measurable_majorant` finite in the `d = 0` case. -/
theorem exists_levelSlab {u : X → ℝ} {K : ℝ≥0} {N : Set X} (hu : LipschitzOnWith K u N)
    (T : ℕ → Set X) (hT : ∀ i, Metric.ediam (T i) ≠ ∞) :
    ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i)) ∧
      (∀ i, volume (J i) ≤ 2 * (K : ℝ≥0∞) * Metric.ediam (T i)) ∧
      (∀ i, ∀ x ∈ T i ∩ N, u x ∈ J i) := by
  obtain ⟨J, hJm, hJvol, hJmem, _⟩ := exists_levelBall hu T hT
  have hball : (volume : Measure ℝ) (Metric.closedBall (0 : ℝ) 1) = 2 := by
    norm_num [Real.volume_closedBall]
  exact ⟨J, hJm, fun i => by
    simpa only [Module.finrank_self, pow_one, hball, mul_assoc] using hJvol i, hJmem⟩
/-- **Eilenberg slicing bound, measurable-majorant form.**  For `u` Lipschitz on `S`, the slice
function `t ↦ μH[d] (S ∩ {u = t})` is dominated by a measurable `F` with
`∫⁻ F ≤ 2 K μH[d + 1] S`.

The measurability of `F` is part of the conclusion and is not assumed of the slice function, which
is not known to be measurable at this point of the development.  No measurability, boundedness or
nonemptiness of `S` is assumed, `u` is Lipschitz on `S` only, and `K = 0`, `d = 0`,
`μH[d + 1] S = ∞` and zero-diameter cover pieces are all handled by the argument itself. -/
theorem exists_measurable_majorant {u : X → ℝ} {K : ℝ≥0} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ 2 * (K : ℝ≥0∞) * μH[d + 1] S := by
  have hball : (volume : Measure ℝ) (Metric.closedBall (0 : ℝ) 1) = 2 := by
    norm_num [Real.volume_closedBall]
  simpa only [Module.finrank_self, Nat.cast_one, pow_one, hball] using
    exists_measurable_majorant_vector hd hu
/-- **Null slicing.**  If `N` carries no `(d + 1)`-dimensional Hausdorff measure and `u` is
Lipschitz on `N`, then `μH[d] (N ∩ {u = t}) = 0` for almost every level `t`.

The null case of `exists_measurable_majorant`: its majorant has vanishing integral, and the
majorant — unlike the slice function — is measurable, so `lintegral_eq_zero_iff` applies.

No measurability, boundedness or nonemptiness of `N` is assumed, `u` is Lipschitz on `N` only, and
`K = 0`, `d = 0` and zero-diameter cover pieces are all handled by the argument itself. -/
theorem ae_hausdorffMeasure_inter_levelSet_eq_zero
    {u : X → ℝ} {K : ℝ≥0} {N : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u N) (hN : μH[d + 1] N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), μH[d] (N ∩ {x | u x = t}) = 0 := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant hd hu
  rw [hN, mul_zero] at hFint
  filter_upwards [(lintegral_eq_zero_iff hFmeas).1 (le_antisymm hFint (by simp))] with t ht
  exact le_antisymm (by simpa [ht] using hFdom t) (by simp)

end HausdorffSlicing

end FunctionalInequalities.Analysis
