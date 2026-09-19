import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Eilenberg slicing bound for Hausdorff measures along a Lipschitz real function

Metric-space layer of the coarea route, depending on Mathlib only.  The main result
`exists_measurable_majorant` is the Eilenberg inequality in the form the route needs: for `u`
Lipschitz *on `S` only*, the slice function `t ↦ μH[d] (S ∩ {u = t})` admits a **measurable**
majorant `F` with `∫⁻ F ≤ 2 K μH[d + 1] S`.  Both the majorant's measurability and the constant
are part of the conclusion: the slice function itself is not known to be measurable, so a bound
stated for it alone could not be integrated, and deducing `f = 0` a.e. from `∫⁻ f = 0` needs `f`
measurable.  `ae_hausdorffMeasure_inter_levelSet_eq_zero` — the null special case — is a corollary.

The proof is a covering argument, not an application of Rademacher's theorem: differentiability
almost everywhere says nothing about individual level sets.  For each scale `k` the infimum formula
`Measure.hausdorffMeasure_apply` supplies a countable cover `T k` of `S` with diameters at most
`(k + 1)⁻¹` and total `(d + 1)`-dimensional cover cost at most `μH[d + 1] S + (k + 1)⁻¹`
(`exists_cover_cost_lt`).  Each cover piece meeting `S` has its `u`-image inside an explicit closed
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
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · exact ⟨0, measurable_const, fun t => by simp [hS], by simp⟩
  refine ⟨({u x₀} : Set ℝ).indicator fun _ => ∞,
    measurable_const.indicator (measurableSet_singleton _), fun t => ?_, ?_⟩
  · by_cases ht : t = u x₀
    · simp [ht]
    · have : S ∩ {x | u x = t} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => ht ?_
        rw [← hx.2, h x hx.1 x₀ hx₀]
      simp [this, ht]
  · rw [lintegral_indicator_const (measurableSet_singleton _), Real.volume_singleton, mul_zero]

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Near-optimal countable covers of arbitrarily small diameter: every scale admits a cover whose
total `d`-dimensional cover cost is below any bound strictly above `μH[d] S`.  Read off the
infimum formula for `μH[d]`, whose scalewise infima are all at most `μH[d] S`; the `Nonempty` guard
is Mathlib's, and it keeps the cost of an empty piece at `0` even for `d = 0`. -/
theorem exists_cover_cost_lt {d : ℝ} {S : Set X} {r c : ℝ≥0∞} (hr : 0 < r)
    (hc : μH[d] S < c) :
    ∃ T : ℕ → Set X, S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c := by
  have hle : (⨅ (T : ℕ → Set X) (_ : S ⊆ ⋃ i, T i) (_ : ∀ i, Metric.ediam (T i) ≤ r),
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d) ≤ μH[d] S := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂ (f := fun r (_ : 0 < r) =>
      ⨅ (T : ℕ → Set X) (_ : S ⊆ ⋃ i, T i) (_ : ∀ i, Metric.ediam (T i) ≤ r),
        ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d) r hr
  obtain ⟨T, hT⟩ := iInf_lt_iff.1 (hle.trans_lt hc)
  obtain ⟨hcov, hT⟩ := iInf_lt_iff.1 hT
  obtain ⟨hdiam, hcost⟩ := iInf_lt_iff.1 hT
  exact ⟨T, hcov, hdiam, hcost⟩

/-- A `μH[d]`-null set admits countable covers of arbitrarily small diameter whose total
`d`-dimensional cover cost is arbitrarily small.  The null case of `exists_cover_cost_lt`. -/
theorem exists_cover_of_hausdorffMeasure_eq_zero {d : ℝ} {N : Set X} (hN : μH[d] N = 0)
    {r c : ℝ≥0∞} (hr : 0 < r) (hc : 0 < c) :
    ∃ T : ℕ → Set X, N ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c :=
  exists_cover_cost_lt hr (hN.trans_lt hc)

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
  classical
  have hcast : ∀ i, (K : ℝ≥0∞) * Metric.ediam (T i)
      = ENNReal.ofReal ((K : ℝ) * (Metric.ediam (T i)).toReal) := fun i => by
    rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal (hT i)]
  refine ⟨fun i => if h : (T i ∩ N).Nonempty then
      Metric.closedBall (u h.some) ((K : ℝ) * (Metric.ediam (T i)).toReal) else ∅, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split
    · exact measurableSet_closedBall
    · exact MeasurableSet.empty
  · intro i
    dsimp only
    by_cases h : (T i ∩ N).Nonempty
    · have hval : volume (Metric.closedBall (u h.some)
          ((K : ℝ) * (Metric.ediam (T i)).toReal))
          = 2 * (K : ℝ≥0∞) * Metric.ediam (T i) := by
        rw [Real.volume_closedBall, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← hcast i, ← mul_assoc]
        norm_num
      rw [dif_pos h, hval]
    · rw [dif_neg h]
      simp
  · intro i x hx
    have h : (T i ∩ N).Nonempty := ⟨x, hx⟩
    have hp := h.some_mem
    have hedist : edist (u x) (u h.some) ≤ (K : ℝ≥0∞) * Metric.ediam (T i) :=
      (hu hx.2 hp.2).trans (by gcongr; exact Metric.edist_le_ediam_of_mem hx.1 hp.1)
    have hfin : (K : ℝ≥0∞) * Metric.ediam (T i) ≠ ∞ := by
      simp [ENNReal.mul_eq_top, hT i]
    dsimp only
    rw [dif_pos h, Metric.mem_closedBall, dist_edist]
    calc (edist (u x) (u h.some)).toReal
        ≤ ((K : ℝ≥0∞) * Metric.ediam (T i)).toReal := ENNReal.toReal_mono hfin hedist
      _ = (K : ℝ) * (Metric.ediam (T i)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.coe_toReal]

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
  classical
  -- `K = 0`: `u` is constant on `S`, and the one-point majorant has integral zero.
  rcases eq_or_ne K 0 with hK | hK
  · obtain ⟨F, hFmeas, hFdom, hFint⟩ :=
      exists_measurable_majorant_of_eqOn (μ := (μH[d] : Measure X)) (u := u) (S := S)
        fun x hx y hy => by
          have := hu hx hy
          simp [hK] at this
          exact this
    exact ⟨F, hFmeas, hFdom, by rw [hFint]; simp⟩
  -- Infinite cover cost with `K ≠ 0`: the bound is `∞`.
  rcases eq_or_ne (μH[d + 1] S) ∞ with htop | htop
  · refine ⟨fun _ => ∞, measurable_const, fun _ => le_top, ?_⟩
    rw [htop, ENNReal.mul_top (by simp [hK])]
    exact le_top
  -- Scales and cover costs.
  have hεpos : ∀ k : ℕ, (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ := fun k =>
    ENNReal.inv_pos.2 (by simp)
  have hεtop : ∀ k : ℕ, ((k : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := fun k =>
    ENNReal.inv_ne_top.2 (by positivity)
  have hεtendsto : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have h : (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) = fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      funext k; norm_cast
    rw [h]
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  -- Covers of `S` at every scale, of nearly optimal cost, and their level slabs.
  choose T hcov hdiam hcost using fun k : ℕ =>
    exists_cover_cost_lt (S := S) (d := d + 1) (hεpos k)
      (ENNReal.lt_add_right htop (hεpos k).ne')
  have hδtop : ∀ k i, Metric.ediam (T k i) ≠ ∞ := fun k i =>
    ne_top_of_le_ne_top (hεtop k) (hdiam k i)
  choose J hJmeas hJvol hJmem using fun k : ℕ => exists_levelSlab hu (T k) (hδtop k)
  -- The measurable majorants at each scale.
  set F : ℕ → ℝ → ℝ≥0∞ := fun k t =>
    ∑' i, (J k i).indicator (fun _ => Metric.ediam (T k i) ^ d) t with hF
  have hFmeas : ∀ k, Measurable (F k) := by
    intro k
    simp only [hF, ENNReal.tsum_eq_iSup_sum]
    exact Measurable.iSup fun s => Finset.measurable_sum s fun i _ =>
      measurable_const.indicator (hJmeas k i)
  -- Pointwise Hausdorff bound at every level, from the cover-limit estimate.
  have hpointwise : ∀ t : ℝ, μH[d] (S ∩ {x | u x = t}) ≤ liminf (fun k => F k t) atTop := by
    intro t
    have hbound := Measure.hausdorffMeasure_le_liminf_tsum (X := X)
      (ι := fun k : ℕ => {i : ℕ // t ∈ J k i}) d (S ∩ {x | u x = t})
      (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) hεtendsto (fun k i => T k i.1)
      (Eventually.of_forall fun k i => hdiam k i.1)
      (Eventually.of_forall fun k x hx => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov k hx.1)
        exact Set.mem_iUnion.2 ⟨⟨i, hx.2 ▸ hJmem k i x ⟨hi, hx.1⟩⟩, hi⟩)
    refine hbound.trans (liminf_le_liminf (Eventually.of_forall fun k => ?_))
    have h1 : ∑' i : {i : ℕ // t ∈ J k i}, Metric.ediam (T k i.1) ^ d
        = ∑' i : ℕ, Set.indicator {i : ℕ | t ∈ J k i}
            (fun i => Metric.ediam (T k i) ^ d) i :=
      tsum_subtype {i : ℕ | t ∈ J k i} fun i => Metric.ediam (T k i) ^ d
    refine le_of_eq (h1.trans ?_)
    simp only [hF]
    exact tsum_congr fun i => by
      by_cases h : t ∈ J k i <;> simp [h]
  -- The majorants have nearly optimal integrals.
  have hintegral : ∀ k : ℕ, ∫⁻ t, F k t ∂(volume : Measure ℝ)
      ≤ 2 * (K : ℝ≥0∞) * (μH[d + 1] S + ((k : ℝ≥0∞) + 1)⁻¹) := by
    intro k
    simp only [hF]
    rw [lintegral_tsum fun i => (measurable_const.indicator (hJmeas k i)).aemeasurable]
    have hterm : ∀ i, ∫⁻ t, (J k i).indicator (fun _ => Metric.ediam (T k i) ^ d) t
          ∂(volume : Measure ℝ)
        ≤ 2 * (K : ℝ≥0∞) * ⨆ _ : (T k i).Nonempty, Metric.ediam (T k i) ^ (d + 1) := by
      intro i
      rw [lintegral_indicator_const (hJmeas k i)]
      by_cases hne : (T k i).Nonempty
      · have hpow : Metric.ediam (T k i) ^ d * (2 * (K : ℝ≥0∞) * Metric.ediam (T k i))
            = 2 * (K : ℝ≥0∞) * Metric.ediam (T k i) ^ (d + 1) := by
          rcases eq_or_ne (Metric.ediam (T k i)) 0 with h0 | h0
          · rcases eq_or_lt_of_le hd with hd0 | hd0
            · simp [h0, ← hd0]
            · rw [h0, ENNReal.zero_rpow_of_pos hd0, ENNReal.zero_rpow_of_pos (by linarith)]
              simp
          · rw [ENNReal.rpow_add _ _ h0 (hδtop k i), ENNReal.rpow_one]; ring
        calc Metric.ediam (T k i) ^ d * volume (J k i)
            ≤ Metric.ediam (T k i) ^ d * (2 * (K : ℝ≥0∞) * Metric.ediam (T k i)) := by
              gcongr; exact hJvol k i
          _ = 2 * (K : ℝ≥0∞) * Metric.ediam (T k i) ^ (d + 1) := hpow
          _ ≤ _ := by
              gcongr
              exact le_iSup (fun _ : (T k i).Nonempty => Metric.ediam (T k i) ^ (d + 1)) hne
      · have hvol : volume (J k i) = 0 := by
          refine nonpos_iff_eq_zero.1 ?_
          have hle := hJvol k i
          rw [Set.not_nonempty_iff_eq_empty.1 hne, Metric.ediam_empty, mul_zero] at hle
          exact hle
        simp [hvol]
    calc ∑' i, ∫⁻ t, (J k i).indicator (fun _ => Metric.ediam (T k i) ^ d) t
            ∂(volume : Measure ℝ)
        ≤ ∑' i, 2 * (K : ℝ≥0∞) * ⨆ _ : (T k i).Nonempty, Metric.ediam (T k i) ^ (d + 1) :=
          ENNReal.tsum_le_tsum hterm
      _ = 2 * (K : ℝ≥0∞) * ∑' i, ⨆ _ : (T k i).Nonempty, Metric.ediam (T k i) ^ (d + 1) :=
          ENNReal.tsum_mul_left
      _ ≤ 2 * (K : ℝ≥0∞) * (μH[d + 1] S + ((k : ℝ≥0∞) + 1)⁻¹) := by
          gcongr; exact (hcost k).le
  -- Fatou's lemma on the measurable majorants.
  refine ⟨fun t => liminf (fun k => F k t) atTop, Measurable.liminf hFmeas, hpointwise, ?_⟩
  refine (lintegral_liminf_le' fun k => (hFmeas k).aemeasurable).trans ?_
  have htend : Tendsto (fun k : ℕ => 2 * (K : ℝ≥0∞) * (μH[d + 1] S + ((k : ℝ≥0∞) + 1)⁻¹))
      atTop (𝓝 (2 * (K : ℝ≥0∞) * μH[d + 1] S)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr (by simp [ENNReal.mul_eq_top]))
    simpa using tendsto_const_nhds.add hεtendsto
  calc liminf (fun k => ∫⁻ t, F k t ∂(volume : Measure ℝ)) atTop
      ≤ liminf (fun k : ℕ => 2 * (K : ℝ≥0∞) * (μH[d + 1] S + ((k : ℝ≥0∞) + 1)⁻¹)) atTop :=
        liminf_le_liminf (Eventually.of_forall hintegral)
    _ = 2 * (K : ℝ≥0∞) * μH[d + 1] S := htend.liminf_eq

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
