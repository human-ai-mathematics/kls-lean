import FunctionalInequalities.Analysis.Hausdorff.Content
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import FunctionalInequalities.Analysis.Hausdorff.Measure

/-!
# The Eilenberg slicing inequality in codimension `m`

Metric-space layer of the codimension-`m` coarea route, depending on Mathlib only.  It is the
analogue of `Analysis/Hausdorff/Slicing.lean`, whose target is the real line; here the target is an
`m`-dimensional inner product space `W`, and the conclusion is

`∫⁻ t, μH[d] (S ∩ u ⁻¹' {t}) dt ≤ volume (closedBall 0 1) · K ^ m · μH[d + m] S`

in the measurable-majorant form the route needs: the slice function itself is not known to be
measurable, so the bound is stated for an explicit measurable majorant `F`, whose measurability is
part of the conclusion.  `ae_hausdorffMeasure_inter_levelSet_eq_zero` — a `μH[d + m]`-null set has
`μH[d]`-null slices for almost every level — is the corollary that the coarea route consumes.

**The argument is a covering argument, not Rademacher.**  At each scale the infimum formula for
`μH[d + m]` supplies a countable cover of `S` of small diameter and nearly optimal cost.  Because
`u` is Lipschitz **on `S`**, the `u`-image of each cover piece meeting `S` lies in a closed **ball**
of radius `K · diam` — this is the only place the codimension enters, replacing the interval of the
real-valued case, and its volume is `volume (closedBall 0 1) · (K · diam) ^ m` rather than
`2 K · diam`.  Summing the pieces whose ball contains `t` gives a measurable majorant at that
scale whose integral is at most `volume (closedBall 0 1) · K ^ m` times the cover cost;
`Measure.hausdorffMeasure_le_liminf_tsum` bounds the slice measure by the `liminf` of the
majorants, and Fatou's lemma finishes.

Degenerate data are covered by explicit branches rather than excluded.  `K = 0` with `m ≥ 1` makes
`u` constant on `S` and the bound `0`, which the one-point majorant of
`exists_measurable_majorant_of_eqOn` meets, and this also settles `μH[d + m] S = ∞` in that case,
where the covering argument has no finite-cost cover to start from; with `K ^ m ≠ 0` an infinite
cover cost makes the bound `∞`.  **A zero-dimensional target is included**: then `K ^ m = 1`, every
ball is the whole space and the inequality degenerates to `μH[d] S · volume univ ≤ volume univ ·
μH[d] S`.  `S` is not assumed measurable, bounded or nonempty, `u` is not assumed globally
Lipschitz, differentiable or measurable, `d = 0` is allowed, and zero-diameter or empty cover pieces
are harmless.
-/

noncomputable section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

section VectorHausdorffSlicing

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- A function constant on `S` has an explicit majorant of integral zero, once single points of the
target are null — that is, once the target is nontrivial.  No measurability or finiteness of `S` or
of `μ` is used. -/
theorem exists_measurable_majorant_of_eqOn_vector [Nontrivial W] {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {u : Y → W} {S : Set Y} (h : ∀ x ∈ S, ∀ y ∈ S, u x = u y) :
    ∃ F : W → ℝ≥0∞, Measurable F ∧ (∀ t, μ (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure W)) = 0 := by
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · exact ⟨0, measurable_const, fun t => by simp [hS], by simp⟩
  refine ⟨({u x₀} : Set W).indicator fun _ => ∞,
    measurable_const.indicator (measurableSet_singleton _), fun t => ?_, ?_⟩
  · by_cases ht : t = u x₀
    · simp [ht]
    · have hempty : S ∩ {x | u x = t} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => ht ?_
        rw [← hx.2, h x hx.1 x₀ hx₀]
      simp [hempty, ht]
  · rw [lintegral_indicator_const (measurableSet_singleton _), measure_singleton, mul_zero]

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Level balls of a cover.**  For a function Lipschitz on `N` with values in `W` and a cover
family of finite diameters, there are measurable subsets of the target containing the `u`-image of
every cover piece intersected with `N`, of volume at most
`volume (closedBall 0 1) · (K · diam) ^ m`.

This is where the codimension enters: in the real-valued case the slab is an interval of length
`2 K · diam`; here it is a **ball** of radius `K · diam`, whose volume carries the `m`-th power. -/
theorem exists_levelBall {u : X → W} {K : ℝ≥0} {N : Set X} (hu : LipschitzOnWith K u N)
    (T : ℕ → Set X) (hT : ∀ i, Metric.ediam (T i) ≠ ∞) :
    ∃ J : ℕ → Set W, (∀ i, MeasurableSet (J i)) ∧
      (∀ i, (volume : Measure W) (J i)
        ≤ (volume : Measure W) (Metric.closedBall (0 : W) 1)
            * ((K : ℝ≥0∞) * Metric.ediam (T i)) ^ (finrank ℝ W)) ∧
      (∀ i, ∀ x ∈ T i ∩ N, u x ∈ J i) ∧
      (∀ i, ¬ (T i ∩ N).Nonempty → J i = ∅) := by
  classical
  have hcast : ∀ i, (K : ℝ≥0∞) * Metric.ediam (T i)
      = ENNReal.ofReal ((K : ℝ) * (Metric.ediam (T i)).toReal) := fun i => by
    rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_toReal (hT i)]
  refine ⟨fun i => if h : (T i ∩ N).Nonempty then
      Metric.closedBall (u h.some) ((K : ℝ) * (Metric.ediam (T i)).toReal) else ∅, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split
    · exact measurableSet_closedBall
    · exact MeasurableSet.empty
  · intro i
    dsimp only
    by_cases h : (T i ∩ N).Nonempty
    · rw [dif_pos h, Measure.addHaar_closedBall' _ _
        (by positivity : (0:ℝ) ≤ (K : ℝ) * (Metric.ediam (T i)).toReal)]
      rw [ENNReal.ofReal_pow (by positivity), ← hcast i, mul_comm]
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
  · intro i hi
    dsimp only
    rw [dif_neg hi]

/-- **The Eilenberg slicing inequality in codimension `m`, measurable-majorant form.**  For `u`
Lipschitz on `S` with values in an `m`-dimensional target, the slice function
`t ↦ μH[d] (S ∩ {u = t})` is dominated by a measurable `F` with
`∫⁻ F ≤ volume (closedBall 0 1) · K ^ m · μH[d + m] S`.

The measurability of `F` is part of the conclusion and is not assumed of the slice function.  No
measurability, boundedness or nonemptiness of `S` is assumed, `u` is Lipschitz on `S` only, and
`K = 0`, `d = 0`, a zero-dimensional target, `μH[d + m] S = ∞` and zero-diameter cover pieces are
all handled by the argument itself. -/
theorem exists_measurable_majorant_vector {u : X → W} {K : ℝ≥0} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u S) :
    ∃ F : W → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure W))
        ≤ (volume : Measure W) (Metric.closedBall (0 : W) 1) * (K : ℝ≥0∞) ^ (finrank ℝ W)
            * μH[d + (finrank ℝ W : ℝ)] S := by
  classical
  set m : ℕ := finrank ℝ W with hm
  set C : ℝ≥0∞ := (volume : Measure W) (Metric.closedBall (0 : W) 1) with hC
  have hCpos : 0 < C := Metric.measure_closedBall_pos volume 0 one_pos
  have hCtop : C ≠ ∞ := measure_closedBall_lt_top.ne
  -- `K = 0` with a nontrivial target: `u` is constant on `S` and the bound is `0`.
  by_cases hK0 : K = 0 ∧ 0 < m
  · have : Nontrivial W := Module.nontrivial_of_finrank_pos (by rw [← hm]; exact hK0.2)
    obtain ⟨F, hFmeas, hFdom, hFint⟩ :=
      exists_measurable_majorant_of_eqOn_vector (μ := (μH[d] : Measure X)) (u := u) (S := S)
        fun x hx y hy => by
          have h := hu hx hy
          simp [hK0.1] at h
          exact h
    refine ⟨F, hFmeas, hFdom, ?_⟩
    rw [hFint]
    simp
  -- otherwise `K ^ m ≠ 0`, so an infinite cover cost makes the bound `∞`.
  have hKm : (K : ℝ≥0∞) ^ m ≠ 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · simp [hm0]
    · have hKne : K ≠ 0 := fun h => hK0 ⟨h, hmpos⟩
      exact pow_ne_zero _ (by exact_mod_cast hKne)
  rcases eq_or_ne (μH[d + (m : ℝ)] S) ∞ with htop | htop
  · refine ⟨fun _ => ∞, measurable_const, fun _ => le_top, ?_⟩
    rw [htop, ENNReal.mul_top (mul_ne_zero hCpos.ne' hKm)]
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
  choose T hcov hdiam hcost using fun k : ℕ =>
    exists_cover_familyCost_lt (A := S) (d := d + (m : ℝ)) (hεpos k)
      (ENNReal.lt_add_right htop (hεpos k).ne')
  have hδtop : ∀ k i, Metric.ediam (T k i) ≠ ∞ := fun k i =>
    ne_top_of_le_ne_top (hεtop k) (hdiam k i)
  choose J hJmeas hJvol hJmem hJempty using fun k : ℕ => exists_levelBall hu (T k) (hδtop k)
  -- The measurable majorants at each scale.
  set F : ℕ → W → ℝ≥0∞ := fun k t =>
    ∑' i, (J k i).indicator (fun _ => Metric.ediam (T k i) ^ d) t with hF
  have hFmeas : ∀ k, Measurable (F k) := by
    intro k
    simp only [hF, ENNReal.tsum_eq_iSup_sum]
    exact Measurable.iSup fun s => Finset.measurable_sum s fun i _ =>
      measurable_const.indicator (hJmeas k i)
  -- Pointwise Hausdorff bound at every level.
  have hpointwise : ∀ t : W, μH[d] (S ∩ {x | u x = t}) ≤ liminf (fun k => F k t) atTop := by
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
  -- The volume factor of a cover piece.
  have hpow : ∀ e : ℝ≥0∞, e ≠ ∞ →
      e ^ d * (C * ((K : ℝ≥0∞) * e) ^ m) = C * (K : ℝ≥0∞) ^ m * e ^ (d + (m : ℝ)) := by
    intro e he
    rw [mul_pow, ← ENNReal.rpow_natCast e m]
    rcases eq_or_ne e 0 with h0 | h0
    · subst h0
      rcases eq_or_lt_of_le hd with hd0 | hdpos
      · subst hd0
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · rw [hm0]; norm_num
        · have hmR : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast hmpos
          rw [ENNReal.zero_rpow_of_pos hmR, ENNReal.rpow_zero,
            ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < 0 + ((m : ℕ) : ℝ))]
          simp
      · have hsum : (0 : ℝ) < d + ((m : ℕ) : ℝ) := by positivity
        rw [ENNReal.zero_rpow_of_pos hdpos, ENNReal.zero_rpow_of_pos hsum]
        simp
    · rw [ENNReal.rpow_add _ _ h0 he]; ring
  -- The majorants have nearly optimal integrals.
  have hintegral : ∀ k : ℕ, ∫⁻ t, F k t ∂(volume : Measure W)
      ≤ C * (K : ℝ≥0∞) ^ m * (μH[d + (m : ℝ)] S + ((k : ℝ≥0∞) + 1)⁻¹) := by
    intro k
    simp only [hF]
    rw [lintegral_tsum fun i => (measurable_const.indicator (hJmeas k i)).aemeasurable]
    have hterm : ∀ i, ∫⁻ t, (J k i).indicator (fun _ => Metric.ediam (T k i) ^ d) t
          ∂(volume : Measure W)
        ≤ C * (K : ℝ≥0∞) ^ m * ⨆ _ : (T k i).Nonempty,
            Metric.ediam (T k i) ^ (d + (m : ℝ)) := by
      intro i
      rw [lintegral_indicator_const (hJmeas k i)]
      by_cases hne : (T k i).Nonempty
      · calc Metric.ediam (T k i) ^ d * (volume : Measure W) (J k i)
            ≤ Metric.ediam (T k i) ^ d * (C * ((K : ℝ≥0∞) * Metric.ediam (T k i)) ^ m) := by
              gcongr; exact hJvol k i
          _ = C * (K : ℝ≥0∞) ^ m * Metric.ediam (T k i) ^ (d + (m : ℝ)) :=
              hpow _ (hδtop k i)
          _ ≤ _ := by
              gcongr
              exact le_iSup
                (fun _ : (T k i).Nonempty => Metric.ediam (T k i) ^ (d + (m : ℝ))) hne
      · have hvol : (volume : Measure W) (J k i) = 0 := by
          rw [hJempty k i fun hc => hne (Set.Nonempty.mono Set.inter_subset_left hc)]
          simp
        simp [hvol]
    calc ∑' i, ∫⁻ t, (J k i).indicator (fun _ => Metric.ediam (T k i) ^ d) t
            ∂(volume : Measure W)
        ≤ ∑' i, C * (K : ℝ≥0∞) ^ m * ⨆ _ : (T k i).Nonempty,
            Metric.ediam (T k i) ^ (d + (m : ℝ)) := ENNReal.tsum_le_tsum hterm
      _ = C * (K : ℝ≥0∞) ^ m
            * ∑' i, ⨆ _ : (T k i).Nonempty, Metric.ediam (T k i) ^ (d + (m : ℝ)) :=
          ENNReal.tsum_mul_left
      _ ≤ C * (K : ℝ≥0∞) ^ m * (μH[d + (m : ℝ)] S + ((k : ℝ≥0∞) + 1)⁻¹) := by
          gcongr; exact (hcost k).le
  -- Fatou's lemma on the measurable majorants.
  refine ⟨fun t => liminf (fun k => F k t) atTop, Measurable.liminf hFmeas, hpointwise, ?_⟩
  refine (lintegral_liminf_le' fun k => (hFmeas k).aemeasurable).trans ?_
  have htend : Tendsto (fun k : ℕ =>
      C * (K : ℝ≥0∞) ^ m * (μH[d + (m : ℝ)] S + ((k : ℝ≥0∞) + 1)⁻¹)) atTop
      (𝓝 (C * (K : ℝ≥0∞) ^ m * μH[d + (m : ℝ)] S)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr (by
      simp [ENNReal.mul_eq_top, hCtop, ENNReal.pow_eq_top_iff]))
    simpa using tendsto_const_nhds.add hεtendsto
  calc liminf (fun k => ∫⁻ t, F k t ∂(volume : Measure W)) atTop
      ≤ liminf (fun k : ℕ =>
          C * (K : ℝ≥0∞) ^ m * (μH[d + (m : ℝ)] S + ((k : ℝ≥0∞) + 1)⁻¹)) atTop :=
        liminf_le_liminf (Eventually.of_forall hintegral)
    _ = C * (K : ℝ≥0∞) ^ m * μH[d + (m : ℝ)] S := htend.liminf_eq

/-- **Null slicing in codimension `m`.**  If `N` carries no `(d + m)`-dimensional Hausdorff measure
and `u` is Lipschitz on `N`, then `μH[d] (N ∩ {u = t}) = 0` for almost every level `t`.

The null case of the Eilenberg inequality: the majorant has vanishing integral, and the majorant —
unlike the slice function — is measurable, so `lintegral_eq_zero_iff` applies. -/
theorem ae_hausdorffMeasure_inter_levelSet_eq_zero_vector
    {u : X → W} {K : ℝ≥0} {N : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u N) (hN : μH[d + (finrank ℝ W : ℝ)] N = 0) :
    ∀ᵐ t ∂(volume : Measure W), μH[d] (N ∩ {x | u x = t}) = 0 := by
  obtain ⟨F, hFmeas, hFdom, hFint⟩ := exists_measurable_majorant_vector hd hu
  rw [hN, mul_zero] at hFint
  filter_upwards [(lintegral_eq_zero_iff hFmeas).1 (le_antisymm hFint (by simp))] with t ht
  exact le_antisymm (by simpa [ht] using hFdom t) (by simp)

/-! ### The normalized convention -/

section Normalized

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section NormalizedSlices

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
/-- The normalization constant of `KLS.hausdorffNormalized` is positive and finite, so a set is
null for the normalized measure exactly when it is null for the raw one. -/
theorem hausdorffNormalized_eq_zero_iff (k : ℕ) (A : Set V) :
    KLS.hausdorffNormalized V k A = 0 ↔ μH[(k : ℝ)] A = 0 := by
  have hpos : 0 < KLS.unitBallVolume k / 2 ^ k := by
    unfold KLS.unitBallVolume; positivity
  rw [KLS.hausdorffNormalized, Measure.smul_apply, smul_eq_mul, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (by simp [ENNReal.ofReal_eq_zero, not_le, hpos])
    · exact h
  · exact fun h => Or.inr h

/-- **Null slicing in the normalized convention.**  The form the codimension-`m` coarea layer
consumes: a set with no `(d + m)`-dimensional normalized measure has null slices at almost every
level. -/
theorem ae_hausdorffNormalized_inter_levelSet_eq_zero_vector {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] {u : V → W} {K : ℝ≥0} {N : Set V} {k : ℕ}
    (hu : LipschitzOnWith K u N)
    (hN : KLS.hausdorffNormalized V (k + finrank ℝ W) N = 0) :
    ∀ᵐ t ∂(volume : Measure W), KLS.hausdorffNormalized V k (N ∩ {x | u x = t}) = 0 := by
  have hraw : μH[((k : ℝ) + (finrank ℝ W : ℝ))] N = 0 := by
    have h := (hausdorffNormalized_eq_zero_iff (V := V) (k + finrank ℝ W) N).1 hN
    rwa [show (((k + finrank ℝ W : ℕ) : ℝ)) = (k : ℝ) + (finrank ℝ W : ℝ) by push_cast; ring] at h
  filter_upwards [ae_hausdorffMeasure_inter_levelSet_eq_zero_vector
    (Nat.cast_nonneg k) hu hraw] with t ht
  exact (hausdorffNormalized_eq_zero_iff (V := V) k _).2 ht

end NormalizedSlices

end Normalized

end VectorHausdorffSlicing

end FunctionalInequalities.Analysis
