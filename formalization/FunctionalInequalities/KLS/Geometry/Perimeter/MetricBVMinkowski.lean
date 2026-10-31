module

public import FunctionalInequalities.Analysis.MetricBV.Basic
public import FunctionalInequalities.Analysis.MetricBV.Complement
public import FunctionalInequalities.Analysis.MetricBV.Approximation
public import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiContent
public import FunctionalInequalities.KLS.Geometry.Cheeger.LocalSlopeCoarea

/-!
# Metric BV perimeter below the outer Minkowski content

One inequality between two existing objects: the metric BV perimeter `MetricBV.perimeter` is at
most the outer Minkowski content `Isoperimetry.minkowskiContent` of a measurable set, for every
finite Borel measure on a metric space (`perimeter_le_minkowskiContent`; 2026-09-30: generic metric
and finite-measure scope; the ratio-recovery section, whose symmetric quotients use `1 - ν B`, stays
at probability laws). This is not an
identification of the two quantities or of their Cheeger infima. The finite-target bridge
`perimeter_le_minkowskiContent_of_measure_lt_top` also permits arbitrary Borel measures,
including infinite total mass, with measurable finite-mass targets; recovery below still
retains its finite-total-mass hypotheses until separately extended.

The naive ramp `(1 - d(·, B) / r)₊` equals `1` on `closure B` but may have slope `1 / r` at
boundary points of `B`, which can carry mass. The two-radius plateau ramp `plateauRamp B s t`
equals `1` on the open set `{d(·, B) < s}` and `0` on the open set `{d(·, B) > t}`, so its slope
vanishes there and is at most `(t - s)⁻¹` on the closed shell `{s ≤ d(·, B) ≤ t}`, which lies in
`B^r \ B` for `0 < s < t < r` (`apply_plateauRamp_le`). The ramp statements hold on every metric
space.

With the local-slope Minkowski coarea inequality, the superlevel sets of a globally Lipschitz
function, in particular of a test, have integrated Minkowski content and integrated metric BV
perimeter at most the slope integral (`lintegral_minkowskiContent_superlevel_le_cost`,
`lintegral_perimeter_superlevel_le_cost`). These are integrated upper bounds, not a pointwise
comparison of content with perimeter.

Quantitative superlevel selection (`exists_superlevel_selection`): for a test `f`, a set `B`,
`0 < δ < 1/2` and `ε > 0`, some level `t ∈ (δ, 1 - δ)` has a measurable superlevel set whose
Minkowski content is at most `cost f / (1 - 2δ) + ε` and whose indicator is within
`indicatorDistance f B / δ` of `1_B` in `L¹`. The level is chosen by positive slack, without
measurability of the content in `t`; the error bound is pointwise.

Minkowski recovery (`minkowskiRecoverySet`): for finite perimeter, the superlevel sets selected
from epsilon recovery tests with widths `1/(n + 3)` form an explicit sequence of measurable sets
converging to `B` in `L¹` whose Minkowski contents converge to the perimeter of `B`
(`tendsto_minkowskiContent_minkowskiRecoverySet`). The lower bound is lower semicontinuity
(`perimeter_le_liminf_minkowskiContent`), not a pointwise comparison with test costs.
For measurable `B` the masses of the recovery sets converge to `ν B`; if `0 < ν B < 1` they
eventually lie in `(0, 1)` and the symmetric Cheeger quotients `content / min (mass, 1 - mass)`
and `perimeter / min (mass, 1 - mass)` of the recovery sets converge to that of `B`
(`tendsto_minkowskiContent_div_min_minkowskiRecoverySet`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace FunctionalInequalities.KLS.MetricBV

section PlateauRamp

variable {X : Type*} [MetricSpace X]

/-- The plateau ramp `clamp ((t - d(x, B)) / (t - s))`: `1` where `d(x, B) ≤ s`, `0` where
`t ≤ d(x, B)`. -/
def plateauRamp (B : Set X) (s t : ℝ) (x : X) : ℝ :=
  clampUnit ((t - Metric.infDist x B) / (t - s))

theorem plateauRamp_nonneg (B : Set X) (s t : ℝ) (x : X) : 0 ≤ plateauRamp B s t x :=
  clampUnit_nonneg _

theorem plateauRamp_le_one (B : Set X) (s t : ℝ) (x : X) : plateauRamp B s t x ≤ 1 :=
  clampUnit_le_one _

theorem plateauRamp_eq_one {B : Set X} {s t : ℝ} (hst : s < t) {x : X}
    (hx : Metric.infDist x B ≤ s) : plateauRamp B s t x = 1 := by
  have h : 1 ≤ (t - Metric.infDist x B) / (t - s) := by
    rw [le_div_iff₀ (sub_pos.2 hst)]
    linarith
  simp [plateauRamp, clampUnit, min_eq_right h]

theorem plateauRamp_eq_zero {B : Set X} {s t : ℝ} (hst : s < t) {x : X}
    (hx : t ≤ Metric.infDist x B) : plateauRamp B s t x = 0 := by
  have h : (t - Metric.infDist x B) / (t - s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.2 hst).le
  simp [plateauRamp, clampUnit, min_eq_left (h.trans zero_le_one), max_eq_right h]

/-- The plateau ramp is `(t - s)⁻¹`-Lipschitz. -/
theorem lipschitzWith_plateauRamp (B : Set X) {s t : ℝ} (hst : s < t) :
    LipschitzWith (Real.toNNReal (t - s)⁻¹) (plateauRamp B s t) := by
  apply LipschitzWith.of_dist_le' (K := (t - s)⁻¹)
  intro x y
  have hts : 0 < t - s := sub_pos.2 hst
  have hinf : |Metric.infDist x B - Metric.infDist y B| ≤ dist x y := by
    simpa [Real.dist_eq] using (Metric.lipschitz_infDist_pt (s := B)).dist_le_mul x y
  rw [Real.dist_eq]
  refine (abs_clampUnit_sub_le _ _).trans ?_
  rw [show (t - Metric.infDist x B) / (t - s) - (t - Metric.infDist y B) / (t - s) =
      -(Metric.infDist x B - Metric.infDist y B) / (t - s) by ring, abs_div, abs_neg,
    abs_of_pos hts, div_le_iff₀ hts]
  calc |Metric.infDist x B - Metric.infDist y B| ≤ dist x y := hinf
    _ = (t - s)⁻¹ * dist x y * (t - s) := by field_simp

/-- Boundary-safe slope bound: the slope vanishes off the closed shell `{s ≤ d(·, B) ≤ t}`, in
particular on a neighbourhood of `closure B`, and is at most `(t - s)⁻¹` on it. -/
theorem apply_plateauRamp_le (B : Set X) {s t : ℝ} (hst : s < t) (x : X) :
    Energy.LocalSlope.apply (plateauRamp B s t) x ≤
      ((fun y => Metric.infDist y B) ⁻¹' Set.Icc s t).indicator
        (fun _ => ENNReal.ofReal (t - s)⁻¹) x := by
  by_cases hx : x ∈ (fun y => Metric.infDist y B) ⁻¹' Set.Icc s t
  · rw [Set.indicator_of_mem hx]
    exact Energy.LocalSlope.apply_le_of_lipschitzWith (lipschitzWith_plateauRamp B hst) x
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_preimage, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hlt | hgt
    · refine (Energy.LocalSlope.apply_eq_zero_of_eqOn_ball
        (r₀ := s - Metric.infDist x B) (by linarith) fun y hy => ?_).le
      have hy' : Metric.infDist y B ≤ s := by
        have := Metric.infDist_le_infDist_add_dist (s := B) (x := y) (y := x)
        linarith
      rw [plateauRamp_eq_one hst hy', plateauRamp_eq_one hst hlt.le]
    · refine (Energy.LocalSlope.apply_eq_zero_of_eqOn_ball
        (r₀ := Metric.infDist x B - t) (by linarith) fun y hy => ?_).le
      have hy' : t ≤ Metric.infDist y B := by
        have := Metric.infDist_le_infDist_add_dist (s := B) (x := x) (y := y)
        rw [dist_comm] at this
        linarith
      rw [plateauRamp_eq_zero hst hy', plateauRamp_eq_zero hst hgt.le]

/-- The plateau ramp differs from `1_B` only on `B^t \ B`, by at most one. -/
theorem enorm_plateauRamp_sub_le {B : Set X} (hB : B.Nonempty) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (x : X) :
    ‖plateauRamp B s t x - B.indicator (1 : X → ℝ) x‖ₑ ≤
      (Metric.thickening t B \ B).indicator (1 : X → ENNReal) x := by
  by_cases hxB : x ∈ B
  · have hx : Metric.infDist x B ≤ s := by
      rw [Metric.infDist_zero_of_mem hxB]
      exact hs
    rw [plateauRamp_eq_one hst hx, Set.indicator_of_mem hxB]
    simp
  · rw [Set.indicator_of_notMem hxB, sub_zero]
    by_cases hxt : x ∈ Metric.thickening t B
    · rw [Set.indicator_of_mem (show x ∈ Metric.thickening t B \ B from ⟨hxt, hxB⟩),
        Real.enorm_eq_ofReal_abs, abs_of_nonneg (plateauRamp_nonneg B s t x)]
      simpa using ENNReal.ofReal_le_one.2 (plateauRamp_le_one B s t x)
    · rw [Metric.mem_thickening_iff_infDist_lt hB, not_lt] at hxt
      rw [plateauRamp_eq_zero hst hxt]
      simp

variable [MeasurableSpace X] [BorelSpace X]

/-- The slope integral of the plateau ramp is at most `(t - s)⁻¹ ν(B^r \ B)`. -/
theorem lintegral_apply_plateauRamp_le (ν : Measure X) {B : Set X} (hB : B.Nonempty)
    {s t r : ℝ} (hs : 0 < s) (hst : s < t) (htr : t < r) :
    ∫⁻ x, Energy.LocalSlope.apply (plateauRamp B s t) x ∂ν ≤
      ENNReal.ofReal (t - s)⁻¹ * ν (Metric.thickening r B \ B) := by
  have hA : MeasurableSet ((fun y => Metric.infDist y B) ⁻¹' Set.Icc s t) :=
    (Metric.continuous_infDist_pt B).measurable measurableSet_Icc
  have hsub : (fun y => Metric.infDist y B) ⁻¹' Set.Icc s t ⊆ Metric.thickening r B \ B :=
    fun y hy => ⟨(Metric.mem_thickening_iff_infDist_lt hB).2 (hy.2.trans_lt htr), fun hyB => by
      have h0 := Metric.infDist_zero_of_mem hyB
      have h1 := hy.1
      simp only at h1
      linarith⟩
  calc ∫⁻ x, Energy.LocalSlope.apply (plateauRamp B s t) x ∂ν
      ≤ ∫⁻ x, ((fun y => Metric.infDist y B) ⁻¹' Set.Icc s t).indicator
          (fun _ => ENNReal.ofReal (t - s)⁻¹) x ∂ν :=
        lintegral_mono (apply_plateauRamp_le B hst)
    _ = ENNReal.ofReal (t - s)⁻¹ * ν ((fun y => Metric.infDist y B) ⁻¹' Set.Icc s t) :=
        lintegral_indicator_const hA _
    _ ≤ ENNReal.ofReal (t - s)⁻¹ * ν (Metric.thickening r B \ B) := by
        gcongr

/-- The `L¹` distance of the plateau ramp to `1_B` is at most `ν(B^r \ B)` for `t ≤ r`. -/
theorem lintegral_enorm_plateauRamp_sub_le (ν : Measure X) {B : Set X} (hB : B.Nonempty)
    (hBm : MeasurableSet B) {s t r : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) :
    ∫⁻ x, ‖plateauRamp B s t x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν ≤
      ν (Metric.thickening r B \ B) := by
  calc ∫⁻ x, ‖plateauRamp B s t x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
      ≤ ∫⁻ x, (Metric.thickening t B \ B).indicator (1 : X → ENNReal) x ∂ν :=
        lintegral_mono (enorm_plateauRamp_sub_le hB hs hst)
    _ = ν (Metric.thickening t B \ B) :=
        lintegral_indicator_one (Metric.isOpen_thickening.measurableSet.diff hBm)
    _ ≤ ν (Metric.thickening r B \ B) :=
        measure_mono (Set.sdiff_subset_sdiff_left (Metric.thickening_mono htr B))

end PlateauRamp

section Bridge

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/--
The metric BV perimeter of a measurable set is at most its outer Minkowski content, for every
Borel measure and measurable finite-mass target. Below any level `a` above the content, radii `r_k →
0` with content quotient
below `a` carry plateau ramps with `L¹` error at most `a r_k` and slope integral at most
`a (1 + 1/(k+1))`; the finite-target Lipschitz bridge then bounds the perimeter by `a`. Top
content is a trivial bound and the empty set has perimeter zero. -/
theorem perimeter_le_minkowskiContent_of_measure_lt_top (ν : Measure V) {B : Set V}
    (hBm : MeasurableSet B) (hνB : ν B < ⊤) :
    perimeter (ν : Measure V) B ≤ Isoperimetry.minkowskiContent ν B := by
  rcases Set.eq_empty_or_nonempty B with rfl | hB
  · rw [perimeter_empty]
    exact bot_le
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  rcases eq_or_ne a ⊤ with rfl | ha_top
  · exact le_top
  have hfreq :
    ∃ᶠ r in 𝓝[>] (0 : ℝ),
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r < a :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) ha
  have hidx :
    ∀ k : ℕ,
      ∃ r : ℝ,
        ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r < a ∧
          r ∈ Set.Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) :=
    fun k => (hfreq.and_eventually (Ioo_mem_nhdsGT (by positivity))).exists
  choose r hrQ hr using hidx
  have hr0 : ∀ k, 0 < r k := fun k =>
    (hr k).1
  -- plateau radii `s k < t k < r k` with `r k / (t k - s k) = 1 + 1 / (k + 1)`

  set s : ℕ → ℝ := fun k => r k / (2 * ((k : ℝ) + 2)) with hs_def
  set t : ℕ → ℝ := fun k => r k - s k with ht_def
  have hs0 : ∀ k, 0 < s k := fun k => by
    have := hr0 k
    simp only [hs_def]
    positivity
  have hs_lt : ∀ k, 2 * s k < r k := fun k => by
    have h := hr0 k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    simp only [hs_def]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hst : ∀ k, s k < t k := fun k => by
    simp only [ht_def]
    linarith [hs_lt k]
  have htr : ∀ k, t k < r k := fun k => by
    simp only [ht_def]
    linarith [hs0 k]
  have hratio : ∀ k : ℕ, r k * (t k - s k)⁻¹ = 1 + 1 / ((k : ℝ) + 1) := fun k => by
    have h := hr0 k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hts : t k - s k = r k * (((k : ℝ) + 1) / ((k : ℝ) + 2)) := by
      simp only [ht_def, hs_def]
      field_simp
      ring
    rw [hts, mul_inv, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul, inv_div]
    field_simp
    ring
  -- the annulus mass is `Q (r k) * r k < a * r k`

  have hmass :
    ∀ k, (ν : Measure V) (Metric.thickening (r k) B \ B) ≤ a * ENNReal.ofReal (r k) := fun k => by
    rw [measure_sdiff (Metric.self_subset_thickening (hr0 k) B) hBm.nullMeasurableSet hνB.ne]
    calc
      (ν : Measure V) (Metric.thickening (r k) B) - (ν : Measure V) B =
          ((ν : Measure V) (Metric.thickening (r k) B) - (ν : Measure V) B) /
              ENNReal.ofReal (r k) *
            ENNReal.ofReal (r k) :=
        (ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 (hr0 k)).ne' ENNReal.ofReal_ne_top).symm
      _ ≤ a * ENNReal.ofReal (r k) := by
        gcongr
        exact (hrQ k).le
  have hlip : ∀ k, ∃ K : ℝ≥0, LipschitzWith K (plateauRamp B (s k) (t k)) := fun k =>
    ⟨_, lipschitzWith_plateauRamp B (hst k)⟩
  have hconv :
    Tendsto
      (fun k =>
        ∫⁻ x, ‖plateauRamp B (s k) (t k) x - B.indicator (1 : V → ℝ) x‖ₑ ∂(ν : Measure V))
      atTop (𝓝 0) := by
    have hup : Tendsto (fun k : ℕ => a * ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using
        ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat) (Or.inr ha_top)
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
        fun k => ?_
    calc
      ∫⁻ x, ‖plateauRamp B (s k) (t k) x - B.indicator (1 : V → ℝ) x‖ₑ ∂(ν : Measure V) ≤
          (ν : Measure V) (Metric.thickening (r k) B \ B) :=
        lintegral_enorm_plateauRamp_sub_le _ hB hBm (hs0 k).le (hst k) (htr k).le
      _ ≤ a * ENNReal.ofReal (r k) := hmass k
      _ ≤ a * ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
        gcongr
        exact (hr k).2.le
  have hcost :
    ∀ k,
      ∫⁻ x, Energy.LocalSlope.apply (plateauRamp B (s k) (t k)) x ∂(ν : Measure V) ≤
        a * ENNReal.ofReal (1 + 1 / ((k : ℝ) + 1)) :=
    fun k => by
    calc
      ∫⁻ x, Energy.LocalSlope.apply (plateauRamp B (s k) (t k)) x ∂(ν : Measure V) ≤
          ENNReal.ofReal (t k - s k)⁻¹ * (ν : Measure V) (Metric.thickening (r k) B \ B) :=
        lintegral_apply_plateauRamp_le _ hB (hs0 k) (hst k) (htr k)
      _ ≤ ENNReal.ofReal (t k - s k)⁻¹ * (a * ENNReal.ofReal (r k)) := by
        gcongr
        exact hmass k
      _ = a * ENNReal.ofReal (r k * (t k - s k)⁻¹) := by
        rw [ENNReal.ofReal_mul (hr0 k).le]
        ring
      _ = a * ENNReal.ofReal (1 + 1 / ((k : ℝ) + 1)) := by rw [hratio k]
  have hlim : Tendsto (fun k : ℕ => a * ENNReal.ofReal (1 + 1 / ((k : ℝ) + 1))) atTop (𝓝 a) := by
    have h1 : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using
        (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h1) (Or.inr ha_top)
  calc
    perimeter (ν : Measure V) B ≤
        liminf
          (fun k =>
            ∫⁻ x, Energy.LocalSlope.apply (plateauRamp B (s k) (t k)) x ∂(ν : Measure V))
          atTop :=
      perimeter_le_liminf_of_lipschitz_of_measure_lt_top ν hBm hνB hlip hconv
    _ ≤ liminf (fun k : ℕ => a * ENNReal.ofReal (1 + 1 / ((k : ℝ) + 1))) atTop :=
      liminf_le_liminf (Eventually.of_forall hcost)
    _ = a := hlim.liminf_eq

/-- The metric BV perimeter is at most lower Minkowski content for a finite Borel measure
and every measurable target. This retained interface follows from the finite-target bridge. -/
theorem perimeter_le_minkowskiContent (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hBm : MeasurableSet B) :
    perimeter (ν : Measure V) B ≤ Isoperimetry.minkowskiContent ν B :=
  perimeter_le_minkowskiContent_of_measure_lt_top ν hBm (measure_lt_top ν B)

/-- Integrated BV-perimeter coarea upper bound for a globally Lipschitz function: the
superlevel sets are closed, so each perimeter is at most the Minkowski content, and the local-slope
Minkowski coarea inequality applies. -/
theorem lintegral_perimeter_superlevel_le_localSlope (ν : Measure V) [IsFiniteMeasure ν] {u : V → ℝ}
    {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, perimeter (ν : Measure V) {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂(ν : Measure V) :=
  (lintegral_mono fun _ => perimeter_le_minkowskiContent ν
      (measurableSet_le measurable_const hK.continuous.measurable)).trans
    (Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν hK)

/-- The local-slope Minkowski coarea inequality for a metric BV test: the right side is its
cost. -/
theorem lintegral_minkowskiContent_superlevel_le_cost (ν : Measure V) [IsFiniteMeasure ν]
    (f : Test V) :
    ∫⁻ t, Isoperimetry.minkowskiContent ν {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
      cost (ν : Measure V) f := by
  obtain ⟨K, hK⟩ := f.lipschitz
  exact Isoperimetry.lintegral_minkowskiContent_superlevel_le_localSlope ν hK

/-- Integrated BV-perimeter coarea upper bound for a metric BV test. -/
theorem lintegral_perimeter_superlevel_le_cost (ν : Measure V) [IsFiniteMeasure ν] (f : Test V) :
    ∫⁻ t, perimeter (ν : Measure V) {x | t ≤ f x} ∂(volume : Measure ℝ) ≤
      cost (ν : Measure V) f := by
  obtain ⟨K, hK⟩ := f.lipschitz
  exact lintegral_perimeter_superlevel_le_localSlope ν hK

end Bridge

section SuperlevelSelection

/-- Pointwise indicator error of a superlevel set at a level `t ∈ [δ, 1 - δ]`: wherever the
indicators differ, the function is at least `δ` away from `1_B`. -/
theorem enorm_indicator_superlevel_sub_le {X : Type*} (g : X → ℝ) (B : Set X) {δ t : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t) (ht : t ≤ 1 - δ) (x : X) :
    ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ≤
      ‖g x - B.indicator (1 : X → ℝ) x‖ₑ / ENNReal.ofReal δ := by
  have hδne : ENNReal.ofReal δ ≠ 0 := (ENNReal.ofReal_pos.2 hδ).ne'
  have hone : ∀ c : ℝ, δ ≤ |c| → (1 : ℝ≥0∞) ≤ ‖c‖ₑ / ENNReal.ofReal δ := fun c hc => by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hδne) (Or.inl ENNReal.ofReal_ne_top), one_mul,
      Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal hc
  by_cases hA : t ≤ g x <;> by_cases hB : x ∈ B
  · have hxA : x ∈ {y | t ≤ g y} := hA
    simp [Set.indicator_of_mem hxA, Set.indicator_of_mem hB]
  · have hxA : x ∈ {y | t ≤ g y} := hA
    rw [Set.indicator_of_mem hxA, Set.indicator_of_notMem hB]
    simpa using hone (g x) (by rw [abs_of_pos (by linarith)]; linarith)
  · have hxA : x ∉ {y | t ≤ g y} := hA
    rw [Set.indicator_of_notMem hxA, Set.indicator_of_mem hB]
    have hlt : g x < t := not_le.mp hA
    simpa using hone (g x - 1) (by rw [abs_of_neg (by linarith)]; linarith)
  · have hxA : x ∉ {y | t ≤ g y} := hA
    simp [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hB]

/-- Integrated indicator error of a superlevel set at a level `t ∈ [δ, 1 - δ]`. No measurability
of `g`, `B` or the superlevel set is needed. -/
theorem lintegral_enorm_indicator_superlevel_sub_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (g : X → ℝ) (B : Set X) {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (ht : t ≤ 1 - δ) :
    ∫⁻ x, ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
      (∫⁻ x, ‖g x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) / ENNReal.ofReal δ := by
  have hinv : (ENNReal.ofReal δ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hδ).ne'
  calc ∫⁻ x, ‖{y | t ≤ g y}.indicator (1 : X → ℝ) x - B.indicator 1 x‖ₑ ∂ν
      ≤ ∫⁻ x, ‖g x - B.indicator (1 : X → ℝ) x‖ₑ * (ENNReal.ofReal δ)⁻¹ ∂ν :=
        lintegral_mono fun x => by
          simpa [div_eq_mul_inv] using enorm_indicator_superlevel_sub_le g B hδ hδt ht x
    _ = (∫⁻ x, ‖g x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) / ENNReal.ofReal δ := by
        rw [lintegral_mul_const' _ _ hinv, div_eq_mul_inv]

/-- Selection with positive slack: if a (not necessarily measurable) `φ` has lower integral at
most a finite `C` over `(a, b)`, some point of `(a, b)` has `φ t ≤ C / (b - a) + ε`. -/
theorem exists_mem_Ioo_le_div_add_of_setLIntegral_le {φ : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a < b)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hφ : ∫⁻ t in Set.Ioo a b, φ t ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo a b, φ t ≤ C / ENNReal.ofReal (b - a) + ENNReal.ofReal ε := by
  by_contra h
  push Not at h
  have hL0 : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  have hlow : (C / ENNReal.ofReal (b - a) + ENNReal.ofReal ε) * ENNReal.ofReal (b - a) ≤ C := by
    calc (C / ENNReal.ofReal (b - a) + ENNReal.ofReal ε) * ENNReal.ofReal (b - a)
        = ∫⁻ _ in Set.Ioo a b, (C / ENNReal.ofReal (b - a) + ENNReal.ofReal ε) := by
          rw [setLIntegral_const, Real.volume_Ioo]
      _ ≤ ∫⁻ t in Set.Ioo a b, φ t := setLIntegral_mono' measurableSet_Ioo fun t ht => (h t ht).le
      _ ≤ C := hφ
  rw [add_mul, ENNReal.div_mul_cancel hL0 ENNReal.ofReal_ne_top] at hlow
  have hpos : 0 < ENNReal.ofReal ε * ENNReal.ofReal (b - a) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hε).ne' hL0
  exact absurd hlow (not_le.2 (ENNReal.lt_add_right hC hpos.ne'))

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- Quantitative superlevel selection for a metric BV test, from the local-slope coarea
inequality restricted to `(δ, 1 - δ)`: a measurable superlevel set with content at most
`cost f / (1 - 2δ) + ε` and `L¹` indicator error at most `indicatorDistance f B / δ`. The set `B`
need not be measurable. -/
theorem exists_superlevel_selection (ν : Measure V) [IsFiniteMeasure ν] (f : Test V) (B : Set V)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ), MeasurableSet {x | t ≤ f x} ∧
      Isoperimetry.minkowskiContent ν {x | t ≤ f x} ≤
        cost (ν : Measure V) f / ENNReal.ofReal (1 - 2 * δ) + ENNReal.ofReal ε ∧
      ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        indicatorDistance (ν : Measure V) f B / ENNReal.ofReal δ := by
  have hab : δ < 1 - δ := by linarith
  have hcoarea : ∫⁻ t in Set.Ioo δ (1 - δ), Isoperimetry.minkowskiContent ν {x | t ≤ f x} ≤
      cost (ν : Measure V) f :=
    (lintegral_mono' Measure.restrict_le_self le_rfl).trans
      (lintegral_minkowskiContent_superlevel_le_cost ν f)
  obtain ⟨t, ht, hc⟩ :=
    exists_mem_Ioo_le_div_add_of_setLIntegral_le hab (cost_ne_top _ f) hcoarea hε
  have hL : 1 - δ - δ = 1 - 2 * δ := by ring
  rw [hL] at hc
  obtain ⟨K, hK⟩ := f.lipschitz
  exact ⟨t, ht, measurableSet_le measurable_const hK.continuous.measurable, hc,
    lintegral_enorm_indicator_superlevel_sub_le _ f B hδ ht.1.le ht.2.le⟩

end SuperlevelSelection

section MinkowskiRecovery

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- Lower bound for Minkowski recovery: for measurable sets converging to `B` in `L¹(ν)`, the
perimeter of `B` is at most the liminf of their Minkowski contents (lower semicontinuity and
`perimeter ≤ content`). No finiteness is assumed. -/
theorem perimeter_le_liminf_minkowskiContent (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    perimeter (ν : Measure V) B ≤
      liminf (fun n => Isoperimetry.minkowskiContent ν (A n)) atTop :=
  (perimeter_le_liminf_of_tendsto (ν : Measure V) hA hconv).trans
    (liminf_le_liminf (Eventually.of_forall fun n => perimeter_le_minkowskiContent ν (hA n)))

/-- The selection widths `1 / (n + 3)`. -/
def recoveryWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 3)

theorem recoveryWidth_pos (n : ℕ) : 0 < recoveryWidth n := by
  unfold recoveryWidth
  positivity

theorem recoveryWidth_lt_half (n : ℕ) : recoveryWidth n < 1 / 2 := by
  unfold recoveryWidth
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem tendsto_recoveryWidth : Tendsto recoveryWidth atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (recoveryWidth_pos n).le) fun n => ?_
  unfold recoveryWidth
  gcongr
  linarith

/-- The `n`-th epsilon recovery test: indicator error below `recoveryWidth n / (n + 1)` and cost
below `perimeter ν B + 1/(n + 1)`. -/
def minkowskiRecoveryTest (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) : Test V :=
  recoveryTest hB (ε := ENNReal.ofReal (recoveryWidth n / ((n : ℝ) + 1)))
    (η := ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    (ENNReal.ofReal_pos.2 (div_pos (recoveryWidth_pos n) (by positivity)))
    (ENNReal.ofReal_pos.2 (by positivity))

theorem exists_minkowskiRecoveryLevel (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) :
    ∃ t ∈ Set.Ioo (recoveryWidth n) (1 - recoveryWidth n),
      MeasurableSet {x | t ≤ minkowskiRecoveryTest ν hB n x} ∧
      Isoperimetry.minkowskiContent ν {x | t ≤ minkowskiRecoveryTest ν hB n x} ≤
        cost (ν : Measure V) (minkowskiRecoveryTest ν hB n) /
          ENNReal.ofReal (1 - 2 * recoveryWidth n) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
      ∫⁻ x, ‖{x | t ≤ minkowskiRecoveryTest ν hB n x}.indicator (1 : V → ℝ) x -
          B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        indicatorDistance (ν : Measure V) (minkowskiRecoveryTest ν hB n) B /
          ENNReal.ofReal (recoveryWidth n) :=
  exists_superlevel_selection ν _ B (recoveryWidth_pos n) (recoveryWidth_lt_half n)
    (by positivity)

/-- The selected level of the `n`-th recovery test. -/
def minkowskiRecoveryLevel (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) : ℝ :=
  Classical.choose (exists_minkowskiRecoveryLevel ν hB n)

/-- The `n`-th Minkowski recovery set: a closed superlevel set of the `n`-th recovery test. -/
def minkowskiRecoverySet (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) : Set V :=
  {x | minkowskiRecoveryLevel ν hB n ≤ minkowskiRecoveryTest ν hB n x}

theorem measurableSet_minkowskiRecoverySet (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) :
    MeasurableSet (minkowskiRecoverySet ν hB n) :=
  (Classical.choose_spec (exists_minkowskiRecoveryLevel ν hB n)).2.1

/-- The indicator error of the `n`-th recovery set is at most `1 / (n + 1)`. -/
theorem lintegral_enorm_minkowskiRecoverySet_sub_le (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) :
    ∫⁻ x, ‖(minkowskiRecoverySet ν hB n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  have hw := recoveryWidth_pos n
  have he := (Classical.choose_spec (exists_minkowskiRecoveryLevel ν hB n)).2.2.2
  refine he.trans ?_
  calc indicatorDistance (ν : Measure V) (minkowskiRecoveryTest ν hB n) B /
        ENNReal.ofReal (recoveryWidth n)
      ≤ ENNReal.ofReal (recoveryWidth n / ((n : ℝ) + 1)) / ENNReal.ofReal (recoveryWidth n) :=
        ENNReal.div_le_div_right (indicatorDistance_recoveryTest_lt hB _ _).le _
    _ = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        rw [← ENNReal.ofReal_div_of_pos hw]
        congr 1
        field_simp

/-- The Minkowski content of the `n`-th recovery set is at most
`(perimeter + 1/(n + 1)) / (1 - 2 recoveryWidth n) + 1/(n + 1)`. -/
theorem minkowskiContent_minkowskiRecoverySet_le (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) (n : ℕ) :
    Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n) ≤
      (perimeter (ν : Measure V) B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
        ENNReal.ofReal (1 - 2 * recoveryWidth n) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  have hc := (Classical.choose_spec (exists_minkowskiRecoveryLevel ν hB n)).2.2.1
  refine hc.trans ?_
  gcongr
  exact (cost_recoveryTest_lt hB _ _).le

theorem tendsto_indicator_minkowskiRecoverySet (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    Tendsto (fun n => ∫⁻ x, ‖(minkowskiRecoverySet ν hB n).indicator (1 : V → ℝ) x -
      B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) := by
  have hup : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le)
    (lintegral_enorm_minkowskiRecoverySet_sub_le ν hB)

/-- Minkowski recovery: the contents of the recovery sets converge to the perimeter of `B`. -/
theorem tendsto_minkowskiContent_minkowskiRecoverySet (ν : Measure V) [IsFiniteMeasure ν]
    {B : Set V} (hB : perimeter (ν : Measure V) B < ⊤) :
    Tendsto (fun n => Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n)) atTop
      (𝓝 (perimeter (ν : Measure V) B)) := by
  have hη : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hnum :
    Tendsto (fun n : ℕ => perimeter (ν : Measure V) B + ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (perimeter (ν : Measure V) B)) := by
    simpa using (tendsto_const_nhds (x := perimeter (ν : Measure V) B)).add hη
  have hden : Tendsto (fun n : ℕ => ENNReal.ofReal (1 - 2 * recoveryWidth n)) atTop (𝓝 1) := by
    have h :=
      ENNReal.tendsto_ofReal
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_recoveryWidth.const_mul 2))
    simpa using h
  have hup :
    Tendsto
      (fun n : ℕ =>
        (perimeter (ν : Measure V) B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
            ENNReal.ofReal (1 - 2 * recoveryWidth n) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (perimeter (ν : Measure V) B)) := by
    have h :=
      (ENNReal.Tendsto.div hnum (Or.inr one_ne_zero) hden (Or.inl ENNReal.one_ne_top)).add hη
    simpa using h
  refine
    tendsto_of_le_liminf_of_limsup_le
      (perimeter_le_liminf_minkowskiContent ν (measurableSet_minkowskiRecoverySet ν hB)
        (tendsto_indicator_minkowskiRecoverySet ν hB))
      ?_
  calc
    limsup (fun n => Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n)) atTop ≤
        limsup
          (fun n : ℕ =>
            (perimeter (ν : Measure V) B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
                ENNReal.ofReal (1 - 2 * recoveryWidth n) +
              ENNReal.ofReal (1 / ((n : ℝ) + 1)))
          atTop :=
      limsup_le_limsup (Eventually.of_forall (minkowskiContent_minkowskiRecoverySet_le ν hB))
    _ = perimeter (ν : Measure V) B := hup.limsup_eq

/-- The perimeters of the recovery sets also converge to the perimeter of `B`. -/
theorem tendsto_perimeter_minkowskiRecoverySet (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    Tendsto (fun n => perimeter (ν : Measure V) (minkowskiRecoverySet ν hB n)) atTop
      (𝓝 (perimeter (ν : Measure V) B)) := by
  refine tendsto_of_le_liminf_of_limsup_le
    (perimeter_le_liminf_of_tendsto (ν : Measure V) (measurableSet_minkowskiRecoverySet ν hB)
      (tendsto_indicator_minkowskiRecoverySet ν hB)) ?_
  calc limsup (fun n => perimeter (ν : Measure V) (minkowskiRecoverySet ν hB n)) atTop
      ≤ limsup (fun n => Isoperimetry.minkowskiContent ν (minkowskiRecoverySet ν hB n)) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n =>
          perimeter_le_minkowskiContent ν (measurableSet_minkowskiRecoverySet ν hB n))
    _ = perimeter (ν : Measure V) B :=
        (tendsto_minkowskiContent_minkowskiRecoverySet ν hB).limsup_eq

/-- Existence form of Minkowski recovery for finite perimeter. -/
theorem exists_minkowskiRecovery (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    ∃ A : ℕ → Set V, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.minkowskiContent ν (A n)) atTop
        (𝓝 (perimeter (ν : Measure V) B)) :=
  ⟨minkowskiRecoverySet ν hB, measurableSet_minkowskiRecoverySet ν hB,
    tendsto_indicator_minkowskiRecoverySet ν hB,
    tendsto_minkowskiContent_minkowskiRecoverySet ν hB⟩

/-- At a measurable finite-mass target, global indicator L1 convergence gives eventual
finite mass of the approximating sets; therefore their lower contents bound the perimeter
in liminf for every Borel measure. A finite initial segment may have infinite mass. -/
theorem perimeter_le_liminf_minkowskiContent_of_measure_lt_top (ν : Measure V) {B : Set V}
    (hB : MeasurableSet B) (hνB : ν B < ⊤) {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv :
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) atTop
        (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => Isoperimetry.minkowskiContent ν (A n)) atTop := by
  have hfin : ∀ᶠ n in atTop, ν (A n) < ⊤ := by
    filter_upwards [hconv.eventually_lt_const (by norm_num : (0 : ℝ≥0∞) < 1)] with n hn
    exact
      (measure_le_add_lintegral_indicator_sub ν (hA n) hB).trans_lt
        (ENNReal.add_lt_top.2 ⟨hνB, hn.trans (by norm_num)⟩)
  exact
    (perimeter_le_liminf_of_tendsto ν hA hconv).trans
      (liminf_le_liminf
        (hfin.mono fun n hn => perimeter_le_minkowskiContent_of_measure_lt_top ν (hA n) hn))

/-- Quantitative positive-superlevel selection for tests under finiteness on bounded
Borel sets; the carrier need not be proper and the target need not be measurable. -/
theorem exists_superlevel_selection_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤) (f : Test V)
    (B : Set V) {δ ε : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo δ (1 - δ),
      MeasurableSet {x | t ≤ f x} ∧
        Isoperimetry.minkowskiContent ν {x | t ≤ f x} ≤
            cost ν f / ENNReal.ofReal (1 - 2 * δ) + ENNReal.ofReal ε ∧
          ∫⁻ x, ‖{x | t ≤ f x}.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
            indicatorDistance ν f B / ENNReal.ofReal δ := by
  have hab : δ < 1 - δ := by linarith
  obtain ⟨K, hK⟩ := f.lipschitz
  have hpos : Bornology.IsBounded {x | 0 < f x} :=
    f.boundedSupport.subset fun x hx => (show f x ≠ 0 from ne_of_gt hx)
  have hcoarea :
    ∫⁻ t in Set.Ioo δ (1 - δ), Isoperimetry.minkowskiContent ν {x | t ≤ f x} ≤ cost ν f :=
    (lintegral_mono' (Measure.restrict_mono (by intro t ht; exact hδ.trans ht.1) le_rfl)
          le_rfl).trans
      (Isoperimetry.setLIntegral_minkowskiContent_superlevel_le_localSlope_of_bounded_positive ν
        hν hK hpos)
  have hcfin : cost ν f ≠ ⊤ :=
    cost_ne_top_of_support_measure ν f
      (hν _ f.boundedSupport.closure isClosed_closure.measurableSet).ne
  obtain ⟨t, ht, hc⟩ := exists_mem_Ioo_le_div_add_of_setLIntegral_le hab hcfin hcoarea hε
  have hL : 1 - δ - δ = 1 - 2 * δ := by ring
  rw [hL] at hc
  exact
    ⟨t, ht, measurableSet_le measurable_const hK.continuous.measurable, hc,
      lintegral_enorm_indicator_superlevel_sub_le ν f B hδ ht.1.le ht.2.le⟩
/-- Actual lower-content recovery at a measurable finite-mass, finite-perimeter target
under finiteness on bounded Borel sets. Recovery sets are bounded measurable superlevels
with finite mass and finite lower content term by term; indicators converge in global L1
and their lower contents converge to the target perimeter. -/
theorem exists_minkowskiRecovery_of_finite_on_bounded (ν : Measure V)
    (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤) {B : Set V}
    (hBm : MeasurableSet B) (hνB : ν B < ⊤) (hB : perimeter ν B < ⊤) :
    ∃ A : ℕ → Set V,
      (∀ n, MeasurableSet (A n)) ∧
        (∀ n, Bornology.IsBounded (A n)) ∧
          (∀ n, ν (A n) < ⊤) ∧
            (∀ n, Isoperimetry.minkowskiContent ν (A n) < ⊤) ∧
              Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν)
                  atTop (𝓝 0) ∧
                Tendsto (fun n => Isoperimetry.minkowskiContent ν (A n)) atTop
                  (𝓝 (perimeter ν B)) := by
  let f : ℕ → Test V := fun n =>
    recoveryTest hB (ε := ENNReal.ofReal (recoveryWidth n / ((n : ℝ) + 1))) (η :=
      ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      (ENNReal.ofReal_pos.2 (div_pos (recoveryWidth_pos n) (by positivity)))
      (ENNReal.ofReal_pos.2 (by positivity))
  have hs := fun n =>
    exists_superlevel_selection_of_finite_on_bounded ν hν (f n) B (recoveryWidth_pos n)
      (recoveryWidth_lt_half n) (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose t ht hAm hc he using hs
  let A : ℕ → Set V := fun n => {x | t n ≤ f n x}
  have hA : ∀ n, MeasurableSet (A n) := hAm
  have hbnd : ∀ n, Bornology.IsBounded (A n) := fun n =>
    (f n).boundedSupport.subset fun x hx =>
      ne_of_gt ((recoveryWidth_pos n).trans_le ((ht n).1.le.trans hx))
  have hmass : ∀ n, ν (A n) < ⊤ := fun n => hν _ (hbnd n) (hA n)
  have herr :
    ∀ n,
      ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    refine (he n).trans ?_
    calc
      indicatorDistance ν (f n) B / ENNReal.ofReal (recoveryWidth n) ≤
          ENNReal.ofReal (recoveryWidth n / ((n : ℝ) + 1)) / ENNReal.ofReal (recoveryWidth n) :=
        ENNReal.div_le_div_right (indicatorDistance_recoveryTest_lt hB _ _).le _
      _ = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        rw [← ENNReal.ofReal_div_of_pos (recoveryWidth_pos n)]
        congr 1
        field_simp [(recoveryWidth_pos n).ne']
  have hη : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv :
    Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) atTop
      (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hη (fun _ => zero_le) herr
  have hbound :
    ∀ n,
      Isoperimetry.minkowskiContent ν (A n) ≤
        (perimeter ν B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
            ENNReal.ofReal (1 - 2 * recoveryWidth n) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    refine (hc n).trans ?_
    gcongr
    exact (cost_recoveryTest_lt hB _ _).le
  have hcontentFin : ∀ n, Isoperimetry.minkowskiContent ν (A n) < ⊤ := by
    intro n
    have hdenpos : 0 < 1 - 2 * recoveryWidth n := by linarith [recoveryWidth_lt_half n]
    exact
      (hbound n).trans_lt
        (ENNReal.add_lt_top.2
          ⟨ENNReal.div_lt_top (ENNReal.add_lt_top.2 ⟨hB, ENNReal.ofReal_lt_top⟩).ne
              (ENNReal.ofReal_pos.2 hdenpos).ne',
            ENNReal.ofReal_lt_top⟩)
  have hnum :
    Tendsto (fun n : ℕ => perimeter ν B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (perimeter ν B)) := by
    simpa using (tendsto_const_nhds (x := perimeter ν B)).add hη
  have hden : Tendsto (fun n : ℕ => ENNReal.ofReal (1 - 2 * recoveryWidth n)) atTop (𝓝 1) := by
    simpa using
      ENNReal.tendsto_ofReal
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_recoveryWidth.const_mul 2))
  have hup :
    Tendsto
      (fun n : ℕ =>
        (perimeter ν B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
            ENNReal.ofReal (1 - 2 * recoveryWidth n) +
          ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (perimeter ν B)) := by
    simpa using
      (ENNReal.Tendsto.div hnum (Or.inr one_ne_zero) hden (Or.inl ENNReal.one_ne_top)).add hη
  refine ⟨A, hA, hbnd, hmass, hcontentFin, hconv, ?_⟩
  exact
    tendsto_of_le_liminf_of_limsup_le
      (perimeter_le_liminf_minkowskiContent_of_measure_lt_top ν hBm hνB hA hconv)
      ((limsup_le_limsup (Eventually.of_forall hbound)).trans_eq hup.limsup_eq)


end MinkowskiRecovery

section RatioRecovery

/-- Symmetric quotients converge when the numerators converge and the masses converge to a value
strictly between `0` and `1`: the limiting denominator is nonzero and finite. -/
theorem tendsto_div_min_one_sub {ι : Type*} {l : Filter ι} {a m : ι → ℝ≥0∞} {a₀ m₀ : ℝ≥0∞}
    (ha : Tendsto a l (𝓝 a₀)) (hm : Tendsto m l (𝓝 m₀)) (h0 : 0 < m₀) (h1 : m₀ < 1) :
    Tendsto (fun i => a i / min (m i) (1 - m i)) l (𝓝 (a₀ / min m₀ (1 - m₀))) := by
  have hmin : Tendsto (fun i => min (m i) (1 - m i)) l (𝓝 (min m₀ (1 - m₀))) :=
    hm.min (ENNReal.Tendsto.sub tendsto_const_nhds hm (Or.inl ENNReal.one_ne_top))
  have hpos : min m₀ (1 - m₀) ≠ 0 := (lt_min h0 (tsub_pos_of_lt h1)).ne'
  have htop : min m₀ (1 - m₀) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_right _ _).trans tsub_le_self)
  exact ENNReal.Tendsto.div ha (Or.inr hpos) hmin (Or.inl htop)

variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- The masses of the Minkowski recovery sets of a measurable `B` converge to `ν B`. -/
theorem tendsto_measure_minkowskiRecoverySet (ν : ProbabilityMeasure V) {B : Set V}
    (hBm : MeasurableSet B) (hB : perimeter (ν : Measure V) B < ⊤) :
    Tendsto (fun n => (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n)) atTop
      (𝓝 ((ν : Measure V) B)) :=
  tendsto_measure_of_tendsto_indicator (ν : Measure V)
    (measurableSet_minkowskiRecoverySet (ν : Measure V) hB) hBm
    (tendsto_indicator_minkowskiRecoverySet (ν : Measure V) hB)

/-- For `0 < ν B < 1`, the recovery sets eventually have mass strictly between `0` and `1`. -/
theorem eventually_measure_minkowskiRecoverySet_mem_Ioo (ν : ProbabilityMeasure V) {B : Set V}
    (hBm : MeasurableSet B) (hB : perimeter (ν : Measure V) B < ⊤) (h0 : 0 < (ν : Measure V) B)
    (h1 : (ν : Measure V) B < 1) :
    ∀ᶠ n in atTop, (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) ∈ Set.Ioo 0 1 :=
  (tendsto_measure_minkowskiRecoverySet ν hBm hB).eventually (Ioo_mem_nhds h0 h1)

/-- Symmetric Minkowski quotients of the recovery sets converge to the symmetric BV quotient of
`B`, for measurable `B` of finite perimeter with `0 < ν B < 1`. -/
theorem tendsto_minkowskiContent_div_min_minkowskiRecoverySet (ν : ProbabilityMeasure V)
    {B : Set V} (hBm : MeasurableSet B) (hB : perimeter (ν : Measure V) B < ⊤)
    (h0 : 0 < (ν : Measure V) B) (h1 : (ν : Measure V) B < 1) :
    Tendsto
      (fun n =>
        Isoperimetry.minkowskiContent (ν : Measure V)
            (minkowskiRecoverySet (ν : Measure V) hB n) /
          min ((ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))
            (1 - (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n)))
      atTop
      (𝓝 (perimeter (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B))) :=
  tendsto_div_min_one_sub (tendsto_minkowskiContent_minkowskiRecoverySet (ν : Measure V) hB)
    (tendsto_measure_minkowskiRecoverySet ν hBm hB) h0 h1

/-- Symmetric BV quotients of the recovery sets converge to that of `B`. -/
theorem tendsto_perimeter_div_min_minkowskiRecoverySet (ν : ProbabilityMeasure V)
    {B : Set V} (hBm : MeasurableSet B) (hB : perimeter (ν : Measure V) B < ⊤)
    (h0 : 0 < (ν : Measure V) B) (h1 : (ν : Measure V) B < 1) :
    Tendsto (fun n => perimeter (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n) /
        min ((ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))
          (1 - (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))) atTop
      (𝓝 (perimeter (ν : Measure V) B / min ((ν : Measure V) B) (1 - (ν : Measure V) B))) :=
  tendsto_div_min_one_sub (tendsto_perimeter_minkowskiRecoverySet (ν : Measure V) hB)
    (tendsto_measure_minkowskiRecoverySet ν hBm hB) h0 h1

end RatioRecovery

end FunctionalInequalities.KLS.MetricBV
