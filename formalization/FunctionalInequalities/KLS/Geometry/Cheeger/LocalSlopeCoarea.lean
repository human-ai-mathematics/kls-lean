module

public import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiContent
public import FunctionalInequalities.Energy.LocalSlope.Basic

/-!
# Minkowski coarea inequality with the local slope

For a finite Borel measure `ν` on a metric space and a globally Lipschitz `u`,
with no differentiability assumption,
`∫ ν⁺({u ≥ t}) dt ≤ ∫ |∇u|(x) dν(x)` where `|∇u|` is the pointwise local metric slope
`Energy.LocalSlope.apply` (`lintegral_minkowskiContent_superlevel_le_localSlope`; generic metric
scope since 2026-09-30, the local-slope form of Lemma 3.2 of Ambrosio--Di Marino--Gigli for
finite measures; probability laws are instances). The direct content/slope upper bound now
also holds for positive levels when some positive-support neighborhood has finite mass,
and for all levels of a nonnegative Lipschitz function under that same premise. The original
measure may have infinite total mass. The full Lemma 3.2 chain is also proved: the positive
superlevel-content integral is bounded by the actual right-radius liminf of integrated
open-ball growth, which is bounded by the original local-slope integral. The finite-support
neighborhood controls growth outside it; no integrability of the function is assumed.

Generic route (section `Generic`, `[MetricSpace V]`).  The layer cake
`lintegral_minkowskiContent_superlevel_le_limsup_of_majorant` takes an abstract measurable majorant
family `w n` carrying the near-neighbour witness at radii `r n → 0` and exceeding `u` by at most
`K · r n` (measurable strips, Tonelli, Fatou and reverse Fatou under the uniform Lipschitz bound).
On an arbitrary metric space the majorant is the open-ball supremum `openBallSup` (ADMG (3.1)),
which is lower semicontinuous, hence Borel, on every metric space
(`lintegral_minkowskiContent_superlevel_le_limsup_openBallSup`); the growth-quotient bound
`limsup_ofReal_openBallSup_le_localSlope` holds for every function since points of the open ball
are at distance less than `r`.

Retained closed-ball statements (section `ClosedBall`, `[NormedAddCommGroup V]`).  The closed-ball
supremum `ballSup` is measurable only through its translation-based Lipschitz property
`lipschitzWith_ballSup`, and it need not be continuous on a general metric space; so
`limsup_ofReal_ballSup_le_localSlope` and the closed-ball layer cake
`lintegral_minkowskiContent_superlevel_le_limsup` keep their original normed scope with unchanged
statements, the latter now an instance of the majorant lemma.  The `C¹` theorem
`lintegral_minkowskiContent_superlevel_le` in `MinkowskiContent.lean` also specializes the
generic measurable-majorant theorem.  This is not a
pointwise comparison of Minkowski content with a perimeter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.KLS.Isoperimetry

section Generic

variable {V : Type*} [MetricSpace V]

/-- Along positive radii tending to zero, the limsup of the normalized local growth
`(openBallSup u r x - u x) / r` is at most the local slope of `u` at `x`, on every metric space and
for every function: a point of the open `r`-ball above the centre value is at positive distance
less than `r`, so its growth over `r` is at most its secant slope. -/
theorem limsup_ofReal_openBallSup_le_localSlope (u : V → ℝ) (x : V) {r : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    limsup (fun n => ENNReal.ofReal ((openBallSup u (r n) x - u x) / r n)) atTop
      ≤ Energy.LocalSlope.apply u x := by
  unfold Energy.LocalSlope.apply
  refine le_iInf₂ fun ρ hρ => ?_
  refine limsup_le_of_le isCobounded_le_of_bot ?_
  filter_upwards [hr0.eventually_lt_const hρ] with n hn
  set S : ℝ≥0∞ := ⨆ (y : V) (_ : dist y x < ρ), ENNReal.ofReal (dist (u y) (u x) / dist y x)
    with hS
  rcases eq_or_ne S ⊤ with htop | htop
  · rw [htop]
    exact le_top
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
  have hsup : openBallSup u (r n) x ≤ u x + S.toReal * r n := by
    refine csSup_le ⟨u x, x, Metric.mem_ball_self (hrpos n), rfl⟩ ?_
    rintro a ⟨y, hy, rfl⟩
    have hyx : dist y x < r n := Metric.mem_ball.1 hy
    rcases le_or_gt (u y) (u x) with hle | hlt
    · nlinarith [hrpos n]
    · have hpos : 0 < dist y x := dist_pos.2 fun hxy => by
        rw [hxy] at hlt
        exact lt_irrefl _ hlt
      have hq : ENNReal.ofReal (dist (u y) (u x) / dist y x) ≤ S :=
        le_iSup₂ (f := fun (y : V) (_ : dist y x < ρ) =>
          ENNReal.ofReal (dist (u y) (u x) / dist y x)) y (hyx.trans hn)
      have hq' := (ENNReal.ofReal_le_iff_le_toReal htop).1 hq
      rw [div_le_iff₀ hpos, Real.dist_eq, abs_of_pos (sub_pos.2 hlt)] at hq'
      nlinarith
  rw [div_le_iff₀ (hrpos n)]
  linarith

variable [MeasurableSpace V] [BorelSpace V]

/-- Layer cake with the open-ball majorant at the radii `1 / (n + 1)`, on every metric space. -/
theorem lintegral_minkowskiContent_superlevel_le_limsup_openBallSup (ν : Measure V)
    [IsFiniteMeasure ν] {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x,
        limsup
          (fun n : ℕ =>
            ENNReal.ofReal ((openBallSup u (1 / ((n : ℝ) + 1)) x - u x) / (1 / ((n : ℝ) + 1))))
          atTop ∂(ν : Measure V) :=
  lintegral_minkowskiContent_superlevel_le_limsup_of_majorant ν hK (r := fun n : ℕ =>
    1 / ((n : ℝ) + 1)) (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => measurable_openBallSup hK (by positivity))
    (fun n t => thickening_superlevel_subset_openBallSup hK _ t)
    (fun n x => openBallSup_le_add hK (by positivity) x)

/-- Minkowski coarea inequality with the local slope, for every globally Lipschitz function
(no differentiability, bounded values or bounded support) and every finite Borel measure on a metric
space: `∫ ν⁺({u ≥ t}) dt ≤ ∫ |∇u| dν`. -/
theorem lintegral_minkowskiContent_superlevel_le_localSlope (ν : Measure V) [IsFiniteMeasure ν]
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂(ν : Measure V) :=
  (lintegral_minkowskiContent_superlevel_le_limsup_openBallSup ν hK).trans
    (lintegral_mono fun x => limsup_ofReal_openBallSup_le_localSlope u x
      (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat)

/-- The actual right-radius liminf of integrated open-ball growth bounds the superlevel
content integral. A sequence attaining that liminf is used only to prove the radius-filter
statement; no sequence-specific replacement is made in the conclusion. -/
theorem lintegral_minkowskiContent_superlevel_le_liminf_openBallSup (ν : Measure V)
    [IsFiniteMeasure ν] {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) := by
  let H : ℝ → ℝ≥0∞ := fun r => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν
  obtain ⟨r, hq, hr⟩ := exists_seq_tendsto_liminf (u := H) (f := 𝓝[>] (0 : ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.eventually self_mem_nhdsWithin)
  have hrpos : ∀ n : ℕ, 0 < r (n + N) := fun n => hN (n + N) (Nat.le_add_left N n)
  have hr0 : Tendsto (fun n => r (n + N)) atTop (𝓝 (0 : ℝ)) :=
    (hr.comp (tendsto_add_atTop_nat N)).mono_right nhdsWithin_le_nhds
  have hl :=
    lintegral_minkowskiContent_superlevel_le_liminf_of_majorant ν hK hrpos hr0
      (fun n => measurable_openBallSup hK (hrpos n))
      (fun n t => thickening_superlevel_subset_openBallSup hK (r (n + N)) t)
  have hqt : Tendsto (fun n => H (r (n + N))) atTop (𝓝 (liminf H (𝓝[>] 0))) :=
    hq.comp (tendsto_add_atTop_nat N)
  exact hl.trans_eq hqt.liminf_eq

/-- Dominated reverse Fatou bounds the right-radius liminf of integrated open-ball
growth by the actual local-slope integral for a finite Borel measure. -/
theorem liminf_lintegral_openBallSup_le_localSlope (ν : Measure V) [IsFiniteMeasure ν]
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂ν := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hrpos : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrW : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hr0 (Eventually.of_forall hrpos)
  have hc :=
    hrW.liminf_le_liminf_comp (u := fun r : ℝ =>
      ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν)
  have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal ((openBallSup u (r n) x - u x) / r n) :=
    fun n =>
    (((measurable_openBallSup hK (hrpos n)).sub hK.continuous.measurable).div_const
        _).ennreal_ofReal
  have hbound :
    ∀ n x, ENNReal.ofReal ((openBallSup u (r n) x - u x) / r n) ≤ ENNReal.ofReal (K : ℝ) := by
    intro n x
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (hrpos n)]
    linarith [openBallSup_le_add hK (hrpos n) x]
  have hgfin : ∫⁻ _ : V, ENNReal.ofReal (K : ℝ) ∂ν ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  refine hc.trans (le_trans liminf_le_limsup ?_)
  exact
    (limsup_lintegral_le _ hmeas (fun n => Eventually.of_forall (hbound n)) hgfin).trans
      (lintegral_mono fun x => limsup_ofReal_openBallSup_le_localSlope u x hrpos hr0)
omit [BorelSpace V] in
private theorem lintegral_openBallSup_growth_restrict_eq (ν : Measure V) {u : V → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) (hu : ∀ x, 0 ≤ u x) {δ r : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) (hrδ : r ≤ δ) :
    (∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r)
      ∂(ν.restrict (thickening δ {x | 0 < u x}))) =
      ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν := by
  apply setLIntegral_eq_of_support_subset
  intro x hx
  by_contra hnot
  have hxpos : ¬0 < u x := fun hp => hnot (self_subset_thickening hδ _ hp)
  have hxzero : u x = 0 := le_antisymm (not_lt.mp hxpos) (hu x)
  have hyzero : ∀ y ∈ ball x r, u y ≤ 0 := by
    intro y hy
    apply not_lt.mp
    intro hp
    apply hnot
    apply Metric.mem_thickening_iff.2
    exact ⟨y, hp, by simpa [dist_comm] using (Metric.mem_ball.1 hy).trans_le hrδ⟩
  have hsle : openBallSup u r x ≤ 0 :=
    csSup_le ⟨u x, x, Metric.mem_ball_self hr, rfl⟩ (by
      rintro a ⟨y, hy, rfl⟩
      exact hyzero y hy)
  have hszero : openBallSup u r x = 0 :=
    le_antisymm hsle (hxzero ▸ le_openBallSup hK hr x)
  exact hx (by simp [hxzero, hszero])

/-- Full ADMG Lemma 3.2: positive-superlevel content integral is at most the actual
right-radius liminf of integrated open-ball growth, which is at most the local-slope
integral. The function is nonnegative and Lipschitz, and some positive-support
neighborhood has finite mass. The original measure may have infinite total mass;
no properness, sigma-finiteness or integrability of the function is assumed. -/
theorem setLIntegral_minkowskiContent_superlevel_coarea_of_finite_neighborhood (ν : Measure V)
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) (hu : ∀ x, 0 ≤ u x) {δ : ℝ} (hδ : 0 < δ)
    (hfin : ν (thickening δ {x | 0 < u x}) < ⊤) :
    (∫⁻ t in Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
        liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν)
          (𝓝[>] 0)) ∧
      (liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) ≤
        ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂ν) := by
  let U := thickening δ {x | 0 < u x}
  have hU : MeasurableSet U := Metric.isOpen_thickening.measurableSet
  have : IsFiniteMeasure (ν.restrict U) := ⟨by simpa [Measure.restrict_apply_univ] using hfin⟩
  have he :
    ∀ t ∈ Ioi (0 : ℝ),
      minkowskiContent ν {x | t ≤ u x} = minkowskiContent (ν.restrict U) {x | t ≤ u x} := by
    intro t ht
    have hsub : {x | t ≤ u x} ⊆ {x | 0 < u x} := by
      intro x hx
      exact (show 0 < t from ht).trans_le hx
    exact
      (minkowskiContent_restrict_of_thickening_subset ν hU hδ
          (thickening_subset_of_subset δ hsub)).symm
  have hi :
    liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂(ν.restrict U))
        (𝓝[>] 0) =
      liminf (fun r : ℝ => ∫⁻ x, ENNReal.ofReal ((openBallSup u r x - u x) / r) ∂ν) (𝓝[>] 0) := by
    apply liminf_congr
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    exact lintegral_openBallSup_growth_restrict_eq ν hK hu hδ hr.1 hr.2.le
  constructor
  · calc
      ∫⁻ t in Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) =
          ∫⁻ t in Ioi (0 : ℝ),
            minkowskiContent (ν.restrict U) {x | t ≤ u x} ∂(volume : Measure ℝ) :=
        setLIntegral_congr_fun measurableSet_Ioi he
      _ ≤ ∫⁻ t, minkowskiContent (ν.restrict U) {x | t ≤ u x} ∂(volume : Measure ℝ) :=
        setLIntegral_le_lintegral _ _
      _ ≤ _ :=
        (lintegral_minkowskiContent_superlevel_le_liminf_openBallSup (ν.restrict U) hK).trans_eq
          hi
  · rw [← hi]
    exact
      (liminf_lintegral_openBallSup_le_localSlope (ν.restrict U) hK).trans
        (setLIntegral_le_lintegral _ _)

/-- Positive-superlevel coarea when a positive-support neighborhood has finite measure.
The original measure need not be finite or sigma-finite, and the carrier need not be proper. -/
theorem setLIntegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood
    (ν : Measure V) {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) {δ : ℝ} (hδ : 0 < δ)
    (hfin : ν (Metric.thickening δ {x | 0 < u x}) < ⊤) :
    ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂ν := by
  let U := Metric.thickening δ {x | 0 < u x}
  have hU : MeasurableSet U := Metric.isOpen_thickening.measurableSet
  have : IsFiniteMeasure (ν.restrict U) := ⟨by simpa [Measure.restrict_apply_univ] using hfin⟩
  have he :
    ∀ t ∈ Set.Ioi (0 : ℝ),
      minkowskiContent ν {x | t ≤ u x} = minkowskiContent (ν.restrict U) {x | t ≤ u x} := by
    intro t ht
    have htS : {x | t ≤ u x} ⊆ {x | 0 < u x} := by
      intro x hx
      exact (show 0 < t from ht).trans_le hx
    have htU : Metric.thickening δ {x | t ≤ u x} ⊆ U := Metric.thickening_subset_of_subset δ htS
    exact (minkowskiContent_restrict_of_thickening_subset ν hU hδ htU).symm
  calc
    ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          minkowskiContent (ν.restrict U) {x | t ≤ u x} ∂(volume : Measure ℝ) :=
      setLIntegral_congr_fun measurableSet_Ioi he
    _ ≤ ∫⁻ t, minkowskiContent (ν.restrict U) {x | t ≤ u x} ∂(volume : Measure ℝ) :=
      setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂(ν.restrict U) :=
      lintegral_minkowskiContent_superlevel_le_localSlope _ hK
    _ ≤ _ := setLIntegral_le_lintegral _ _
/-- The local-slope upper bound in ADMG Lemma 3.2 for nonnegative Lipschitz functions
with finite mass of a positive-support neighborhood, as a consequence of the full
right-radius-liminf chain. Nonpositive superlevels have zero content. -/
theorem lintegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood
    (ν : Measure V) {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) (hu : ∀ x, 0 ≤ u x) {δ : ℝ}
    (hδ : 0 < δ) (hfin : ν (Metric.thickening δ {x | 0 < u x}) < ⊤) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂ν := by
  have he :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) =
      ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      have hs : {x | t ≤ u x} = Set.univ :=
        Set.eq_univ_of_forall fun x => (not_lt.mp ht).trans (hu x)
      rw [hs, minkowskiContent_univ]
  rw [he]
  have hc :=
    setLIntegral_minkowskiContent_superlevel_coarea_of_finite_neighborhood ν hK hu hδ hfin
  exact hc.1.trans hc.2

/-- Finiteness on bounded Borel sets supplies the finite-neighborhood premise for a
Lipschitz function with bounded positive support on an arbitrary metric space. -/
theorem setLIntegral_minkowskiContent_superlevel_le_localSlope_of_bounded_positive
    (ν : Measure V) (hν : ∀ s : Set V, Bornology.IsBounded s → MeasurableSet s → ν s < ⊤)
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) (hu : Bornology.IsBounded {x | 0 < u x}) :
    ∫⁻ t in Set.Ioi (0 : ℝ), minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, FunctionalInequalities.Energy.LocalSlope.apply u x ∂ν :=
  setLIntegral_minkowskiContent_superlevel_le_localSlope_of_finite_neighborhood ν hK zero_lt_one
    (hν _ hu.thickening Metric.isOpen_thickening.measurableSet)


end Generic

/-! ### Closed-ball statements (normed scope, unchanged signatures) -/

section ClosedBall

variable {V : Type*} [NormedAddCommGroup V]

/-- Along positive radii tending to zero, the limsup of the normalized local growth
`(ballSup u r x - u x) / r` is at most the local slope of `u` at `x`. No regularity of `u` is
needed: a point of the closed `r`-ball above the centre value is at positive distance at most `r`,
so its growth over `r` is at most its secant slope. -/
theorem limsup_ofReal_ballSup_le_localSlope (u : V → ℝ) (x : V) {r : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    limsup (fun n => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)) atTop
      ≤ Energy.LocalSlope.apply u x := by
  unfold Energy.LocalSlope.apply
  refine le_iInf₂ fun ρ hρ => ?_
  refine limsup_le_of_le isCobounded_le_of_bot ?_
  filter_upwards [hr0.eventually_lt_const hρ] with n hn
  set S : ℝ≥0∞ := ⨆ (y : V) (_ : dist y x < ρ), ENNReal.ofReal (dist (u y) (u x) / dist y x)
    with hS
  rcases eq_or_ne S ⊤ with htop | htop
  · rw [htop]
    exact le_top
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
  have hsup : ballSup u (r n) x ≤ u x + S.toReal * r n := by
    refine csSup_le ⟨u x, x, Metric.mem_closedBall_self (hrpos n).le, rfl⟩ ?_
    rintro a ⟨y, hy, rfl⟩
    have hyx : dist y x ≤ r n := by simpa [Metric.mem_closedBall] using hy
    rcases le_or_gt (u y) (u x) with hle | hlt
    · nlinarith [hrpos n]
    · have hpos : 0 < dist y x := dist_pos.2 fun hxy => by
        rw [hxy] at hlt
        exact lt_irrefl _ hlt
      have hq : ENNReal.ofReal (dist (u y) (u x) / dist y x) ≤ S :=
        le_iSup₂ (f := fun (y : V) (_ : dist y x < ρ) =>
          ENNReal.ofReal (dist (u y) (u x) / dist y x)) y (hyx.trans_lt hn)
      have hq' := (ENNReal.ofReal_le_iff_le_toReal htop).1 hq
      rw [div_le_iff₀ hpos, Real.dist_eq, abs_of_pos (sub_pos.2 hlt)] at hq'
      nlinarith
  rw [div_le_iff₀ (hrpos n)]
  linarith

variable [MeasurableSpace V] [BorelSpace V]

/--
Layer cake with the closed-ball majorant at the radii `1 / (n + 1)` (normed scope, as before):
an instance of the majorant lemma, the closed-ball supremum being measurable through its
translation-based Lipschitz property. -/
theorem lintegral_minkowskiContent_superlevel_le_limsup (ν : Measure V) [IsFiniteMeasure ν]
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x,
        limsup
          (fun n : ℕ =>
            ENNReal.ofReal ((ballSup u (1 / ((n : ℝ) + 1)) x - u x) / (1 / ((n : ℝ) + 1))))
          atTop ∂(ν : Measure V) :=
  lintegral_minkowskiContent_superlevel_le_limsup_of_majorant ν hK (r := fun n : ℕ =>
    1 / ((n : ℝ) + 1)) (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n =>
      (lipschitzWith_ballSup hK
          (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))).continuous.measurable)
    (fun n t => thickening_superlevel_subset hK _ t)
    (fun n x => ballSup_le_add hK (by positivity) x)

end ClosedBall

end FunctionalInequalities.KLS.Isoperimetry
