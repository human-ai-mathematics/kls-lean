import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiContent
import FunctionalInequalities.Energy.LocalSlope.Basic

/-!
# Minkowski coarea inequality with the local slope

For a probability law `ν` on a normed group and a globally Lipschitz `u`, with no
differentiability assumption,
`∫ ν⁺({u ≥ t}) dt ≤ ∫ |∇u|(x) dν(x)` where `|∇u|` is the pointwise local metric slope
`Energy.LocalSlope.apply` (`lintegral_minkowskiContent_superlevel_le_localSlope`).

The layer-cake part repeats the proof of the `C¹` theorem `lintegral_minkowskiContent_superlevel_le`
(near-neighbour witness, measurable strips, Tonelli, Fatou and reverse Fatou under the uniform
Lipschitz bound) as a bound by the integrated limsup of the growth quotients
`(ballSup u r x - u x) / r` (`lintegral_minkowskiContent_superlevel_le_limsup`). The derivative
bound is replaced by the proved growth-quotient bound `limsup_ofReal_ballSup_le_localSlope`, which
holds for every function. The `C¹` statement, `minkowskiContent` and the `ballSup` API are
unchanged. This is not a pointwise comparison of Minkowski content with a perimeter.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.KLS.Isoperimetry

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

/-- Layer cake for a globally Lipschitz function (no differentiability): the superlevel-content
integral is at most the integrated limsup of the growth quotients at the radii `1 / (n + 1)`.
The proof is that of `lintegral_minkowskiContent_superlevel_le`, stopped before the pointwise
derivative bound. -/
theorem lintegral_minkowskiContent_superlevel_le_limsup (ν : ProbabilityMeasure V) {u : V → ℝ}
    {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, limsup (fun n : ℕ => ENNReal.ofReal
        ((ballSup u (1 / ((n : ℝ) + 1)) x - u x) / (1 / ((n : ℝ) + 1)))) atTop
        ∂(ν : Measure V) := by
  classical
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simpa [hrdef] using one_div_pos.mpr this
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrW : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hr0
      (Eventually.of_forall hrpos)
  have humeas : Measurable u := hK.continuous.measurable
  have hbmeas : ∀ n, Measurable (ballSup u (r n)) := fun n =>
    (lipschitzWith_ballSup hK (hrpos n).le).continuous.measurable
  set T : ℕ → Set (ℝ × V) := fun n => {p | u p.2 < p.1 ∧ p.1 ≤ ballSup u (r n) p.2} with hTdef
  have hTmeas : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_lt (humeas.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst ((hbmeas n).comp measurable_snd))
  set S : ℕ → ℝ → Set V := fun n t => {x | u x < t ∧ t ≤ ballSup u (r n) x} with hSdef
  set G : ℕ → ℝ → ℝ≥0∞ := fun n t => (ν : Measure V) (S n t) / ENNReal.ofReal (r n) with hGdef
  have hmeasfun : ∀ n, Measurable fun t : ℝ => (ν : Measure V) (S n t) := fun n =>
    measurable_measure_prodMk_left (ν := (ν : Measure V)) (hTmeas n)
  have hGmeas : ∀ n, Measurable (G n) := by
    intro n
    simpa [hGdef, div_eq_mul_inv] using
      (hmeasfun n).mul_const ((ENNReal.ofReal (r n))⁻¹)
  -- Step 1: the near-neighbour witness bounds the content by a measurable strip quotient.
  have step1 : ∀ t : ℝ, minkowskiContent ν {x | t ≤ u x} ≤ liminf (fun n => G n t) atTop := by
    intro t
    have h1 : minkowskiContent ν {x | t ≤ u x} ≤
        liminf (fun n => ((ν : Measure V) (Metric.thickening (r n) {x | t ≤ u x}) -
          (ν : Measure V) {x | t ≤ u x}) / ENNReal.ofReal (r n)) atTop := by
      have hcomp := hrW.liminf_le_liminf_comp (u := fun s : ℝ =>
        ((ν : Measure V) (Metric.thickening s {x | t ≤ u x}) -
          (ν : Measure V) {x | t ≤ u x}) / ENNReal.ofReal s)
      simpa [minkowskiContent, Function.comp_def] using hcomp
    refine h1.trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
    refine ENNReal.div_le_div_right (tsub_le_iff_right.mpr ?_) _
    calc (ν : Measure V) (Metric.thickening (r n) {x | t ≤ u x})
        ≤ (ν : Measure V) (S n t ∪ {x | t ≤ u x}) :=
          measure_mono (thickening_superlevel_subset hK (r n) t)
      _ ≤ (ν : Measure V) (S n t) + (ν : Measure V) {x | t ≤ u x} := measure_union_le _ _
  -- Step 2: Tonelli turns the strip integral into the growth quotient.
  have step2 : ∀ n, ∫⁻ t, G n t ∂(volume : Measure ℝ) =
      ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) ∂(ν : Measure V) := by
    intro n
    have hrne : ENNReal.ofReal (r n) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hrpos n]
    have hinvne : (ENNReal.ofReal (r n))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hrne
    have hsec : ∀ x : V, (fun t : ℝ => (t, x)) ⁻¹' T n = Set.Ioc (u x) (ballSup u (r n) x) := by
      intro x
      ext t
      simp [hTdef, Set.mem_Ioc]
    calc ∫⁻ t, G n t ∂(volume : Measure ℝ)
        = ∫⁻ t, (ν : Measure V) (Prod.mk t ⁻¹' T n) * (ENNReal.ofReal (r n))⁻¹
            ∂(volume : Measure ℝ) := by
          simp [hGdef, hTdef, hSdef, div_eq_mul_inv]
      _ = (∫⁻ t, (ν : Measure V) (Prod.mk t ⁻¹' T n) ∂(volume : Measure ℝ)) *
            (ENNReal.ofReal (r n))⁻¹ := lintegral_mul_const' _ _ hinvne
      _ = ((volume : Measure ℝ).prod (ν : Measure V)) (T n) * (ENNReal.ofReal (r n))⁻¹ := by
          rw [Measure.prod_apply (hTmeas n)]
      _ = (∫⁻ x, (volume : Measure ℝ) ((fun t : ℝ => (t, x)) ⁻¹' T n) ∂(ν : Measure V)) *
            (ENNReal.ofReal (r n))⁻¹ := by rw [Measure.prod_apply_symm (hTmeas n)]
      _ = (∫⁻ x, ENNReal.ofReal (ballSup u (r n) x - u x) ∂(ν : Measure V)) *
            (ENNReal.ofReal (r n))⁻¹ := by
          congr 1
          refine lintegral_congr fun x => ?_
          rw [hsec x, Real.volume_Ioc]
      _ = ∫⁻ x, ENNReal.ofReal (ballSup u (r n) x - u x) * (ENNReal.ofReal (r n))⁻¹
            ∂(ν : Measure V) := (lintegral_mul_const' _ _ hinvne).symm
      _ = ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) ∂(ν : Measure V) := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_div_of_pos (hrpos n), div_eq_mul_inv]
  -- Step 3: the growth quotients are uniformly bounded by the Lipschitz constant.
  have hqmeas : ∀ n, Measurable fun x : V => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) :=
    fun n => (((hbmeas n).sub humeas).div_const _).ennreal_ofReal
  have hqbound : ∀ n, ∀ x : V,
      ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) ≤ ENNReal.ofReal (K : ℝ) := by
    intro n x
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (hrpos n)]
    linarith [ballSup_le_add hK (hrpos n).le x]
  have hgfin : ∫⁻ _ : V, ENNReal.ofReal (K : ℝ) ∂(ν : Measure V) ≠ ⊤ := by
    simp [lintegral_const, measure_univ]
  calc ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ)
      ≤ ∫⁻ t, liminf (fun n => G n t) atTop ∂(volume : Measure ℝ) := lintegral_mono step1
    _ ≤ liminf (fun n => ∫⁻ t, G n t ∂(volume : Measure ℝ)) atTop := lintegral_liminf_le hGmeas
    _ = liminf (fun n => ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)
          ∂(ν : Measure V)) atTop := by simp only [step2]
    _ ≤ limsup (fun n => ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)
          ∂(ν : Measure V)) atTop := liminf_le_limsup
    _ ≤ ∫⁻ x, limsup (fun n => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)) atTop
          ∂(ν : Measure V) :=
        limsup_lintegral_le _ hqmeas (fun n => Eventually.of_forall (hqbound n)) hgfin

/-- Minkowski coarea inequality with the local slope, for every globally Lipschitz function
(no differentiability, bounded values or bounded support) and every probability law on a normed
group: `∫ ν⁺({u ≥ t}) dt ≤ ∫ |∇u| dν`. -/
theorem lintegral_minkowskiContent_superlevel_le_localSlope (ν : ProbabilityMeasure V)
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, Energy.LocalSlope.apply u x ∂(ν : Measure V) :=
  (lintegral_minkowskiContent_superlevel_le_limsup ν hK).trans
    (lintegral_mono fun x => limsup_ofReal_ballSup_le_localSlope u x
      (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat)

end FunctionalInequalities.KLS.Isoperimetry
