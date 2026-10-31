module

public import FunctionalInequalities.Probability.BrunnMinkowski
public import FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import FunctionalInequalities.Analysis.Convex.Coercivity
public import FunctionalInequalities.Analysis.Convex.Subgradient.Measure
public import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Measurable
public import FunctionalInequalities.Probability.ExponentialMoments.Norm
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Maximality of a finite moment potential

Let `ψ` be a finite convex function on a finite-dimensional real inner-product space `E` with
`∫ e^{-ψ} = 1`, whose gradient pushes `e^{-ψ(x)} dx` forward to `μ`. This module proves the
maximality inequality behind the uniqueness half of Cordero-Erausquin–Klartag, *Moment measures*
(arXiv:1304.0630v1), Theorem 2 (their Theorem 8, here for finite potentials):

* `lintegral_le_exp_integral_of_map_gradient`: if a measurable `g ≥ 0` satisfies, for almost every
  `w`, `g(y) ≤ exp(h(∇ψ(w)) − ψ(w) − ⟪∇ψ(w), y − w⟫)` for all `y`, where `exp(s|h|)` is
  `μ`-integrable for some `s > 0`, then `∫ g ≤ exp(∫ h dμ)`. For `g = e^{-χ}` the hypothesis says
  `χ* ≤ ψ* + h` on the gradient image, and the conclusion is `log ∫ e^{-χ} ≤ ∫ (χ* − ψ*) dμ`
  (that is, `ψ*` maximizes the functional `I_μ` of CEK Proposition 12 against `χ*`). The proof
  applies the Prékopa–Leindler inequality to `e^{-ψ}`, `g` and `e^{-ψ + t h(∇ψ)}`, then
  differentiates at `t = 0`.

Supporting facts: linear growth `c ‖x‖ + b ≤ ψ x` of a convex `ψ` with integrable `e^{-ψ}`
(`exists_linear_lower_bound_of_integrable_exp_neg`), the a.e. gradient bound `‖∇ψ‖ ≤ R` when `μ` is
carried by the closed ball of radius `R`
(`ae_norm_gradient_le`), the Fenchel equality `ψ*(∇ψ(w)) = ⟪w, ∇ψ(w)⟫ − ψ(w)` at differentiability
points (`legendre_gradient`), `μ`-a.e. finiteness of `ψ*` (`ae_legendre_ne_top`) and the
exponential integrability of `|ψ*|` under `μ` for a bounded-support `μ`
(`exists_integrable_exp_mul_abs_legendre`).

## Integrable perturbations

Here no assumption is made on the support of `μ`. This part removes the exponential-integrability
hypothesis from the maximality inequality `lintegral_le_exp_integral_of_map_gradient`
(Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1, Theorem 8, for finite potentials):

* `lintegral_le_exp_integral_of_map_gradient_of_integrable`: if `h` is `μ`-integrable and a
  measurable `g ≥ 0` satisfies, for almost every `w`,
  `g(y) ≤ exp(h(∇ψ(w)) − ψ(w) − ⟪∇ψ(w), y − w⟫)` for all `y`, then `∫ g ≤ exp(∫ h dμ)`. For
  `g = e^{-χ}` this is CEK (18): `log ∫ e^{-χ} ≤ ∫ (χ* − ψ*) dμ`. Proof: the truncations
  `max (min h k) (−k)` are bounded, and `min (g, e^{k − ψ})` is dominated through them because
  `ψ` lies above its tangent planes; let `k → ∞` (monotone and dominated convergence).
* `integrable_of_map_gradient_of_le`: under the same domination with `h` bounded above and
  `∫ g > 0`, `h` is automatically `μ`-integrable.
* `integrable_legendre_toReal`: the conjugate `ψ*` is `μ`-integrable (CEK Proposition 7, for
  finite potentials); it is bounded below by `−ψ(0)`, and the domination with `g(y) = e^{-ψ(2y)/2}`
  and `h = −ψ*/2` bounds it above.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation (measurable_gradient)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Growth

/-- **Linear growth** of a convex potential `ψ` on a finite-dimensional real inner-product space
with `e^{-ψ}` integrable for an additive Haar measure: `c ‖x‖ + b ≤ ψ x` for some `c > 0`. -/
theorem exists_linear_lower_bound_of_integrable_exp_neg (m : Measure E) [m.IsAddHaarMeasure]
    {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ) (hint : Integrable (fun x => Real.exp (-ψ x)) m) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ, ∀ x, c * ‖x‖ + b ≤ ψ x := by
  obtain ⟨⟨a, ha⟩, hcpt⟩ :=
    exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg m hψ hint
  obtain ⟨r, hr⟩ := (hcpt (ψ a + 1)).isBounded.subset_closedBall a
  set R := max r 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hclaim : ∀ x, ψ a + ‖x - a‖ / (2 * R) - 1 ≤ ψ x := by
    intro x
    by_cases hx : ‖x - a‖ ≤ 2 * R
    · have : ‖x - a‖ / (2 * R) ≤ 1 := (div_le_one (by positivity)).mpr hx
      linarith [ha x]
    · replace hx : 2 * R < ‖x - a‖ := not_le.mp hx
      set d := ‖x - a‖ with hd
      have hd0 : 0 < d := lt_trans (by positivity) hx
      set s := 2 * R / d with hs
      have hs0 : 0 < s := by positivity
      have hs1 : s ≤ 1 := (div_le_one hd0).mpr hx.le
      set z := (1 - s) • a + s • x with hz
      have hza : z - a = s • (x - a) := by rw [hz]; module
      have hzn : ‖z - a‖ = 2 * R := by
        rw [hza, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hs, ← hd]
        field_simp
      have hzout : ψ a + 1 < ψ z := by
        by_contra hle
        replace hle : ψ z ≤ ψ a + 1 := not_lt.mp hle
        have hmem := hr (show z ∈ {y | ψ y ≤ ψ a + 1} from hle)
        rw [Metric.mem_closedBall, dist_eq_norm, hzn] at hmem
        have : r ≤ R := le_max_left _ _
        linarith
      have hconv : ψ z ≤ (1 - s) * ψ a + s * ψ x := by
        simpa only [smul_eq_mul] using
          hψ.2 (mem_univ a) (mem_univ x) (by linarith) hs0.le (by ring)
      have hkey : 1 < s * (ψ x - ψ a) := by nlinarith
      have hsd : s * d = 2 * R := by rw [hs]; field_simp
      have h2 : d / (2 * R) < ψ x - ψ a := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  refine ⟨1 / (2 * R), by positivity, ψ a - 1 - ‖a‖ / (2 * R), fun x => ?_⟩
  have hn : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - a) a
  have h := hclaim x
  have hdiv : ‖x‖ / (2 * R) ≤ (‖x - a‖ + ‖a‖) / (2 * R) :=
    div_le_div_of_nonneg_right hn (by positivity)
  rw [add_div] at hdiv
  have : 1 / (2 * R) * ‖x‖ = ‖x‖ / (2 * R) := by ring
  linarith

end Growth

section Gradient

/-- If `∇ψ` pushes the normalized measure `e^{-ψ} dx` forward to `μ` and `μ` is carried by the
closed ball of radius `R`, then `‖∇ψ(x)‖ ≤ R` for Lebesgue-almost every `x`. -/
theorem ae_norm_gradient_le {ψ : E → ℝ}
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ) {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∀ᵐ x ∂(volume : Measure E), ‖gradient ψ x‖ ≤ R := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  rw [← hmap] at hR
  exact (absolutelyContinuous_tilted (f := -ψ) hint).ae_le
    (ae_of_ae_map (measurable_gradient ψ).aemeasurable hR)

end Gradient

section Fenchel

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Fenchel equality at a differentiability point**: for convex `ψ` differentiable at `w`,
`ψ*(∇ψ(w)) = ⟪w, ∇ψ(w)⟫ − ψ(w)`. -/
theorem legendre_gradient {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ) {w : E}
    (hw : DifferentiableAt ℝ ψ w) :
    legendre (fun x => (ψ x : EReal)) (gradient ψ w) =
      ((⟪w, gradient ψ w⟫ - ψ w : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    have hinc := gradient_le_increment hψ w (x - w) hw
    rw [add_sub_cancel] at hinc
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [inner_sub_right, real_inner_comm w, real_inner_comm x] at hinc
    linarith
  · have h := le_iSup (fun x : E => (⟪x, gradient ψ w⟫ : EReal) - (ψ x : EReal)) w
    simpa only [legendre, EReal.coe_sub] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Fenchel–Young inequality with a finite real conjugate value**: if `ψ*(p) < ∞` then
`⟪x, p⟫ − ψ(x) ≤ ψ*(p)` for every `x`, where `ψ*(p)` is read as a real number. -/
theorem inner_sub_le_legendre_toReal {ψ : E → ℝ} {p : E}
    (hp : legendre (fun x => (ψ x : EReal)) p ≠ ⊤) (x : E) :
    ⟪x, p⟫ - ψ x ≤ (legendre (fun x => (ψ x : EReal)) p).toReal := by
  have h : ((⟪x, p⟫ - ψ x : ℝ) : EReal) ≤ legendre (fun x => (ψ x : EReal)) p := by
    have := le_iSup (fun z : E => (⟪z, p⟫ : EReal) - (ψ z : EReal)) x
    simpa only [legendre, EReal.coe_sub] using this
  have hb : legendre (fun x => (ψ x : EReal)) p ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
  rw [← EReal.coe_toReal hp hb, EReal.coe_le_coe_iff] at h
  exact h

omit [FiniteDimensional ℝ E] in
/-- The real-valued conjugate `p ↦ (ψ*(p)).toReal` is Borel measurable. -/
theorem measurable_legendre_toReal (ψ : E → ℝ) :
    Measurable fun p => (legendre (fun x => (ψ x : EReal)) p).toReal :=
  (lowerSemicontinuous_legendre _).measurable.ereal_toReal

/-- If `∇ψ` of a convex `ψ` pushes `e^{-ψ} dx` (tilted by `-ψ`) forward to `μ`, then `ψ*` is finite
`μ`-almost everywhere. -/
theorem ae_legendre_ne_top {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ) :
    ∀ᵐ p ∂μ, legendre (fun x => (ψ x : EReal)) p ≠ ⊤ := by
  have hD : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ w := by
    filter_upwards [hψ.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hset : MeasurableSet {p | legendre (fun x => (ψ x : EReal)) p ≠ ⊤} :=
    ((lowerSemicontinuous_legendre _).measurable (measurableSet_singleton ⊤)).compl
  rw [← hmap]
  refine (ae_map_iff (measurable_gradient ψ).aemeasurable hset).2 ?_
  filter_upwards [(tilted_absolutelyContinuous _ _).ae_le hD] with w hw
  rw [legendre_gradient hψ hw]
  exact EReal.coe_ne_top _

end Fenchel

section Maximality

private theorem abs_exp_sub_one_le_mul_exp (u : ℝ) : |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  rcases le_total 0 u with hu | hu
  · have h := Real.add_one_le_exp (-u)
    have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu
    rw [abs_of_nonneg hu, abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right h (Real.exp_pos u).le]
  · have h := Real.add_one_le_exp u
    have h1 : 1 ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    have h2 : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
    rw [abs_of_nonpos hu, abs_of_nonpos (by linarith : Real.exp u - 1 ≤ 0)]
    nlinarith

/-- **Maximality of a finite moment potential** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 8, for a finite convex potential). Let `ψ` be convex on `E` with `∫ e^{-ψ} = 1` and let
`∇ψ` push `e^{-ψ(x)} dx` forward to `μ`. Let `h` be measurable with `exp(s |h|)` `μ`-integrable for
some `s > 0`, and let `g ≥ 0` be measurable with, for almost every `w`,
`g(y) ≤ exp(h(∇ψ(w)) − ψ(w) − ⟪∇ψ(w), y − w⟫)` for all `y`. Then `∫ g ≤ exp(∫ h dμ)`.

Proof: for `0 < t < 1`, Prékopa–Leindler with exponents `1 − t`, `t` applied to `e^{-ψ}`, `g` and
`e^{-ψ + t h(∇ψ)}` (the tangent-plane inequality of `ψ` at `(1 − t) x + t y`) gives
`(∫ g)^t ≤ ∫ e^{t h} dμ`; hence `log ∫ g ≤ ∫ (e^{t h} − 1)/t dμ → ∫ h dμ` as `t → 0+`. -/
theorem lintegral_le_exp_integral_of_map_gradient {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ)
    {h : E → ℝ} (hh : Measurable h) {s : ℝ} (hs : 0 < s)
    (hexp : Integrable (fun p => Real.exp (s * |h p|)) μ)
    {g : E → ℝ≥0∞} (hg : Measurable g)
    (hdom : ∀ᵐ w ∂(volume : Measure E), ∀ y,
      g y ≤ ENNReal.ofReal (Real.exp (h (gradient ψ w) - ψ w - ⟪gradient ψ w, y - w⟫))) :
    ∫⁻ y, g y ∂(volume : Measure E) ≤ ENNReal.ofReal (Real.exp (∫ p, h p ∂μ)) := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hcont : Continuous ψ := continuousOn_univ.mp (hψ.continuousOn isOpen_univ)
  have hgrad := measurable_gradient ψ
  have : IsProbabilityMeasure ((volume : Measure E).tilted (-ψ)) :=
    isProbabilityMeasure_tilted hint
  have : IsProbabilityMeasure μ := by
    rw [← hmap]; exact (Measure.isProbabilityMeasure_map_iff hgrad.aemeasurable).2 inferInstance
  have hD : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ w := by
    filter_upwards [hψ.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  set P : E → Prop := fun w => DifferentiableAt ℝ ψ w ∧ ∀ y,
    g y ≤ ENNReal.ofReal (Real.exp (h (gradient ψ w) - ψ w - ⟪gradient ψ w, y - w⟫)) with hPdef
  have hP : ∀ᵐ w ∂(volume : Measure E), P w := hD.and hdom
  set N := toMeasurable (volume : Measure E) {w | ¬ P w} with hNdef
  have hN0 : (volume : Measure E) N = 0 := by
    rw [hNdef, measure_toMeasurable]; exact ae_iff.mp hP
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hPN : ∀ w, w ∉ N → P w := fun w hw => by
    by_contra hc; exact hw (subset_toMeasurable _ _ hc)
  set H : ℝ → E → ℝ≥0∞ := fun t w => N.indicator (fun _ => ∞) w +
    ENNReal.ofReal (Real.exp (-ψ w + t * h (gradient ψ w))) with hHdef
  have hHm : ∀ t, Measurable (H t) := fun t =>
    (measurable_const.indicator hNm).add (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (hcont.measurable.neg.add
        (measurable_const.mul (hh.comp hgrad)))))
  have hmeasexp : ∀ t : ℝ, Measurable fun p => ENNReal.ofReal (Real.exp (t * h p)) := fun t =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hh))
  have hHint : ∀ t, ∫⁻ w, H t w ∂(volume : Measure E) =
      ∫⁻ p, ENNReal.ofReal (Real.exp (t * h p)) ∂μ := by
    intro t
    have hae : (fun w => H t w) =ᵐ[volume] fun w => ENNReal.ofReal (Real.exp (-ψ w)) *
        ENNReal.ofReal (Real.exp (t * h (gradient ψ w))) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN0] with w hw
      simp only [hHdef, Set.indicator_of_notMem hw, zero_add]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [lintegral_congr_ae hae, ← hmap, lintegral_map (hmeasexp t) hgrad, lintegral_tilted]
    simp only [Pi.neg_apply, hnorm, div_one]
  have hf : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hcont.measurable.neg)
  have hf1 : ∫⁻ x, ENNReal.ofReal (Real.exp (-ψ x)) ∂(volume : Measure E) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => (Real.exp_pos _).le), hnorm, ENNReal.ofReal_one]
  have hPL : ∀ t, 0 < t → t < 1 →
      (∫⁻ y, g y ∂(volume : Measure E)) ^ t ≤
        ∫⁻ p, ENNReal.ofReal (Real.exp (t * h p)) ∂μ := by
    intro t ht0 ht1
    have h1t : 0 < 1 - t := by linarith
    have hPL := Analysis.lintegral_prekopaLeindler (volume : Measure E) hf hg (hHm t) h1t
      (by linarith : 1 - t < 1) (h := H t) ?_
    · rw [hf1, ENNReal.one_rpow, one_mul, sub_sub_cancel, hHint t] at hPL
      exact hPL
    · intro x y
      rw [sub_sub_cancel]
      set w := (1 - t) • x + t • y with hw
      by_cases hwN : w ∈ N
      · simp only [hHdef, Set.indicator_of_mem hwN, top_add, le_top]
      · obtain ⟨hdiff, hbound⟩ := hPN w hwN
        set p := gradient ψ w with hp
        have hinc := gradient_le_increment hψ w (x - w) hdiff
        rw [add_sub_cancel] at hinc
        have hvec : (1 - t) • (x - w) + t • (y - w) = 0 := by rw [hw]; module
        have hinner : (1 - t) * ⟪p, x - w⟫ + t * ⟪p, y - w⟫ = 0 := by
          rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hvec, inner_zero_right]
        rw [← hp] at hinc
        have hmul := mul_le_mul_of_nonneg_left hinc h1t.le
        calc ENNReal.ofReal (Real.exp (-ψ x)) ^ (1 - t) * g y ^ t
            ≤ ENNReal.ofReal (Real.exp (-ψ x)) ^ (1 - t) *
                ENNReal.ofReal (Real.exp (h p - ψ w - ⟪p, y - w⟫)) ^ t := by
              gcongr
              exact hbound y
          _ = ENNReal.ofReal (Real.exp (-ψ x * (1 - t) + (h p - ψ w - ⟪p, y - w⟫) * t)) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1t.le,
                ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0.le,
                ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul,
                ← Real.exp_add]
          _ ≤ ENNReal.ofReal (Real.exp (-ψ w + t * h p)) := by
              refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
              nlinarith
          _ ≤ H t w := by simp only [hHdef]; exact le_add_self
  have hexpt : ∀ t, 0 ≤ t → t ≤ s → Integrable (fun p => Real.exp (t * h p)) μ := by
    intro t ht0 hts
    refine hexp.mono' ((hh.const_mul t).exp.aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) ht0)
      (mul_le_mul_of_nonneg_right hts (abs_nonneg _)))
  have hlt : ∀ t, 0 < t → t ≤ s → ∫⁻ p, ENNReal.ofReal (Real.exp (t * h p)) ∂μ =
      ENNReal.ofReal (∫ p, Real.exp (t * h p) ∂μ) := fun t ht hts =>
    (ofReal_integral_eq_lintegral_ofReal (hexpt t ht.le hts)
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm
  set A := ∫⁻ y, g y ∂(volume : Measure E) with hAdef
  set t₀ := min s 1 / 2 with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  have ht₀1 : t₀ < 1 := by have := min_le_right s 1; linarith
  have ht₀s : t₀ ≤ s / 2 := by have := min_le_left s 1; linarith
  have hAtop : A ≠ ∞ := by
    intro hA
    have h1 := hPL t₀ ht₀ ht₀1
    rw [hA, ENNReal.top_rpow_of_pos ht₀, hlt t₀ ht₀ (by linarith)] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h1)
  by_cases hA0 : A = 0
  · rw [hA0]; exact zero_le
  set a := A.toReal with hadef
  have ha0 : 0 < a := ENNReal.toReal_pos hA0 hAtop
  have hAa : A = ENNReal.ofReal a := (ENNReal.ofReal_toReal hAtop).symm
  set F : ℝ → ℝ := fun t => ∫ p, (Real.exp (t * h p) - 1) / t ∂μ with hFdef
  have hkey : ∀ t, 0 < t → t ≤ t₀ → Real.log a ≤ F t := by
    intro t ht htt
    have hts : t ≤ s := by linarith
    have h1 := hPL t ht (by linarith)
    rw [hlt t ht hts, hAa, ENNReal.ofReal_rpow_of_nonneg ha0.le ht.le] at h1
    have hM := (ENNReal.ofReal_le_ofReal_iff
      (integral_nonneg (fun _ => (Real.exp_pos _).le))).mp h1
    set M := ∫ p, Real.exp (t * h p) ∂μ with hMdef
    have hM0 : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos ha0 t) hM
    have hlog : t * Real.log a ≤ M - 1 := by
      rw [← Real.log_rpow ha0]
      exact (Real.log_le_log (Real.rpow_pos_of_pos ha0 t) hM).trans
        (Real.log_le_sub_one_of_pos hM0)
    have hF : F t = (M - 1) / t := by
      simp only [hFdef]
      rw [integral_div, integral_sub (hexpt t ht.le hts) (integrable_const 1), integral_const]
      simp only [probReal_univ, smul_eq_mul, mul_one, hMdef]
    rw [hF, le_div_iff₀ ht]
    linarith
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (∫ p, h p ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun p => 2 / s * Real.exp (s * |h p|)) ?_ ?_ (hexp.const_mul _) ?_
    · exact Eventually.of_forall fun t =>
        (((hh.const_mul t).exp.sub measurable_const).div_const t).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < s / 2 by positivity)] with t ht
      refine Eventually.of_forall fun p => ?_
      have hu := abs_exp_sub_one_le_mul_exp (t * h p)
      have hth : |t * h p| = t * |h p| := by rw [abs_mul, abs_of_pos ht.1]
      rw [hth] at hu
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1, div_le_iff₀ ht.1]
      have he1 : Real.exp (t * |h p|) ≤ Real.exp (s / 2 * |h p|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2.le (abs_nonneg _))
      have he2 : s / 2 * |h p| ≤ Real.exp (s / 2 * |h p|) := by
        linarith [Real.add_one_le_exp (s / 2 * |h p|)]
      have he3 : Real.exp (s * |h p|) =
          Real.exp (s / 2 * |h p|) * Real.exp (s / 2 * |h p|) := by
        rw [← Real.exp_add]; ring_nf
      have ht0 : 0 ≤ t * |h p| := mul_nonneg ht.1.le (abs_nonneg _)
      have ht1 : 0 ≤ t * (2 / s) := mul_nonneg ht.1.le (by positivity)
      calc |Real.exp (t * h p) - 1| ≤ t * |h p| * Real.exp (t * |h p|) := hu
        _ ≤ t * |h p| * Real.exp (s / 2 * |h p|) := mul_le_mul_of_nonneg_left he1 ht0
        _ = t * (2 / s) * (s / 2 * |h p|) * Real.exp (s / 2 * |h p|) := by
          field_simp
        _ ≤ t * (2 / s) * Real.exp (s / 2 * |h p|) * Real.exp (s / 2 * |h p|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 ht1) (Real.exp_pos _).le
        _ = 2 / s * Real.exp (s * |h p|) * t := by rw [he3]; ring
    · refine Eventually.of_forall fun p => ?_
      have hd : HasDerivAt (fun t : ℝ => Real.exp (t * h p)) (h p) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (h p)).exp
      have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
        (nhdsWithin_mono _ (fun t (ht : 0 < t) => ne_of_gt ht))
      refine hsl.congr' (Eventually.of_forall fun t => ?_)
      simp [slope_def_field]
  have hle : Real.log a ≤ ∫ p, h p ∂μ :=
    ge_of_tendsto hlim (by
      filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht using hkey t ht.1 ht.2.le)
  rw [hAa]
  exact ENNReal.ofReal_le_ofReal ((Real.log_le_iff_le_exp ha0).mp hle)

end Maximality

section ConjugateIntegrability

/-- **Exponential integrability of the conjugate under a bounded-support moment measure.** If a
convex `ψ` with `∫ e^{-ψ} = 1` has gradient pushing `e^{-ψ(x)} dx` forward to `μ`, and `μ` is
carried by the closed ball of radius `R`, then `p ↦ exp(s |ψ*(p)|)` is `μ`-integrable for some
`s > 0` (`ψ*(p)` read as a real number; it is finite `μ`-a.e. by `ae_legendre_ne_top`). -/
theorem exists_integrable_exp_mul_abs_legendre {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ) {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∃ s : ℝ, 0 < s ∧ Integrable
      (fun p => Real.exp (s * |(legendre (fun x => (ψ x : EReal)) p).toReal|)) μ := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  obtain ⟨c, hc, b, hb⟩ := exists_linear_lower_bound_of_integrable_exp_neg volume hψ hint
  set K : ℝ := |R| + 1 with hKdef
  have hK : 0 < K := by positivity
  set s : ℝ := min (1 / 2) (c / (4 * K)) with hsdef
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 2 := min_le_left _ _
  have hsK : s * K ≤ c / 4 := by
    have := min_le_right (1 / 2 : ℝ) (c / (4 * K))
    rw [← hsdef, le_div_iff₀ (by positivity)] at this
    linarith
  refine ⟨s, hs0, ?_⟩
  have hgrad := measurable_gradient ψ
  have hmeas : Measurable fun p => Real.exp (s * |(legendre (fun x => (ψ x : EReal)) p).toReal|) :=
    Real.measurable_exp.comp (measurable_const.mul
      (continuous_abs.measurable.comp (measurable_legendre_toReal ψ)))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  rw [← hmap, lintegral_map (f := fun p => ENNReal.ofReal
    (Real.exp (s * |(legendre (fun x => (ψ x : EReal)) p).toReal|)))
    (ENNReal.measurable_ofReal.comp hmeas) hgrad, lintegral_tilted]
  simp only [Pi.neg_apply, hnorm, div_one]
  have hD : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ w := by
    filter_upwards [hψ.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hbound := ae_norm_gradient_le hnorm hmap hR
  have hdecay : Integrable (fun x => Real.exp (-(c / 4 * ‖x‖))) (volume : Measure E) := by
    simpa only [pow_zero, one_mul] using
      integrable_norm_pow_mul_exp_neg_mul_norm (volume : Measure E) (show 0 < c / 4 by positivity) 0
  have hfin := (hdecay.const_mul (Real.exp (2 * |b|))).lintegral_lt_top
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  filter_upwards [hD, hbound] with x hx hxR
  rw [legendre_gradient hψ hx, EReal.toReal_coe, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hin : |⟪x, gradient ψ x⟫| ≤ K * ‖x‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hxR.trans (by rw [hKdef]; linarith [le_abs_self R]))
      (norm_nonneg _)
  have hq : |⟪x, gradient ψ x⟫ - ψ x| ≤ K * ‖x‖ + |ψ x| :=
    (abs_sub _ _).trans (by linarith)
  have hsq := mul_le_mul_of_nonneg_left hq hs0.le
  have hsKx : s * (K * ‖x‖) ≤ c / 4 * ‖x‖ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hsK (norm_nonneg _)
  have hgx := hb x
  have hn := norm_nonneg x
  rcases le_total 0 (ψ x) with hψ0 | hψ0
  · rw [abs_of_nonneg hψ0] at hsq
    have : s * ψ x ≤ 1 / 2 * ψ x := mul_le_mul_of_nonneg_right hs1 hψ0
    nlinarith [neg_abs_le b, le_abs_self b]
  · rw [abs_of_nonpos hψ0] at hsq
    have : s * -ψ x ≤ 1 * -ψ x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [neg_abs_le b, le_abs_self b]

end ConjugateIntegrability

end FunctionalInequalities.Probability.MomentMeasure

end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation (measurable_gradient)

/-- A measurable function bounded below whose truncations `min f k` have uniformly bounded
integrals under a finite measure is integrable. -/
private theorem integrable_of_integral_min_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {c : ℝ} (hc : ∀ p, c ≤ f p) {B : ℝ}
    (hB : ∀ k : ℝ, ∫ p, min (f p) k ∂μ ≤ B) : Integrable f μ := by
  set F : ℕ → α → ℝ≥0∞ := fun n p => ENNReal.ofReal (min (f p) (c + n) - c) with hFdef
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp ((hf.min measurable_const).sub_const c)
  have hmono : Monotone F := by
    intro m n hmn p
    refine ENNReal.ofReal_le_ofReal (sub_le_sub_right (min_le_min_left _ ?_) c)
    have := (Nat.cast_le (α := ℝ)).mpr hmn
    linarith
  have hsup : ∀ p, ⨆ n, F n p = ENNReal.ofReal (f p - c) := by
    intro p
    refine le_antisymm (iSup_le fun n =>
      ENNReal.ofReal_le_ofReal (sub_le_sub_right (min_le_left _ _) c)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (f p - c)
    refine le_trans (le_of_eq ?_) (le_iSup (fun n => F n p) n)
    simp only [hFdef]
    rw [min_eq_left (by linarith)]
  have hbound : ∀ n : ℕ, ∫⁻ p, F n p ∂μ ≤ ENNReal.ofReal (B - c * μ.real univ) := by
    intro n
    have hint : Integrable (fun p => min (f p) (c + n) - c) μ := by
      refine (integrable_const (n : ℝ)).mono'
        ((hf.min measurable_const).sub_const c).aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hc p
        have : c ≤ min (f p) (c + n) := le_min this (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
        linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      · linarith [min_le_right (f p) (c + n)]
    have hmin : Integrable (fun p => min (f p) (c + n)) μ := by
      exact (hint.add (integrable_const c)).congr
        (ae_of_all _ fun p => by simp only [Pi.add_apply, sub_add_cancel])
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun p => sub_nonneg.mpr
      (le_min (hc p) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_sub hmin (integrable_const c), integral_const, smul_eq_mul]
    linarith [hB (c + n), mul_comm c (μ.real univ)]
  have hfin : HasFiniteIntegral (fun p => f p - c) μ := by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => sub_nonneg.mpr (hc p))]
    calc ∫⁻ p, ENNReal.ofReal (f p - c) ∂μ = ∫⁻ p, ⨆ n, F n p ∂μ := by simp_rw [hsup]
      _ = ⨆ n, ∫⁻ p, F n p ∂μ := lintegral_iSup hFm hmono
      _ ≤ ENNReal.ofReal (B - c * μ.real univ) := iSup_le hbound
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hfc : Integrable (fun p => f p - c) μ := ⟨(hf.sub_const c).aestronglyMeasurable, hfin⟩
  exact (hfc.add (integrable_const c)).congr
    (ae_of_all _ fun p => by simp only [Pi.add_apply, sub_add_cancel])

/-- `exp(|b|)` is integrable under a finite measure when `|b| ≤ K`. -/
private theorem integrable_exp_abs_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {b : α → ℝ} (hb : Measurable b) {K : ℝ} (hK : ∀ p, |b p| ≤ K) :
    Integrable (fun p => Real.exp (1 * |b p|)) μ := by
  refine (integrable_const (Real.exp K)).mono'
    (Real.measurable_exp.comp (measurable_const.mul
      (continuous_abs.measurable.comp hb))).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr (hK p)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The moment measure of a normalized potential is a probability measure. -/
private theorem isProbabilityMeasure_of_map_gradient {ψ : E → ℝ}
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ) : IsProbabilityMeasure μ := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have : IsProbabilityMeasure ((volume : Measure E).tilted (-ψ)) := isProbabilityMeasure_tilted hint
  rw [← hmap]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_gradient ψ).aemeasurable).2 inferInstance

/-- **Integrability of a perturbation bounded above.** Let `ψ` be convex with `∫ e^{-ψ} = 1`
whose gradient pushes `e^{-ψ(x)} dx` forward to `μ`. If `h ≤ M` is measurable and a measurable
`g ≥ 0` with `∫ g ≠ 0` satisfies, for almost every `w`,
`g(y) ≤ exp(h(∇ψ(w)) − ψ(w) − ⟪∇ψ(w), y − w⟫)` for all `y`, then `h` is `μ`-integrable. -/
theorem integrable_of_map_gradient_of_le {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ)
    {h : E → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ p, h p ≤ M)
    {g : E → ℝ≥0∞} (hg : Measurable g) (hg0 : ∫⁻ y, g y ∂(volume : Measure E) ≠ 0)
    (hdom : ∀ᵐ w ∂(volume : Measure E), ∀ y,
      g y ≤ ENNReal.ofReal (Real.exp (h (gradient ψ w) - ψ w - ⟪gradient ψ w, y - w⟫))) :
    Integrable h μ := by
  have := isProbabilityMeasure_of_map_gradient hnorm hmap
  set A := ∫⁻ y, g y ∂(volume : Measure E) with hAdef
  have hkey : ∀ k : ℝ, A ≤ ENNReal.ofReal (Real.exp (∫ p, max (h p) (-k) ∂μ)) := by
    intro k
    refine lintegral_le_exp_integral_of_map_gradient hψ hnorm hmap (hh.max measurable_const)
      one_pos (integrable_exp_abs_of_le (hh.max measurable_const) (K := |M| + |k|) fun p => ?_)
      hg ?_
    · rw [abs_le]
      constructor
      · have := le_max_right (h p) (-k)
        linarith [le_abs_self k, abs_nonneg M]
      · exact max_le ((hM p).trans ((le_abs_self M).trans (le_add_of_nonneg_right
          (abs_nonneg k)))) (by linarith [neg_abs_le k, le_abs_self k, abs_nonneg M])
    · filter_upwards [hdom] with w hw y
      refine (hw y).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
      linarith [le_max_left (h (gradient ψ w)) (-k)]
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hkey 0)
  have hA : 0 < A.toReal := ENNReal.toReal_pos hg0 hAtop
  have hL : ∀ k : ℝ, Real.log A.toReal ≤ ∫ p, max (h p) (-k) ∂μ := fun k => by
    have h1 := hkey k
    rw [← ENNReal.ofReal_toReal hAtop, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at h1
    exact (Real.log_le_iff_le_exp hA).mpr h1
  have hneg : Integrable (fun p => -h p) μ := by
    refine integrable_of_integral_min_le hh.neg (c := -M) (fun p => by linarith [hM p])
      (B := -Real.log A.toReal) fun k => ?_
    have heq : ∫ p, min (-h p) k ∂μ = -∫ p, max (h p) (-k) ∂μ := by
      rw [← integral_neg]
      congr 1
      funext p
      rw [← neg_neg k, min_neg_neg, neg_neg]
    rw [heq]
    linarith [hL k]
  exact hneg.neg.congr (ae_of_all _ fun p => by simp only [Pi.neg_apply, neg_neg])

/-- **Maximality of a finite moment potential against integrable perturbations**
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 8, (18), for a finite convex potential and
an arbitrary moment measure). Let `ψ` be convex on `E` with `∫ e^{-ψ} = 1` and let `∇ψ` push
`e^{-ψ(x)} dx` forward to `μ`. Let `h` be measurable and `μ`-integrable, and let `g ≥ 0` be
measurable with, for almost every `w`, `g(y) ≤ exp(h(∇ψ(w)) − ψ(w) − ⟪∇ψ(w), y − w⟫)` for all
`y`. Then `∫ g ≤ exp(∫ h dμ)`. -/
theorem lintegral_le_exp_integral_of_map_gradient_of_integrable {ψ : E → ℝ}
    (hψ : ConvexOn ℝ univ ψ) (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1)
    {μ : Measure E} (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ)
    {h : E → ℝ} (hh : Measurable h) (hint : Integrable h μ)
    {g : E → ℝ≥0∞} (hg : Measurable g)
    (hdom : ∀ᵐ w ∂(volume : Measure E), ∀ y,
      g y ≤ ENNReal.ofReal (Real.exp (h (gradient ψ w) - ψ w - ⟪gradient ψ w, y - w⟫))) :
    ∫⁻ y, g y ∂(volume : Measure E) ≤ ENNReal.ofReal (Real.exp (∫ p, h p ∂μ)) := by
  have := isProbabilityMeasure_of_map_gradient hnorm hmap
  have hcont : Continuous ψ := continuousOn_univ.mp (hψ.continuousOn isOpen_univ)
  have hD : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ w := by
    filter_upwards [hψ.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  set b : ℕ → E → ℝ := fun k p => max (min (h p) k) (-k) with hbdef
  have hbm : ∀ k, Measurable (b k) := fun k => (hh.min measurable_const).max measurable_const
  set G : ℕ → E → ℝ≥0∞ := fun k y => min (g y) (ENNReal.ofReal (Real.exp (k - ψ y))) with hGdef
  have hGm : ∀ k, Measurable (G k) := fun k => hg.min (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.sub hcont.measurable)))
  have hstep : ∀ k : ℕ, ∫⁻ y, G k y ∂(volume : Measure E) ≤
      ENNReal.ofReal (Real.exp (∫ p, b k p ∂μ)) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine lintegral_le_exp_integral_of_map_gradient hψ hnorm hmap (hbm k) one_pos
      (integrable_exp_abs_of_le (hbm k) (K := k) fun p => ?_) (hGm k) ?_
    · rw [abs_le]
      exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
    · filter_upwards [hdom, hD] with w hw hwd y
      have hinc := gradient_le_increment hψ w (y - w) hwd
      rw [add_sub_cancel] at hinc
      by_cases hk : h (gradient ψ w) ≤ k
      · have hb : h (gradient ψ w) ≤ b k (gradient ψ w) := by
          simp only [hbdef, min_eq_left hk]
          exact le_max_left _ _
        refine (min_le_left _ _).trans ((hw y).trans
          (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
        linarith
      · have hb : b k (gradient ψ w) = k := by
          simp only [hbdef, min_eq_right (not_le.mp hk).le]
          exact max_eq_left (by linarith)
        refine (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
        rw [hb]
        linarith
  have hGlim : Tendsto (fun k => ∫⁻ y, G k y ∂(volume : Measure E)) atTop
      (𝓝 (∫⁻ y, g y ∂(volume : Measure E))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun k => (hGm k).aemeasurable)
      (ae_of_all _ fun y m n hmn => ?_) (ae_of_all _ fun y => ?_)
    · refine min_le_min_left _ (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
      have : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      linarith
    · have hto : Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp (k - ψ y))) atTop (𝓝 ⊤) :=
        ENNReal.tendsto_ofReal_atTop.comp (Real.tendsto_exp_atTop.comp
          (tendsto_atTop_add_const_right _ (-ψ y) tendsto_natCast_atTop_atTop |>.congr
            fun k => by ring))
      simpa only [min_top_right] using (tendsto_const_nhds (x := g y)).min hto
  have hblim : Tendsto (fun k => ∫ p, b k p ∂μ) atTop (𝓝 (∫ p, h p ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun p => |h p|)
      (fun k => (hbm k).aestronglyMeasurable) hint.abs (fun k => ae_of_all _ fun p => ?_)
      (ae_of_all _ fun p => ?_)
    · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have h1 := neg_abs_le (h p)
        exact (le_min h1 (by linarith [abs_nonneg (h p)])).trans (le_max_left _ _)
      · exact max_le ((min_le_left _ _).trans (le_abs_self _)) (by linarith [abs_nonneg (h p)])
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|h p|⌉₊] with k hk
      have hk' : |h p| ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)
      rw [abs_le] at hk'
      simp only [hbdef]
      rw [min_eq_left hk'.2, max_eq_left hk'.1]
  have hRlim : Tendsto (fun k => ENNReal.ofReal (Real.exp (∫ p, b k p ∂μ))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (∫ p, h p ∂μ)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp hblim)
  exact le_of_tendsto_of_tendsto' hGlim hRlim hstep

/-- **The conjugate of a finite moment potential is integrable** (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, Proposition 7, for a finite convex potential and an arbitrary moment measure).
If `ψ` is convex on `E` with `∫ e^{-ψ} = 1` and `∇ψ` pushes `e^{-ψ(x)} dx` forward to `μ`, then
`p ↦ ψ*(p)`, read as a real number, is `μ`-integrable. -/
theorem integrable_legendre_toReal {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ) :
    Integrable (fun p => (legendre (fun x => (ψ x : EReal)) p).toReal) μ := by
  set C : E → ℝ := fun p => (legendre (fun x => (ψ x : EReal)) p).toReal with hCdef
  have hCm : Measurable C := measurable_legendre_toReal ψ
  have hlow : ∀ p, min 0 (-ψ 0) ≤ C p := by
    intro p
    by_cases hp : legendre (fun x => (ψ x : EReal)) p = ⊤
    · simp only [hCdef, hp, EReal.toReal_top]
      exact min_le_left _ _
    · have h0 := inner_sub_le_legendre_toReal hp 0
      rw [inner_zero_left, zero_sub] at h0
      exact (min_le_right _ _).trans h0
  have hc : Continuous ψ := continuousOn_univ.mp (hψ.continuousOn isOpen_univ)
  set g : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-ψ ((2 : ℝ) • y) / 2)) with hgdef
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hc.comp (continuous_const_smul (2 : ℝ))).measurable.neg.div_const 2))
  have hg0 : ∫⁻ y, g y ∂(volume : Measure E) ≠ 0 := by
    intro h0
    rw [lintegral_eq_zero_iff hg] at h0
    have hF : ∀ᵐ y ∂(volume : Measure E), False :=
      h0.mono fun y hy => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hy
    obtain ⟨_, hy⟩ := hF.exists
    exact hy
  have hD : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ w := by
    filter_upwards [hψ.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hneg := integrable_of_map_gradient_of_le hψ hnorm hmap (h := fun p => -C p / 2)
    (hCm.neg.div_const 2) (M := -min 0 (-ψ 0) / 2) (fun p => by linarith [hlow p]) hg hg0 (by
      filter_upwards [hD] with w hw y
      have hC : C (gradient ψ w) = ⟪w, gradient ψ w⟫ - ψ w := by
        simp only [hCdef, legendre_gradient hψ hw, EReal.toReal_coe]
      have hinc := gradient_le_increment hψ w ((2 : ℝ) • y - w) hw
      rw [add_sub_cancel, inner_sub_right, real_inner_smul_right] at hinc
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      rw [hC, inner_sub_right, real_inner_comm (gradient ψ w) w]
      linarith)
  exact (hneg.const_mul (-2)).congr (ae_of_all _ fun p => by ring)

end FunctionalInequalities.Probability.MomentMeasure
