import FunctionalInequalities.Probability.MomentMeasure.Gradient
import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.MidpointEquality
import FunctionalInequalities.Probability.MomentMeasure.Maximality.Finite

/-!
# Uniqueness of finite moment potentials

## Bounded-support moment measure

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Theorem 2, uniqueness up to
translation (= Letwin arXiv:2607.24164v1, Lemma 2.1, uniqueness), for finite convex potentials
whose moment measure has bounded support: if `ψ₀, ψ₁ : E → ℝ` are convex on a finite-dimensional
real inner-product space with `∫ e^{-ψᵢ} = 1`, and both gradients push `e^{-ψᵢ(x)} dx` forward to
the same `μ` carried by a closed ball, then `ψ₁ = ψ₀(· − y₀)` for some `y₀`
(`exists_eq_translate_of_map_gradient_eq`); conversely every translate of `ψ₀` has moment measure
`μ` (`map_gradient_eq_iff_exists_eq_translate`).

Route (CEK, proof of Theorem 2, uniqueness, through the equality case of Prékopa–Leindler): the
midpoint density `midpointDensity ψ₀ ψ₁ y = sup_a exp(−(ψ₀(a) + ψ₁(2y − a))/2)` satisfies
`ρ½((x + y)/2) ≥ √(e^{-ψ₀(x)} e^{-ψ₁(y)})`, and the maximality inequality
`lintegral_le_exp_integral_of_map_gradient`, applied at `ψ₀` and at `ψ₁` with
`h = ±(ψ₁* − ψ₀*)/2`, gives `∫ ρ½ ≤ 1`; the equality case
`exists_eq_translate_of_lintegral_midpointDensity_le_one` (Dubuc) then yields the translation.

## Arbitrary moment measure

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Theorem 2, uniqueness up to
translation (= Letwin arXiv:2607.24164v1, Lemma 2.1, uniqueness), for finite convex potentials,
with no assumption on the support of the moment measure: if `ψ₀, ψ₁ : E → ℝ` are convex on a
finite-dimensional real inner-product space with `∫ e^{-ψᵢ} = 1`, and both gradients push
`e^{-ψᵢ(x)} dx` forward to the same `μ`, then `ψ₁ = ψ₀(· − y₀)` for some `y₀`
(`exists_eq_translate_of_map_gradient_eq_unbounded`); conversely every translate of `ψ₀` has moment
measure `μ` (`map_gradient_eq_iff_exists_eq_translate_unbounded`). The bounded-support case is
`exists_eq_translate_of_map_gradient_eq`.

Route (CEK, proof of Theorem 2, uniqueness): the conjugates `ψᵢ*` are `μ`-integrable
(`integrable_legendre_toReal`, CEK Proposition 7), so the maximality inequality
`lintegral_le_exp_integral_of_map_gradient_of_integrable` (CEK Theorem 8), applied at `ψ₀` and at
`ψ₁` with `h = ±(ψ₁* − ψ₀*)/2`, bounds the mass of the midpoint density by `1`; the equality case
of Prékopa–Leindler (`exists_eq_translate_of_lintegral_midpointDensity_le_one`) concludes.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation (measurable_gradient)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Midpoint

/-- If `ψ'` has moment measure `μ` and `∇ψ` pushes the normalized `e^{-ψ} dx` to `μ`, then
`ψ'*(∇ψ(w)) < ∞` for almost every `w`. -/
private theorem ae_legendre_gradient_ne_top {ψ ψ' : E → ℝ}
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) (hψ' : ConvexOn ℝ univ ψ')
    {μ : Measure E} (hmap : ((volume : Measure E).tilted (-ψ)).map (gradient ψ) = μ)
    (hmap' : ((volume : Measure E).tilted (-ψ')).map (gradient ψ') = μ) :
    ∀ᵐ w ∂(volume : Measure E), legendre (fun x => (ψ' x : EReal)) (gradient ψ w) ≠ ⊤ := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have h := ae_legendre_ne_top hψ' hmap'
  rw [← hmap] at h
  exact (absolutelyContinuous_tilted (f := -ψ) hint).ae_le
    (ae_of_ae_map (measurable_gradient ψ).aemeasurable h)

private theorem exp_mul_abs_half_sub_le {s s₀ s₁ a b : ℝ} (hs₀ : s ≤ s₀) (hs₁ : s ≤ s₁)
    (hs : 0 ≤ s) :
    Real.exp (s * |(a - b) / 2|) ≤ Real.exp (s₀ * |b|) + Real.exp (s₁ * |a|) := by
  have hab : |(a - b) / 2| ≤ (|a| + |b|) / 2 := by
    rw [abs_div, abs_two]
    gcongr
    exact abs_sub _ _
  have h1 : s * |(a - b) / 2| ≤ max (s₀ * |b|) (s₁ * |a|) := by
    have hsa : s * |a| ≤ s₁ * |a| := mul_le_mul_of_nonneg_right hs₁ (abs_nonneg _)
    have hsb : s * |b| ≤ s₀ * |b| := mul_le_mul_of_nonneg_right hs₀ (abs_nonneg _)
    have := mul_le_mul_of_nonneg_left hab hs
    rcases le_total (s₀ * |b|) (s₁ * |a|) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  calc Real.exp (s * |(a - b) / 2|) ≤ Real.exp (max (s₀ * |b|) (s₁ * |a|)) :=
        Real.exp_le_exp.mpr h1
    _ ≤ Real.exp (s₀ * |b|) + Real.exp (s₁ * |a|) := by
        rcases le_total (s₀ * |b|) (s₁ * |a|) with h | h
        · rw [max_eq_right h]; linarith [Real.exp_pos (s₀ * |b|)]
        · rw [max_eq_left h]; linarith [Real.exp_pos (s₁ * |a|)]

/-- **Midpoint mass bound** (CEK Theorem 2, uniqueness step): for two normalized convex potentials
with the same bounded-support moment measure, the midpoint density has total mass at most `1`. -/
private theorem lintegral_midpointDensity_le_one {ψ₀ ψ₁ : E → ℝ} (hψ₀ : ConvexOn ℝ univ ψ₀)
    (hψ₁ : ConvexOn ℝ univ ψ₁) (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hm₀ : ((volume : Measure E).tilted (-ψ₀)).map (gradient ψ₀) = μ)
    (hm₁ : ((volume : Measure E).tilted (-ψ₁)).map (gradient ψ₁) = μ) {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∫⁻ y, midpointDensity ψ₀ ψ₁ y ∂(volume : Measure E) ≤ 1 := by
  set C₀ : E → ℝ := fun p => (legendre (fun x => (ψ₀ x : EReal)) p).toReal with hC₀
  set C₁ : E → ℝ := fun p => (legendre (fun x => (ψ₁ x : EReal)) p).toReal with hC₁
  obtain ⟨s₀, hs₀, hi₀⟩ := exists_integrable_exp_mul_abs_legendre hψ₀ hn₀ hm₀ hR
  obtain ⟨s₁, hs₁, hi₁⟩ := exists_integrable_exp_mul_abs_legendre hψ₁ hn₁ hm₁ hR
  set s := min s₀ s₁ with hsdef
  have hs : 0 < s := lt_min hs₀ hs₁
  have hmC₀ : Measurable C₀ := measurable_legendre_toReal ψ₀
  have hmC₁ : Measurable C₁ := measurable_legendre_toReal ψ₁
  have hc₀ : Continuous ψ₀ := continuousOn_univ.mp (hψ₀.continuousOn isOpen_univ)
  have hc₁ : Continuous ψ₁ := continuousOn_univ.mp (hψ₁.continuousOn isOpen_univ)
  have hexp : ∀ (a b : E → ℝ) (sa sb : ℝ), s ≤ sa → s ≤ sb → Measurable a → Measurable b →
      Integrable (fun p => Real.exp (sb * |b p|)) μ →
      Integrable (fun p => Real.exp (sa * |a p|)) μ →
      Integrable (fun p => Real.exp (s * |(a p - b p) / 2|)) μ := by
    intro a b sa sb hsa hsb ha hb hia hib
    refine (hia.add hib).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (Real.measurable_exp.comp (measurable_const.mul
        (continuous_abs.measurable.comp ((ha.sub hb).div_const _)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_mul_abs_half_sub_le hsb hsa hs.le
  have hD₀ : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ₀ w := by
    filter_upwards [hψ₀.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hD₁ : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ₁ w := by
    filter_upwards [hψ₁.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hmid := measurable_midpointDensity ψ₀ hc₁
  -- maximality at `ψ₀` with `h = (ψ₁* − ψ₀*)/2`
  have hI₀ := lintegral_le_exp_integral_of_map_gradient hψ₀ hn₀ hm₀
    (h := fun p => (C₁ p - C₀ p) / 2) ((hmC₁.sub hmC₀).div_const 2) hs
    (hexp C₁ C₀ s₁ s₀ (min_le_right _ _) (min_le_left _ _) hmC₁ hmC₀ hi₀ hi₁) hmid (by
      filter_upwards [hD₀, ae_legendre_gradient_ne_top hn₀ hψ₁ hm₀ hm₁] with w hw hfin
      intro y
      have hfin₀ : legendre (fun x => (ψ₀ x : EReal)) (gradient ψ₀ w) ≠ ⊤ := by
        rw [legendre_gradient hψ₀ hw]; exact EReal.coe_ne_top _
      refine (midpointDensity_le_of_legendre ψ₀ ψ₁ hfin₀ hfin y).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))
      have hC : C₀ (gradient ψ₀ w) = ⟪w, gradient ψ₀ w⟫ - ψ₀ w := by
        simp only [hC₀, legendre_gradient hψ₀ hw, EReal.toReal_coe]
      simp only [hC₀, hC₁] at hC ⊢
      rw [hC, inner_sub_right, real_inner_comm (gradient ψ₀ w) w]
      ring)
  -- maximality at `ψ₁` with `h = (ψ₀* − ψ₁*)/2`
  have hI₁ := lintegral_le_exp_integral_of_map_gradient hψ₁ hn₁ hm₁
    (h := fun p => (C₀ p - C₁ p) / 2) ((hmC₀.sub hmC₁).div_const 2) hs
    (hexp C₀ C₁ s₀ s₁ (min_le_left _ _) (min_le_right _ _) hmC₀ hmC₁ hi₁ hi₀) hmid (by
      filter_upwards [hD₁, ae_legendre_gradient_ne_top hn₁ hψ₀ hm₁ hm₀] with w hw hfin
      intro y
      have hfin₁ : legendre (fun x => (ψ₁ x : EReal)) (gradient ψ₁ w) ≠ ⊤ := by
        rw [legendre_gradient hψ₁ hw]; exact EReal.coe_ne_top _
      refine (midpointDensity_le_of_legendre ψ₀ ψ₁ hfin hfin₁ y).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))
      have hC : C₁ (gradient ψ₁ w) = ⟪w, gradient ψ₁ w⟫ - ψ₁ w := by
        simp only [hC₁, legendre_gradient hψ₁ hw, EReal.toReal_coe]
      simp only [hC₀, hC₁] at hC ⊢
      rw [hC, inner_sub_right, real_inner_comm (gradient ψ₁ w) w]
      ring)
  have hneg : ∫ p, (C₀ p - C₁ p) / 2 ∂μ = -∫ p, (C₁ p - C₀ p) / 2 ∂μ := by
    rw [← integral_neg]
    congr 1
    funext p
    ring
  rw [hneg] at hI₁
  rcases le_total (∫ p, (C₁ p - C₀ p) / 2 ∂μ) 0 with h | h
  · refine hI₀.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr h)
  · refine hI₁.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by linarith))

end Midpoint

section Translation

/-- **Uniqueness of finite moment potentials with bounded-support moment measure**
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2, uniqueness up to translation; Letwin
arXiv:2607.24164v1, Lemma 2.1). Let `ψ₀, ψ₁` be convex functions on a finite-dimensional real
inner-product space with `∫ e^{-ψᵢ} = 1`, whose gradients push `e^{-ψᵢ(x)} dx` forward to the same
measure `μ`, and let `μ` be carried by the closed ball of radius `R`. Then `ψ₁ = ψ₀(· − y₀)` for
some `y₀`. -/
theorem exists_eq_translate_of_map_gradient_eq {ψ₀ ψ₁ : E → ℝ} (hψ₀ : ConvexOn ℝ univ ψ₀)
    (hψ₁ : ConvexOn ℝ univ ψ₁) (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hm₀ : ((volume : Measure E).tilted (-ψ₀)).map (gradient ψ₀) = μ)
    (hm₁ : ((volume : Measure E).tilted (-ψ₁)).map (gradient ψ₁) = μ) {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) :=
  exists_eq_translate_of_lintegral_midpointDensity_le_one hψ₀ hψ₁ hn₀ hn₁
    (lintegral_midpointDensity_le_one hψ₀ hψ₁ hn₀ hn₁ hm₀ hm₁ hR)

/-- **Moment potentials of a bounded-support measure are unique up to translation**
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2, uniqueness, for finite potentials). Let
`ψ₀` be convex with `∫ e^{-ψ₀} = 1` whose gradient pushes `e^{-ψ₀(x)} dx` forward to `μ`, carried
by the closed ball of radius `R`. A convex `ψ₁` with `∫ e^{-ψ₁} = 1` has the same moment measure
`μ` if and only if `ψ₁ = ψ₀(· − y₀)` for some `y₀`. -/
theorem map_gradient_eq_iff_exists_eq_translate {ψ₀ ψ₁ : E → ℝ} (hψ₀ : ConvexOn ℝ univ ψ₀)
    (hψ₁ : ConvexOn ℝ univ ψ₁) (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hm₀ : ((volume : Measure E).tilted (-ψ₀)).map (gradient ψ₀) = μ) {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ((volume : Measure E).tilted (-ψ₁)).map (gradient ψ₁) = μ ↔
      ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  refine ⟨fun hm₁ => exists_eq_translate_of_map_gradient_eq hψ₀ hψ₁ hn₀ hn₁ hm₀ hm₁ hR, ?_⟩
  rintro ⟨y₀, hy₀⟩
  have hψ : ψ₁ = fun x => ψ₀ (x + -y₀) := funext fun x => by rw [hy₀, sub_eq_add_neg]
  have h := (translate_moment_potential_of_normalized hn₀ μ hm₀ (-y₀)).2.1
  rw [hψ]
  exact h

end Translation

end FunctionalInequalities.Probability.MomentMeasure

end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation (measurable_gradient)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Midpoint mass bound** (CEK Theorem 2, uniqueness step, (36)–(37)): for two normalized convex
potentials with the same moment measure, the midpoint density has total mass at most `1`. -/
private theorem lintegral_midpointDensity_le_one_of_map_gradient {ψ₀ ψ₁ : E → ℝ}
    (hψ₀ : ConvexOn ℝ univ ψ₀) (hψ₁ : ConvexOn ℝ univ ψ₁)
    (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hm₀ : ((volume : Measure E).tilted (-ψ₀)).map (gradient ψ₀) = μ)
    (hm₁ : ((volume : Measure E).tilted (-ψ₁)).map (gradient ψ₁) = μ) :
    ∫⁻ y, midpointDensity ψ₀ ψ₁ y ∂(volume : Measure E) ≤ 1 := by
  set C₀ : E → ℝ := fun p => (legendre (fun x => (ψ₀ x : EReal)) p).toReal with hC₀
  set C₁ : E → ℝ := fun p => (legendre (fun x => (ψ₁ x : EReal)) p).toReal with hC₁
  have hmC₀ : Measurable C₀ := measurable_legendre_toReal ψ₀
  have hmC₁ : Measurable C₁ := measurable_legendre_toReal ψ₁
  have hi₀ : Integrable C₀ μ := integrable_legendre_toReal hψ₀ hn₀ hm₀
  have hi₁ : Integrable C₁ μ := integrable_legendre_toReal hψ₁ hn₁ hm₁
  have hc₁ : Continuous ψ₁ := continuousOn_univ.mp (hψ₁.continuousOn isOpen_univ)
  have hD₀ : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ₀ w := by
    filter_upwards [hψ₀.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hD₁ : ∀ᵐ w ∂(volume : Measure E), DifferentiableAt ℝ ψ₁ w := by
    filter_upwards [hψ₁.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    exact hw (mem_univ w)
  have hmid := measurable_midpointDensity ψ₀ hc₁
  -- maximality at `ψ₀` with `h = (ψ₁* − ψ₀*)/2`
  have hI₀ := lintegral_le_exp_integral_of_map_gradient_of_integrable hψ₀ hn₀ hm₀
    (h := fun p => (C₁ p - C₀ p) / 2) ((hmC₁.sub hmC₀).div_const 2) ((hi₁.sub hi₀).div_const 2)
    hmid (by
      filter_upwards [hD₀, ae_legendre_gradient_ne_top hn₀ hψ₁ hm₀ hm₁] with w hw hfin
      intro y
      have hfin₀ : legendre (fun x => (ψ₀ x : EReal)) (gradient ψ₀ w) ≠ ⊤ := by
        rw [legendre_gradient hψ₀ hw]; exact EReal.coe_ne_top _
      refine (midpointDensity_le_of_legendre ψ₀ ψ₁ hfin₀ hfin y).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))
      have hC : C₀ (gradient ψ₀ w) = ⟪w, gradient ψ₀ w⟫ - ψ₀ w := by
        simp only [hC₀, legendre_gradient hψ₀ hw, EReal.toReal_coe]
      simp only [hC₀, hC₁] at hC ⊢
      rw [hC, inner_sub_right, real_inner_comm (gradient ψ₀ w) w]
      ring)
  -- maximality at `ψ₁` with `h = (ψ₀* − ψ₁*)/2`
  have hI₁ := lintegral_le_exp_integral_of_map_gradient_of_integrable hψ₁ hn₁ hm₁
    (h := fun p => (C₀ p - C₁ p) / 2) ((hmC₀.sub hmC₁).div_const 2) ((hi₀.sub hi₁).div_const 2)
    hmid (by
      filter_upwards [hD₁, ae_legendre_gradient_ne_top hn₁ hψ₀ hm₁ hm₀] with w hw hfin
      intro y
      have hfin₁ : legendre (fun x => (ψ₁ x : EReal)) (gradient ψ₁ w) ≠ ⊤ := by
        rw [legendre_gradient hψ₁ hw]; exact EReal.coe_ne_top _
      refine (midpointDensity_le_of_legendre ψ₀ ψ₁ hfin hfin₁ y).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))
      have hC : C₁ (gradient ψ₁ w) = ⟪w, gradient ψ₁ w⟫ - ψ₁ w := by
        simp only [hC₁, legendre_gradient hψ₁ hw, EReal.toReal_coe]
      simp only [hC₀, hC₁] at hC ⊢
      rw [hC, inner_sub_right, real_inner_comm (gradient ψ₁ w) w]
      ring)
  have hneg : ∫ p, (C₀ p - C₁ p) / 2 ∂μ = -∫ p, (C₁ p - C₀ p) / 2 ∂μ := by
    rw [← integral_neg]
    congr 1
    funext p
    ring
  rw [hneg] at hI₁
  rcases le_total (∫ p, (C₁ p - C₀ p) / 2 ∂μ) 0 with h | h
  · refine hI₀.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr h)
  · refine hI₁.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by linarith))

/-- **Uniqueness of finite moment potentials, arbitrary moment measure**
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2, uniqueness up to translation; Letwin
arXiv:2607.24164v1, Lemma 2.1). Let `ψ₀, ψ₁` be convex functions on a finite-dimensional real
inner-product space with `∫ e^{-ψᵢ} = 1`, whose gradients push `e^{-ψᵢ(x)} dx` forward to the same
measure `μ`. Then `ψ₁ = ψ₀(· − y₀)` for some `y₀`. No assumption is made on the support or the
moments of `μ`. -/
theorem exists_eq_translate_of_map_gradient_eq_unbounded {ψ₀ ψ₁ : E → ℝ}
    (hψ₀ : ConvexOn ℝ univ ψ₀) (hψ₁ : ConvexOn ℝ univ ψ₁)
    (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hm₀ : ((volume : Measure E).tilted (-ψ₀)).map (gradient ψ₀) = μ)
    (hm₁ : ((volume : Measure E).tilted (-ψ₁)).map (gradient ψ₁) = μ) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) :=
  exists_eq_translate_of_lintegral_midpointDensity_le_one hψ₀ hψ₁ hn₀ hn₁
    (lintegral_midpointDensity_le_one_of_map_gradient hψ₀ hψ₁ hn₀ hn₁ hm₀ hm₁)

/-- **Finite moment potentials of a measure, all of them** (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, Theorem 2, uniqueness, for finite potentials and an arbitrary moment measure).
Let `ψ₀` be convex with `∫ e^{-ψ₀} = 1` whose gradient pushes `e^{-ψ₀(x)} dx` forward to `μ`. A
convex `ψ₁` with `∫ e^{-ψ₁} = 1` has the same moment measure `μ` if and only if
`ψ₁ = ψ₀(· − y₀)` for some `y₀`. -/
theorem map_gradient_eq_iff_exists_eq_translate_unbounded {ψ₀ ψ₁ : E → ℝ}
    (hψ₀ : ConvexOn ℝ univ ψ₀) (hψ₁ : ConvexOn ℝ univ ψ₁)
    (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1) {μ : Measure E}
    (hm₀ : ((volume : Measure E).tilted (-ψ₀)).map (gradient ψ₀) = μ) :
    ((volume : Measure E).tilted (-ψ₁)).map (gradient ψ₁) = μ ↔
      ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  refine ⟨fun hm₁ => exists_eq_translate_of_map_gradient_eq_unbounded hψ₀ hψ₁ hn₀ hn₁ hm₀ hm₁, ?_⟩
  rintro ⟨y₀, hy₀⟩
  have hψ : ψ₁ = fun x => ψ₀ (x + -y₀) := funext fun x => by rw [hy₀, sub_eq_add_neg]
  have h := (translate_moment_potential_of_normalized hn₀ μ hm₀ (-y₀)).2.1
  rw [hψ]
  exact h

end FunctionalInequalities.Probability.MomentMeasure
