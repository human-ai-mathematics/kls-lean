import FunctionalInequalities.Probability.MomentMeasure.Maximality.Finite
import FunctionalInequalities.Probability.Line.Haar
import FunctionalInequalities.Probability.Line.PrekopaEquality
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Equality in the midpoint Prékopa–Leindler inequality for log-concave densities

For convex `ψ₀, ψ₁ : E → ℝ` on a finite-dimensional real inner-product space, the midpoint density
`midpointDensity ψ₀ ψ₁ y = sup_a exp(−(ψ₀(a) + ψ₁(2y − a))/2)` satisfies
`ρ½((x + y)/2) ≥ √(e^{-ψ₀(x)} e^{-ψ₁(y)})` (`le_midpointDensity`), so Prékopa–Leindler gives
`∫ ρ½ ≥ (∫ e^{-ψ₀})^{1/2} (∫ e^{-ψ₁})^{1/2}`. The equality case
`exists_eq_translate_of_lintegral_midpointDensity_le_one`: if `∫ e^{-ψ₀} = ∫ e^{-ψ₁} = 1` and
`∫ ρ½ ≤ 1`, then `ψ₁ = ψ₀(· − y₀)` for some `y₀` (Dubuc's characterization of equality in
Prékopa's inequality, as used by Cordero-Erausquin–Klartag, *Moment measures*,
arXiv:1304.0630v1, proof of Theorem 2, uniqueness).

Proof:

* for each unit vector `θ`, Prékopa–Leindler on the hyperplane `θ^⊥` makes the marginal densities
  along `θ` satisfy the one-dimensional midpoint inequality with equal masses, so by the
  one-dimensional equality case (`Probability.Line.exists_eq_comp_sub_of_midpoint_le`) the
  marginal of `ψ₁` is a translate of that of `ψ₀`;
* comparing barycenters, the shift is `⟪θ, b₁ − b₀⟫`; by the Cramér–Wold device
  (`Measure.ext_of_charFunDual`) `e^{-ψ₁} dx` is the translate of `e^{-ψ₀} dx` by `b₁ − b₀`, and
  continuity of the densities gives the pointwise identity.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Midpoint

/-- The midpoint density `ρ½(y) = sup_a exp(−(ψ₀ a + ψ₁ (2y − a))/2)` of two potentials: the least
function with `ρ½((x + y)/2) ≥ √(e^{-ψ₀(x)} e^{-ψ₁(y)})` for all `x, y` (`le_midpointDensity`). -/
def midpointDensity (ψ₀ ψ₁ : E → ℝ) (y : E) : ℝ≥0∞ :=
  ⨆ a : E, ENNReal.ofReal (Real.exp (-(ψ₀ a + ψ₁ ((2 : ℝ) • y - a)) / 2))

omit [FiniteDimensional ℝ E] in
/-- The midpoint density is lower semicontinuous, hence Borel, when `ψ₁` is continuous. -/
theorem measurable_midpointDensity (ψ₀ : E → ℝ) {ψ₁ : E → ℝ}
    (h₁ : Continuous ψ₁) : Measurable (midpointDensity ψ₀ ψ₁) := by
  refine (lowerSemicontinuous_iSup fun a => ?_).measurable
  refine Continuous.lowerSemicontinuous ?_
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (((continuous_const.add (h₁.comp ((continuous_const.smul continuous_id).sub
      continuous_const))).neg).div_const _))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Prékopa–Leindler condition with exponent `1/2`:
`(e^{-ψ₀(x)})^{1/2} (e^{-ψ₁(y)})^{1/2} ≤ ρ½((x + y)/2)`. -/
theorem le_midpointDensity (ψ₀ ψ₁ : E → ℝ) (x y : E) :
    ENNReal.ofReal (Real.exp (-ψ₀ x)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (Real.exp (-ψ₁ y)) ^ (1 - 1 / 2 : ℝ) ≤
      midpointDensity ψ₀ ψ₁ ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) := by
  refine le_trans (le_of_eq ?_) (le_iSup _ x)
  have hy : (2 : ℝ) • ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y) - x = y := by module
  rw [hy, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 2
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Upper bound of the midpoint density through the conjugates at one dual point `p`:
`ρ½(y) ≤ exp((ψ₀*(p) + ψ₁*(p))/2 − ⟪p, y⟫)` when both conjugates are finite at `p`. -/
theorem midpointDensity_le_of_legendre (ψ₀ ψ₁ : E → ℝ) {p : E}
    (h₀ : legendre (fun x => (ψ₀ x : EReal)) p ≠ ⊤)
    (h₁ : legendre (fun x => (ψ₁ x : EReal)) p ≠ ⊤) (y : E) :
    midpointDensity ψ₀ ψ₁ y ≤ ENNReal.ofReal (Real.exp
      (((legendre (fun x => (ψ₀ x : EReal)) p).toReal +
        (legendre (fun x => (ψ₁ x : EReal)) p).toReal) / 2 - ⟪p, y⟫)) := by
  refine iSup_le fun a => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have ha := inner_sub_le_legendre_toReal h₀ a
  have hb := inner_sub_le_legendre_toReal h₁ ((2 : ℝ) • y - a)
  rw [inner_sub_left, real_inner_smul_left, real_inner_comm p y] at hb
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Linear decay of the midpoint density from a common linear lower bound. -/
private theorem midpointDensity_le_exp {ψ₀ ψ₁ : E → ℝ} {c b : ℝ} (hc : 0 ≤ c)
    (h₀ : ∀ x, c * ‖x‖ + b ≤ ψ₀ x) (h₁ : ∀ x, c * ‖x‖ + b ≤ ψ₁ x) (y : E) :
    midpointDensity ψ₀ ψ₁ y ≤ ENNReal.ofReal (Real.exp (-(c * ‖y‖ + b))) := by
  refine iSup_le fun a => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have htri : ‖(2 : ℝ) • y‖ ≤ ‖a‖ + ‖(2 : ℝ) • y - a‖ := by
    simpa only [add_sub_cancel] using norm_add_le a ((2 : ℝ) • y - a)
  rw [norm_smul, Real.norm_two] at htri
  have := mul_le_mul_of_nonneg_left htri hc
  have ha := h₀ a
  have hb := h₁ ((2 : ℝ) • y - a)
  linarith

end Midpoint

section Marginal

private theorem integrable_exp_neg_mul_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (m : Measure F)
    [m.IsAddHaarMeasure] {a : ℝ} (ha : 0 < a) :
    Integrable (fun x => Real.exp (-(a * ‖x‖))) m := by
  simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_exp_neg_mul_norm m ha 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem inner_coe_add_smul {θ : E} (hθ : ‖θ‖ = 1) (z : (ℝ ∙ θ)ᗮ) (s : ℝ) :
    ⟪θ, (z : E) + s • θ⟫ = s := by
  rw [inner_add_right, Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hθ]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_coe_le_norm_add_smul (θ : E) (z : (ℝ ∙ θ)ᗮ) (s : ℝ) :
    ‖z‖ ≤ ‖(z : E) + s • θ‖ := by
  have hz : ⟪(z : E), s • θ⟫ = 0 := by
    rw [real_inner_smul_right, real_inner_comm,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2, mul_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hz
  have hzn : ‖z‖ = ‖(z : E)‖ := rfl
  rw [hzn]
  nlinarith [norm_nonneg ((z : E) + s • θ), norm_nonneg (z : E), norm_nonneg (s • θ)]

omit [FiniteDimensional ℝ E] in
private theorem measurable_slice (θ : E) {G : E → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun q : ℝ × (ℝ ∙ θ)ᗮ => G ((q.2 : E) + q.1 • θ) :=
  hG.comp ((continuous_subtype_val.comp continuous_snd).add
    (continuous_fst.smul continuous_const)).measurable

/-- Fubini along the line `ℝ θ`, with the slice integral inside. -/
private theorem lintegral_lintegral_slice {θ : E} {c : ℝ≥0∞}
    (hc : ∀ G : E → ℝ≥0∞, Measurable G → c * ∫⁻ x, G x ∂(volume : Measure E) =
      ∫⁻ z : (ℝ ∙ θ)ᗮ, ∫⁻ s : ℝ, G ((z : E) + s • θ) ∂(volume : Measure ℝ)
        ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ))
    {G : E → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ s : ℝ, ∫⁻ z : (ℝ ∙ θ)ᗮ, G ((z : E) + s • θ) ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) =
      c * ∫⁻ x, G x ∂(volume : Measure E) := by
  rw [hc G hG]
  exact lintegral_lintegral_swap (measurable_slice θ hG).aemeasurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exp_neg_slice_le {ψ : E → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hb : ∀ x, a * ‖x‖ + b ≤ ψ x) (θ : E) (s : ℝ) (z : (ℝ ∙ θ)ᗮ) :
    Real.exp (-ψ ((z : E) + s • θ)) ≤ Real.exp (-b) * Real.exp (-(a * ‖z‖)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 := hb ((z : E) + s • θ)
  have h2 := mul_le_mul_of_nonneg_left (norm_coe_le_norm_add_smul θ z s) ha
  linarith

private theorem integrable_slice {ψ : E → ℝ} (hc : Continuous ψ) {a b : ℝ} (ha : 0 < a)
    (hb : ∀ x, a * ‖x‖ + b ≤ ψ x) (θ : E) (s : ℝ) :
    Integrable (fun z : (ℝ ∙ θ)ᗮ => Real.exp (-ψ ((z : E) + s • θ)))
      (Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) := by
  refine ((integrable_exp_neg_mul_norm _ ha).const_mul (Real.exp (-b))).mono' ?_
    (Eventually.of_forall fun z => ?_)
  · exact (Real.continuous_exp.comp ((hc.comp (continuous_subtype_val.add
      continuous_const)).neg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_slice_le ha.le hb θ s z

private theorem continuous_slice {ψ : E → ℝ} (hc : Continuous ψ) {a b : ℝ} (ha : 0 < a)
    (hb : ∀ x, a * ‖x‖ + b ≤ ψ x) (θ : E) :
    Continuous fun s : ℝ => ∫ z : (ℝ ∙ θ)ᗮ, Real.exp (-ψ ((z : E) + s • θ))
      ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) := by
  refine continuous_of_dominated (fun s => (integrable_slice hc ha hb θ s).aestronglyMeasurable)
    (fun s => Eventually.of_forall fun z => ?_)
    ((integrable_exp_neg_mul_norm _ ha).const_mul (Real.exp (-b)))
    (Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_slice_le ha.le hb θ s z
  · exact Real.continuous_exp.comp ((hc.comp (continuous_const.add
      (continuous_id.smul continuous_const))).neg)

private theorem integral_slice_pos {ψ : E → ℝ} (hc : Continuous ψ) {a b : ℝ} (ha : 0 < a)
    (hb : ∀ x, a * ‖x‖ + b ≤ ψ x) (θ : E) (s : ℝ) :
    0 < ∫ z : (ℝ ∙ θ)ᗮ, Real.exp (-ψ ((z : E) + s • θ))
      ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) := by
  rw [integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le)
    (integrable_slice hc ha hb θ s)]
  have hs : Function.support (fun z : (ℝ ∙ θ)ᗮ => Real.exp (-ψ ((z : E) + s • θ))) = univ :=
    Set.eq_univ_of_forall fun z => (Real.exp_pos _).ne'
  rw [hs]
  exact isOpen_univ.measure_pos _ univ_nonempty

private theorem ofReal_integral_slice {ψ : E → ℝ} (hc : Continuous ψ) {a b : ℝ} (ha : 0 < a)
    (hb : ∀ x, a * ‖x‖ + b ≤ ψ x) (θ : E) (s : ℝ) :
    ENNReal.ofReal (∫ z : (ℝ ∙ θ)ᗮ, Real.exp (-ψ ((z : E) + s • θ))
      ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ)) =
      ∫⁻ z : (ℝ ∙ θ)ᗮ, ENNReal.ofReal (Real.exp (-ψ ((z : E) + s • θ)))
        ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) :=
  ofReal_integral_eq_lintegral_ofReal (integrable_slice hc ha hb θ s)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)

private theorem tilted_eq_withDensity {ψ : E → ℝ}
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) :
    (volume : Measure E).tilted (-ψ) =
      (volume : Measure E).withDensity fun x => ENNReal.ofReal (Real.exp (-ψ x)) := by
  simp only [Measure.tilted, Pi.neg_apply, hnorm, div_one]

private theorem lintegral_ofReal_exp_neg {ψ : E → ℝ}
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-ψ x)) ∂(volume : Measure E) = 1 := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => (Real.exp_pos _).le), hnorm, ENNReal.ofReal_one]

/-- The projection of `e^{-ψ} dx` on the line `ℝ θ` has density `c⁻¹ · M` where `M` is the
marginal along `θ`. -/
private theorem mul_map_inner_apply {ψ : E → ℝ} (hψc : Continuous ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) {a b : ℝ} (ha : 0 < a)
    (hb : ∀ x, a * ‖x‖ + b ≤ ψ x) {θ : E} (hθ : ‖θ‖ = 1) {c : ℝ≥0∞}
    (hc : ∀ G : E → ℝ≥0∞, Measurable G → c * ∫⁻ x, G x ∂(volume : Measure E) =
      ∫⁻ z : (ℝ ∙ θ)ᗮ, ∫⁻ s : ℝ, G ((z : E) + s • θ) ∂(volume : Measure ℝ)
        ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    c * (((volume : Measure E).tilted (-ψ)).map fun x => ⟪θ, x⟫) A =
      ∫⁻ s in A, ENNReal.ofReal (∫ z : (ℝ ∙ θ)ᗮ, Real.exp (-ψ ((z : E) + s • θ))
        ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ)) := by
  have hL : Measurable fun x : E => ⟪θ, x⟫ := (continuous_const.inner continuous_id).measurable
  have hB : MeasurableSet ((fun x : E => ⟪θ, x⟫) ⁻¹' A) := hL hA
  have hf : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hψc.measurable.neg)
  rw [Measure.map_apply hL hA, tilted_eq_withDensity hnorm, withDensity_apply _ hB,
    ← lintegral_indicator hB, ← lintegral_lintegral_slice hc (hf.indicator hB),
    ← lintegral_indicator hA]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ A
  · rw [Set.indicator_of_mem hs, ofReal_integral_slice hψc ha hb θ s]
    refine lintegral_congr fun z => ?_
    rw [Set.indicator_of_mem]
    simp only [Set.mem_preimage, inner_coe_add_smul hθ, hs]
  · rw [Set.indicator_of_notMem hs]
    refine (lintegral_congr fun z => ?_).trans lintegral_zero
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_preimage, inner_coe_add_smul hθ, hs, not_false_eq_true]

end Marginal

section Projection

/-- **Equality of marginals up to a shift.** Under the hypotheses of
`exists_eq_translate_of_lintegral_midpointDensity_le_one`, for every unit vector `θ` the law of
`⟪θ, X⟫` under `e^{-ψ₁} dx` is the law of `⟪θ, X⟫ + κ` under `e^{-ψ₀} dx` for some `κ` (slice
Prékopa–Leindler and the one-dimensional equality case). -/
private theorem exists_map_inner_eq_map_add {ψ₀ ψ₁ : E → ℝ} (hψ₀ : ConvexOn ℝ univ ψ₀)
    (hψ₁ : ConvexOn ℝ univ ψ₁) (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1)
    (hρ : ∫⁻ y, midpointDensity ψ₀ ψ₁ y ∂(volume : Measure E) ≤ 1) {θ : E} (hθ : ‖θ‖ = 1) :
    ∃ κ : ℝ, ((volume : Measure E).tilted (-ψ₁)).map (fun x => ⟪θ, x⟫) =
      (((volume : Measure E).tilted (-ψ₀)).map fun x => ⟪θ, x⟫).map (· + κ) := by
  have hint₀ : Integrable (fun x => Real.exp (-ψ₀ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hn₀]; norm_num)
  have hint₁ : Integrable (fun x => Real.exp (-ψ₁ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hn₁]; norm_num)
  have hc₀ : Continuous ψ₀ := continuousOn_univ.mp (hψ₀.continuousOn isOpen_univ)
  have hc₁ : Continuous ψ₁ := continuousOn_univ.mp (hψ₁.continuousOn isOpen_univ)
  obtain ⟨a₀, ha₀, b₀, hb₀⟩ := exists_linear_lower_bound_of_integrable_exp_neg volume hψ₀ hint₀
  obtain ⟨a₁, ha₁, b₁, hb₁⟩ := exists_linear_lower_bound_of_integrable_exp_neg volume hψ₁ hint₁
  set a := min a₀ a₁ with hadef
  set b := min b₀ b₁ with hbdef
  have ha : 0 < a := lt_min ha₀ ha₁
  have hg₀ : ∀ x, a * ‖x‖ + b ≤ ψ₀ x := fun x => by
    have := mul_le_mul_of_nonneg_right (min_le_left a₀ a₁) (norm_nonneg x)
    linarith [hb₀ x, min_le_left b₀ b₁]
  have hg₁ : ∀ x, a * ‖x‖ + b ≤ ψ₁ x := fun x => by
    have := mul_le_mul_of_nonneg_right (min_le_right a₀ a₁) (norm_nonneg x)
    linarith [hb₁ x, min_le_right b₀ b₁]
  obtain ⟨c, hc0, hctop, hc⟩ := Probability.exists_lintegral_line (volume : Measure E) hθ
  have hf₀ : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ₀ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc₀.measurable.neg)
  have hf₁ : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ₁ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hc₁.measurable.neg)
  have hmid := measurable_midpointDensity ψ₀ hc₁
  set M₀ : ℝ → ℝ := fun s => ∫ z : (ℝ ∙ θ)ᗮ, Real.exp (-ψ₀ ((z : E) + s • θ))
    ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) with hM₀
  set M₁ : ℝ → ℝ := fun s => ∫ z : (ℝ ∙ θ)ᗮ, Real.exp (-ψ₁ ((z : E) + s • θ))
    ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) with hM₁
  set S : ℝ → ℝ≥0∞ := fun s => ∫⁻ z : (ℝ ∙ θ)ᗮ, midpointDensity ψ₀ ψ₁ ((z : E) + s • θ)
    ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) with hS
  set Mh : ℝ → ℝ := fun s => (S s).toReal with hMh
  -- masses
  have hmass₀ : ∫⁻ s, ENNReal.ofReal (M₀ s) = c := by
    simp only [hM₀, ofReal_integral_slice hc₀ ha hg₀ θ]
    rw [lintegral_lintegral_slice hc hf₀, lintegral_ofReal_exp_neg hn₀, mul_one]
  have hmass₁ : ∫⁻ s, ENNReal.ofReal (M₁ s) = c := by
    simp only [hM₁, ofReal_integral_slice hc₁ ha hg₁ θ]
    rw [lintegral_lintegral_slice hc hf₁, lintegral_ofReal_exp_neg hn₁, mul_one]
  have hSmass : ∫⁻ s, S s ≤ c := by
    simp only [hS]
    rw [lintegral_lintegral_slice hc hmid]
    calc c * ∫⁻ x, midpointDensity ψ₀ ψ₁ x ∂(volume : Measure E) ≤ c * 1 :=
          mul_le_mul_right hρ c
      _ = c := mul_one c
  have hSfin : ∀ s, S s ≠ ∞ := by
    intro s
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun z => ?_)
      (((integrable_exp_neg_mul_norm (Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) ha).const_mul
        (Real.exp (-b))).lintegral_lt_top))
    refine (midpointDensity_le_exp ha.le hg₀ hg₁ _).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left (norm_coe_le_norm_add_smul θ z s) ha.le
    linarith
  have hSm : Measurable S := (measurable_slice θ hmid).lintegral_prod_right'
  -- one-dimensional hypotheses
  have hcont₀ : Continuous M₀ := continuous_slice hc₀ ha hg₀ θ
  have hcont₁ : Continuous M₁ := continuous_slice hc₁ ha hg₁ θ
  have hpos₀ : ∀ s, 0 < M₀ s := integral_slice_pos hc₀ ha hg₀ θ
  have hpos₁ : ∀ s, 0 < M₁ s := integral_slice_pos hc₁ ha hg₁ θ
  have hI₀ : Integrable M₀ := ⟨hcont₀.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => (hpos₀ s).le)).2
      (by rw [hmass₀]; exact lt_top_iff_ne_top.mpr hctop)⟩
  have hIh : Integrable Mh := ⟨hSm.ennreal_toReal.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => ENNReal.toReal_nonneg)).2
      (by
        simp only [ENNReal.ofReal_toReal (hSfin _)]
        exact lt_of_le_of_lt hSmass (lt_top_iff_ne_top.mpr hctop))⟩
  have hint₀' : ∫ s, M₀ s = c.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun s => (hpos₀ s).le)
      hcont₀.aestronglyMeasurable, hmass₀]
  have hint₁' : ∫ s, M₁ s = c.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun s => (hpos₁ s).le)
      hcont₁.aestronglyMeasurable, hmass₁]
  have hinth : ∫ s, Mh s ≤ ∫ s, M₀ s := by
    rw [hint₀', integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun s => ENNReal.toReal_nonneg) hSm.ennreal_toReal.aestronglyMeasurable]
    simp only [ENNReal.ofReal_toReal (hSfin _)]
    exact ENNReal.toReal_mono hctop hSmass
  have hfgh : ∀ x y, Real.sqrt (M₀ x * M₁ y) ≤ Mh ((x + y) / 2) := by
    intro x y
    have hPL := Analysis.lintegral_slice_prekopaLeindler (ℝ ∙ θ)ᗮ Measure.addHaar hf₀ hf₁ hmid
      (t := 1 / 2) (by norm_num) (by norm_num) (le_midpointDensity ψ₀ ψ₁) (x • θ) (y • θ)
    have harg : (1 / 2 : ℝ) • (x • θ) + (1 - 1 / 2 : ℝ) • (y • θ) = ((x + y) / 2) • θ := by
      module
    rw [harg, ← ofReal_integral_slice hc₀ ha hg₀ θ x,
      ← ofReal_integral_slice hc₁ ha hg₁ θ y] at hPL
    have h0 := (hpos₀ x).le
    have h1 := (hpos₁ y).le
    calc Real.sqrt (M₀ x * M₁ y)
        = (ENNReal.ofReal (M₀ x) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (M₁ y) ^ (1 - 1 / 2 : ℝ)).toReal := by
          rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
            ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1, Real.sqrt_eq_rpow,
            Real.mul_rpow h0 h1]
          norm_num
      _ ≤ Mh ((x + y) / 2) := ENNReal.toReal_mono (hSfin _) hPL
  obtain ⟨κ, hκ⟩ := Probability.Line.exists_eq_comp_sub_of_midpoint_le hcont₀ hcont₁ hpos₀
    hpos₁ hI₀ hIh (hint₁'.trans hint₀'.symm) hinth hfgh
  refine ⟨κ, ?_⟩
  have hL : Measurable fun x : E => ⟪θ, x⟫ := (continuous_const.inner continuous_id).measurable
  ext A hA
  have hA' : MeasurableSet ((· + κ) ⁻¹' A) := measurable_add_const κ hA
  rw [Measure.map_apply (measurable_add_const κ) hA]
  refine (ENNReal.mul_right_inj hc0 hctop).mp ?_
  rw [mul_map_inner_apply hc₁ hn₁ ha hg₁ hθ hc hA, mul_map_inner_apply hc₀ hn₀ ha hg₀ hθ hc hA']
  change ∫⁻ s in A, ENNReal.ofReal (M₁ s) = ∫⁻ s in (· + κ) ⁻¹' A, ENNReal.ofReal (M₀ s)
  simp only [hκ]
  rw [← lintegral_indicator hA, ← lintegral_indicator hA',
    ← lintegral_add_right_eq_self _ κ]
  refine lintegral_congr fun s => ?_
  by_cases hs : s + κ ∈ A
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show s ∈ (· + κ) ⁻¹' A from hs),
      add_sub_cancel_right]
  · rw [Set.indicator_of_notMem hs,
      Set.indicator_of_notMem (show s ∉ (· + κ) ⁻¹' A from hs)]

end Projection

section Translation

/-- The identity has finite first moment under `e^{-ψ} dx` for convex normalized `ψ`. -/
private theorem integrable_id_tilted {ψ : E → ℝ} (hψ : ConvexOn ℝ univ ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) :
    Integrable (fun x => x) ((volume : Measure E).tilted (-ψ)) := by
  have hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hc : Continuous ψ := continuousOn_univ.mp (hψ.continuousOn isOpen_univ)
  obtain ⟨a, ha, b, hb⟩ := exists_linear_lower_bound_of_integrable_exp_neg volume hψ hint
  rw [integrable_tilted_iff (f := -ψ) hint]
  refine ((integrable_exp_neg_mul_norm (volume : Measure E) (half_pos ha)).const_mul
    (Real.exp (-b) * (2 / a))).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((Real.continuous_exp.comp hc.neg).smul continuous_id).aestronglyMeasurable
  · simp only [Pi.neg_apply]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-ψ x) ≤ Real.exp (-b) * Real.exp (-(a * ‖x‖)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [hb x])
    have h2 : Real.exp (-(a * ‖x‖)) = Real.exp (-(a / 2 * ‖x‖)) * Real.exp (-(a / 2 * ‖x‖)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : a / 2 * ‖x‖ ≤ Real.exp (a / 2 * ‖x‖) := by
      linarith [Real.add_one_le_exp (a / 2 * ‖x‖)]
    have h4 : Real.exp (a / 2 * ‖x‖) * Real.exp (-(a / 2 * ‖x‖)) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : ‖x‖ * Real.exp (-(a / 2 * ‖x‖)) ≤ 2 / a := by
      have := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-(a / 2 * ‖x‖))).le
      rw [h4] at this
      rw [le_div_iff₀ ha]
      nlinarith
    calc Real.exp (-ψ x) * ‖x‖ ≤ Real.exp (-b) * Real.exp (-(a * ‖x‖)) * ‖x‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
      _ = Real.exp (-b) * (‖x‖ * Real.exp (-(a / 2 * ‖x‖))) * Real.exp (-(a / 2 * ‖x‖)) := by
          rw [h2]; ring
      _ ≤ Real.exp (-b) * (2 / a) * Real.exp (-(a / 2 * ‖x‖)) := by
          gcongr

/-- Translating `e^{-ψ} dx` by `d` gives the measure with density `e^{-ψ(· − d)}`. -/
private theorem map_add_tilted {ψ : E → ℝ} (hψc : Continuous ψ)
    (hnorm : ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) = 1) (d : E) :
    ((volume : Measure E).tilted (-ψ)).map (· + d) =
      (volume : Measure E).withDensity fun x => ENNReal.ofReal (Real.exp (-ψ (x - d))) := by
  have hf : Measurable fun x => ENNReal.ofReal (Real.exp (-ψ x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hψc.measurable.neg)
  ext A hA
  have hA' : MeasurableSet ((· + d) ⁻¹' A) := measurable_add_const d hA
  rw [Measure.map_apply (measurable_add_const d) hA, tilted_eq_withDensity hnorm,
    withDensity_apply _ hA', withDensity_apply _ hA, ← lintegral_indicator hA',
    ← lintegral_indicator hA]
  conv_rhs => rw [← lintegral_add_right_eq_self _ d]
  refine lintegral_congr fun x => ?_
  by_cases hx : x + d ∈ A
  · rw [Set.indicator_of_mem (show x ∈ (· + d) ⁻¹' A from hx), Set.indicator_of_mem hx,
      add_sub_cancel_right]
  · rw [Set.indicator_of_notMem (show x ∉ (· + d) ⁻¹' A from hx), Set.indicator_of_notMem hx]

/-- **Equality in the midpoint Prékopa–Leindler inequality for log-concave densities** (Dubuc,
in the form used by Cordero-Erausquin–Klartag arXiv:1304.0630v1, proof of Theorem 2, uniqueness).
Let `ψ₀, ψ₁` be convex functions on a finite-dimensional real inner-product space with
`∫ e^{-ψ₀} = ∫ e^{-ψ₁} = 1`. If the midpoint density has `∫ ρ½ ≤ 1` (Prékopa–Leindler always gives
`≥ 1`), then `ψ₁ = ψ₀(· − y₀)` for some `y₀`. -/
theorem exists_eq_translate_of_lintegral_midpointDensity_le_one {ψ₀ ψ₁ : E → ℝ}
    (hψ₀ : ConvexOn ℝ univ ψ₀) (hψ₁ : ConvexOn ℝ univ ψ₁)
    (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure E) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure E) = 1)
    (hρ : ∫⁻ y, midpointDensity ψ₀ ψ₁ y ∂(volume : Measure E) ≤ 1) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  have hint₀ : Integrable (fun x => Real.exp (-ψ₀ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hn₀]; norm_num)
  have hint₁ : Integrable (fun x => Real.exp (-ψ₁ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hn₁]; norm_num)
  have hc₀ : Continuous ψ₀ := continuousOn_univ.mp (hψ₀.continuousOn isOpen_univ)
  have hc₁ : Continuous ψ₁ := continuousOn_univ.mp (hψ₁.continuousOn isOpen_univ)
  have hP₀ : IsProbabilityMeasure ((volume : Measure E).tilted (-ψ₀)) :=
    isProbabilityMeasure_tilted hint₀
  have hP₁ : IsProbabilityMeasure ((volume : Measure E).tilted (-ψ₁)) :=
    isProbabilityMeasure_tilted hint₁
  set ν₀ := (volume : Measure E).tilted (-ψ₀) with hν₀
  set ν₁ := (volume : Measure E).tilted (-ψ₁) with hν₁
  have hid₀ := integrable_id_tilted hψ₀ hn₀
  have hid₁ := integrable_id_tilted hψ₁ hn₁
  set d : E := (∫ x, x ∂ν₁) - ∫ x, x ∂ν₀ with hd
  have hPd : IsProbabilityMeasure (ν₀.map (· + d)) :=
    Measure.isProbabilityMeasure_map (measurable_add_const d).aemeasurable
  -- every one-dimensional projection of `ν₁` is that of the translate of `ν₀`
  have hproj : ∀ θ : E, ‖θ‖ = 1 →
      ν₁.map (fun x => ⟪θ, x⟫) = (ν₀.map (· + d)).map (fun x => ⟪θ, x⟫) := by
    intro θ hθ
    have hL : Measurable fun x : E => ⟪θ, x⟫ :=
      (continuous_const.inner continuous_id).measurable
    obtain ⟨κ, hκ⟩ := exists_map_inner_eq_map_add hψ₀ hψ₁ hn₀ hn₁ hρ hθ
    have hmean₁ : ∫ s, s ∂(ν₁.map fun x => ⟪θ, x⟫) = ⟪θ, ∫ x, x ∂ν₁⟫ := by
      rw [integral_map (f := fun s : ℝ => s) hL.aemeasurable measurable_id'.aestronglyMeasurable]
      exact integral_inner hid₁ θ
    have hmean₀ : ∫ s, s ∂((ν₀.map fun x => ⟪θ, x⟫).map (· + κ)) = ⟪θ, ∫ x, x ∂ν₀⟫ + κ := by
      rw [integral_map (f := fun s : ℝ => s) (measurable_add_const κ).aemeasurable
          measurable_id'.aestronglyMeasurable,
        integral_map hL.aemeasurable (measurable_add_const κ).aestronglyMeasurable,
        integral_add (hid₀.const_inner θ) (integrable_const κ), integral_inner hid₀ θ,
        integral_const, probReal_univ, one_smul]
    have hκd : κ = ⟪θ, d⟫ := by
      rw [hκ] at hmean₁
      rw [hd, inner_sub_right]
      linarith
    rw [hκ, Measure.map_map hL (measurable_add_const d),
      Measure.map_map (measurable_add_const κ) hL]
    congr 1
    funext x
    simp only [Function.comp_apply, inner_add_right, hκd]
  -- Cramér–Wold
  have hall : ∀ L : StrongDual ℝ E, ν₁.map L = (ν₀.map (· + d)).map L := by
    intro L
    set v := (InnerProductSpace.toDual ℝ E).symm L with hv
    have hLv : ∀ x, L x = ⟪v, x⟫ := fun x => (InnerProductSpace.toDual_symm_apply).symm
    by_cases hv0 : v = 0
    · have hL0 : (L : E → ℝ) = fun _ => 0 := funext fun x => by rw [hLv, hv0, inner_zero_left]
      rw [hL0, Measure.map_const, Measure.map_const, measure_univ, measure_univ]
    · set θ : E := ‖v‖⁻¹ • v with hθdef
      have hθ : ‖θ‖ = 1 := norm_smul_inv_norm hv0
      have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      have hLθ : (L : E → ℝ) = (fun r => ‖v‖ * r) ∘ fun x => ⟪θ, x⟫ := by
        funext x
        simp only [Function.comp_apply, hLv, hθdef, real_inner_smul_left]
        field_simp
      have hL : Measurable fun x : E => ⟪θ, x⟫ :=
        (continuous_const.inner continuous_id).measurable
      rw [hLθ, ← Measure.map_map (measurable_const_mul _) hL,
        ← Measure.map_map (measurable_const_mul _) hL, hproj θ hθ]
  have hν : ν₁ = ν₀.map (· + d) := Measure.ext_of_charFunDual (funext fun L => by
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hall L])
  rw [hν₁, tilted_eq_withDensity hn₁, hν₀, map_add_tilted hc₀ hn₀ d] at hν
  have hcont₁ : Continuous fun x => ENNReal.ofReal (Real.exp (-ψ₁ x)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc₁.neg)
  have hcont₀ : Continuous fun x => ENNReal.ofReal (Real.exp (-ψ₀ (x - d))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (hc₀.comp (continuous_id.sub continuous_const)).neg)
  have hae := (withDensity_eq_iff_of_sigmaFinite hcont₁.measurable.aemeasurable
    hcont₀.measurable.aemeasurable).mp hν
  have heq := (Continuous.ae_eq_iff_eq (volume : Measure E) hcont₁ hcont₀).mp hae
  refine ⟨d, fun y => ?_⟩
  have hy := congrFun heq y
  rw [ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le] at hy
  have := Real.exp_injective hy
  linarith

end Translation

end FunctionalInequalities.Probability.MomentMeasure
