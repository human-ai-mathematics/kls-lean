import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.Finite
import FunctionalInequalities.Probability.MomentMeasure.FirstVariation
import FunctionalInequalities.Analysis.Convex.EssentialContinuity

/-!
# Uniqueness of essentially continuous moment potentials with bounded-support moment measure

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Theorem 2, uniqueness up to
translation (= Letwin arXiv:2607.24164v1, Lemma 2.1, uniqueness), for probability measures `μ`
carried by a closed ball, among the potentials of the source: convex `ψ : E → ℝ ∪ {+∞}` that are
essentially continuous (CEK Definition 2, `Analysis.EssentiallyContinuous`) with moment measure
`ofPotential volume ψ = μ`, the push-forward of `e^{-ψ(x)} dx` under `∇ψ`.

* `ofPotential_coe_eq_map_gradient`: for a real potential `φ` with `∫ e^{-φ} = 1`, the
  extended-real moment measure of `φ` is `(∇φ)_*(e^{-φ} dx)`, the real form used for finite
  potentials.
* `exists_eq_coe_of_ofPotential_eq`: such a `ψ` is finite everywhere; its real version `φ` is
  convex, `R`-Lipschitz, normalized (`∫ e^{-φ} = 1`, from `μ(E) = 1`) and has
  `(∇φ)_*(e^{-φ} dx) = μ`.
* `exists_eq_translate_of_ofPotential_eq`,
  `exists_eq_translate_of_ofPotential_eq_of_map_gradient_eq` and
  `ofPotential_eq_iff_exists_eq_translate`: any two such potentials, or one such potential and a
  finite convex normalized potential with moment measure `μ`, differ by a translation, and every
  translate is again a moment potential of `μ`.

Proof: finiteness and the Lipschitz bound are `Analysis.ConvexPotential.ne_top_of_map_gradient`;
the finite potentials are then compared by `exists_eq_translate_of_map_gradient_eq`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation (measurable_gradient)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- For a real potential `φ` with `∫ e^{-φ} = 1`, the extended-real moment measure of `φ` is the
push-forward of the probability measure `e^{-φ(x)} dx` under `∇φ`. No convexity is needed. -/
theorem ofPotential_coe_eq_map_gradient {φ : E → ℝ}
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1) :
    ofPotential volume (fun x => (φ x : EReal)) =
      ((volume : Measure E).tilted (-φ)).map (gradient φ) := by
  have hφ : (fun x => ((φ x : EReal)).toReal) = φ := funext fun x => EReal.toReal_coe (φ x)
  have hw : weightedMeasure volume (fun x => (φ x : EReal)) = (volume : Measure E).tilted (-φ) := by
    simp only [weightedMeasure, Measure.tilted, Pi.neg_apply, hnorm, div_one]
    congr 1
  rw [ofPotential, hφ, hw]

/-- **Essentially continuous moment potentials of bounded-support laws are finite.** Let `μ` be a
probability measure with `‖y‖ ≤ R` for `μ`-a.e. `y`, and `ψ : E → ℝ ∪ {+∞}` convex and
essentially continuous (CEK arXiv:1304.0630v1, Definition 2) with moment measure
`ofPotential volume ψ = μ`. Then `ψ` is finite: `ψ = φ` for a real `φ` that is convex,
`R`-Lipschitz, normalized, `∫ e^{-φ} = 1`, and satisfies `(∇φ)_*(e^{-φ} dx) = μ`. -/
theorem exists_eq_coe_of_ofPotential_eq {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : ofPotential volume ψ = μ) {R : ℝ} (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ConvexOn ℝ univ φ ∧ LipschitzWith (Real.toNNReal R) φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = μ := by
  have hball : ∀ᵐ y ∂μ, y ∈ closedBall (0 : E) (Real.toNNReal R) :=
    hR.mono fun y hy => by
      rw [mem_closedBall_zero_iff]
      exact hy.trans (Real.le_coe_toNNReal R)
  have hμ0 : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  obtain ⟨hfin, hlip⟩ := hψ.ne_top_of_map_gradient hess hμ hμ0 (mem_ae_iff.mp hball)
  set φ : E → ℝ := fun x => (ψ x).toReal with hφdef
  have hcoe : ∀ x, ψ x = φ x := fun x => (EReal.coe_toReal (hfin x) (hψ.1 x)).symm
  have hψφ : ψ = fun x => (φ x : EReal) := funext hcoe
  have hdom : {x | ψ x ≠ ⊤} = univ := eq_univ_of_forall hfin
  have hconv : ConvexOn ℝ univ φ := by
    have h := hψ.convexOn_toReal
    rwa [hdom] at h
  -- normalization from the total mass
  have hmass : mass volume ψ = 1 := by
    rw [← ofPotential_univ, hμ, measure_univ]
  have hmeas : Measurable fun x => Real.exp (-φ x) :=
    Real.continuous_exp.measurable.comp hlip.continuous.measurable.neg
  have hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
      hmeas.aestronglyMeasurable]
    have hl : (∫⁻ x, ENNReal.ofReal (Real.exp (-φ x)) ∂(volume : Measure E)) = 1 := by
      rw [← hmass, mass, hψφ]
      refine lintegral_congr fun x => ?_
      rw [density, ← EReal.coe_neg, EReal.exp_coe]
    rw [hl, ENNReal.toReal_one]
  refine ⟨φ, hcoe, hconv, hlip, hnorm, ?_⟩
  rw [← ofPotential_coe_eq_map_gradient hnorm, ← hψφ, hμ]

/-- **Essentially continuous moment potentials are unique up to translation** (CEK
arXiv:1304.0630v1, Theorem 2, uniqueness, for bounded-support laws). If `ψ₀, ψ₁ : E → ℝ ∪ {+∞}`
are convex and essentially continuous with the same moment measure `μ`, a probability measure
carried by the ball of radius `R`, then `ψ₁ = ψ₀(· − y₀)` for some `y₀`. -/
theorem exists_eq_translate_of_ofPotential_eq {ψ₀ ψ₁ : E → EReal} (hψ₀ : ConvexPotential ψ₀)
    (hess₀ : EssentiallyContinuous ψ₀) (hψ₁ : ConvexPotential ψ₁)
    (hess₁ : EssentiallyContinuous ψ₁) {μ : Measure E} [IsProbabilityMeasure μ]
    (hm₀ : ofPotential volume ψ₀ = μ) (hm₁ : ofPotential volume ψ₁ = μ) {R : ℝ}
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  obtain ⟨φ₀, hc₀, hφ₀, -, hn₀, hmap₀⟩ := exists_eq_coe_of_ofPotential_eq hψ₀ hess₀ hm₀ hR
  obtain ⟨φ₁, hc₁, hφ₁, -, hn₁, hmap₁⟩ := exists_eq_coe_of_ofPotential_eq hψ₁ hess₁ hm₁ hR
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_of_map_gradient_eq hφ₀ hφ₁ hn₀ hn₁ hmap₀ hmap₁ hR
  exact ⟨y₀, fun y => by rw [hc₁, hc₀, hy₀]⟩

/-- **An essentially continuous moment potential is a translate of any finite one** (CEK
arXiv:1304.0630v1, Theorem 2, uniqueness, for bounded-support laws). Let `φ` be convex with
`∫ e^{-φ} = 1` and `(∇φ)_*(e^{-φ} dx) = μ`, where `‖y‖ ≤ R` for `μ`-a.e. `y`. Every convex,
essentially continuous `ψ : E → ℝ ∪ {+∞}` with `ofPotential volume ψ = μ` equals `φ(· − y₀)` for
some `y₀`; in particular it is finite. -/
theorem exists_eq_translate_of_ofPotential_eq_of_map_gradient_eq {φ : E → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    {μ : Measure E} (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = μ)
    {ψ : E → EReal} (hψ : ConvexPotential ψ) (hess : EssentiallyContinuous ψ)
    (hψμ : ofPotential volume ψ = μ) {R : ℝ} (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∃ y₀ : E, ∀ y, ψ y = φ (y - y₀) := by
  have hint : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have : IsProbabilityMeasure ((volume : Measure E).tilted (-φ)) :=
    isProbabilityMeasure_tilted hint
  have : IsProbabilityMeasure μ := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map (measurable_gradient φ).aemeasurable
  obtain ⟨φ₁, hc₁, hφ₁, -, hn₁, hmap₁⟩ := exists_eq_coe_of_ofPotential_eq hψ hess hψμ hR
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_of_map_gradient_eq hφ hφ₁ hnorm hn₁ hmap hmap₁ hR
  exact ⟨y₀, fun y => by rw [hc₁, hy₀]⟩

/-- **Moment potentials of a bounded-support law, all of them** (CEK arXiv:1304.0630v1,
Theorem 2, uniqueness up to translation, for bounded-support laws). Let `ψ₀ : E → ℝ ∪ {+∞}` be
convex and essentially continuous with moment measure `μ`, a probability measure with `‖y‖ ≤ R`
for `μ`-a.e. `y`. A convex, essentially continuous `ψ₁` has moment measure `μ` if and only if
`ψ₁ = ψ₀(· − y₀)` for some `y₀`. -/
theorem ofPotential_eq_iff_exists_eq_translate {ψ₀ ψ₁ : E → EReal} (hψ₀ : ConvexPotential ψ₀)
    (hess₀ : EssentiallyContinuous ψ₀) (hψ₁ : ConvexPotential ψ₁)
    (hess₁ : EssentiallyContinuous ψ₁) {μ : Measure E} [IsProbabilityMeasure μ]
    (hm₀ : ofPotential volume ψ₀ = μ) {R : ℝ} (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ofPotential volume ψ₁ = μ ↔ ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  refine ⟨fun hm₁ => exists_eq_translate_of_ofPotential_eq hψ₀ hess₀ hψ₁ hess₁ hm₀ hm₁ hR, ?_⟩
  rintro ⟨y₀, hy₀⟩
  obtain ⟨φ₀, hc₀, -, -, hn₀, hmap₀⟩ := exists_eq_coe_of_ofPotential_eq hψ₀ hess₀ hm₀ hR
  obtain ⟨hn₁, hmap₁, -⟩ := translate_moment_potential_of_normalized hn₀ μ hmap₀ (-y₀)
  have hψ : ψ₁ = fun x => ((φ₀ (x + -y₀) : ℝ) : EReal) :=
    funext fun x => by rw [hy₀, hc₀, sub_eq_add_neg]
  rw [hψ, ofPotential_coe_eq_map_gradient hn₁]
  exact hmap₁

end FunctionalInequalities.Probability.MomentMeasure
