import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.Finite
import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.BoundedSupport
import FunctionalInequalities.Probability.MomentMeasure.Maximality.EssentiallyContinuous
import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.Maximizer
import FunctionalInequalities.KLS.CEK.GeneralExistence
import FunctionalInequalities.Analysis.Convex.Legendre.Affine

/-!
# CEK Theorem 2: uniqueness of moment potentials

## Finite potentials and an arbitrary moment measure

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Theorem 2, uniqueness up to
translation (= Letwin arXiv:2607.24164v1, Lemma 2.1, uniqueness), in the source's extended-real
formulation, for potentials that are finite everywhere (these are essentially continuous,
`Analysis.ConvexPotential.essentiallyContinuous_of_ne_top`): if `μ` is a finite nonzero Borel
measure and `ψ₀, ψ₁ : E → ℝ ∪ {+∞}` are convex, finite everywhere, with moment measure
`ofPotential volume ψᵢ = μ`, then `ψ₁ = ψ₀(· − y₀)` for some `y₀`
(`exists_eq_translate_of_ofPotential_eq_of_ne_top`). No assumption on the support, the moments or
the barycenter of `μ` is needed.

Proof: subtracting `log μ(E)` normalizes both potentials (`ofPotential_sub_const`); the real
potentials then have the same moment measure `μ / μ(E)`, and
`Probability.MomentMeasure.exists_eq_translate_of_map_gradient_eq_unbounded` applies.

Essentially continuous potentials that may take the value `+∞` are covered in the next part
(CEK Theorem 2 in full).

## Essentially continuous potentials

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Theorem 2 (= Letwin
arXiv:2607.24164v1, Lemma 2.1), in the source's extended-real formulation.

* `exists_eq_translate_of_ofPotential_eq_of_essentiallyContinuous`: if `μ` is a finite nonzero
  Borel measure and `ψ₀, ψ₁ : E → ℝ ∪ {+∞}` are convex and essentially continuous with moment
  measure `μ`, then `ψ₁ = ψ₀(· − y₀)` for some `y₀`. No assumption on the support, moments or
  barycenter of `μ` is needed.
* `exists_essentiallyContinuous_ofPotential_eq_unique`: the full Theorem 2 — under the source's
  hypotheses on `μ` (finite, nonzero, finite first moment, barycenter `0`, not supported in a proper
  subspace) there is a convex essentially continuous `ψ` with moment measure `μ`, unique up to
  translation among convex essentially continuous potentials.

Proof of uniqueness (CEK, proof of Theorem 2): after normalizing `∫ e^{-ψᵢ} = 1`, each `ψᵢ*`
maximizes `I_μ` (Theorem 8, `variationalFunctional_le_legendre`) and is `μ`-integrable
(Proposition 7, `potentialIntegrable_legendre`); two normalized maximizers have conjugates that are
translates of each other (`exists_eq_translate_legendre_of_maximizer`, the equality case of
Prékopa–Leindler), and `ψᵢ** = ψᵢ` (Fenchel–Moreau).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FunctionalInequalities.KLS.CEK

open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure

private theorem sub_coe_add_coe (a : EReal) (r : ℝ) : a - (r : EReal) + (r : EReal) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_sub, ← EReal.coe_add, sub_add_cancel]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section FinitePotential

/-- A finite convex extended-real potential with moment measure `μ` (finite, nonzero) becomes,
after adding `log μ(E)`, a normalized real convex potential whose gradient pushes `e^{-φ} dx`
forward to `μ / μ(E)`. -/
private theorem exists_normalized_of_ofPotential_eq {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {ψ : E → EReal} (hψ : ConvexPotential ψ) (hfin : ∀ x, ψ x ≠ ⊤)
    (hm : ofPotential volume ψ = μ) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) =
        ENNReal.ofReal (μ.real univ)⁻¹ • μ ∧
      ∀ x, ψ x = ((φ x - Real.log (μ.real univ) : ℝ) : EReal) := by
  set m : ℝ := μ.real univ with hmdef
  have hm0 : 0 < m := by
    rw [hmdef, measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top μ univ)
  have hdom : {x | ψ x ≠ ⊤} = univ := eq_univ_of_forall hfin
  have hconv : ConvexOn ℝ univ fun x => (ψ x).toReal := by
    have h := hψ.convexOn_toReal
    rwa [hdom] at h
  have hcont : Continuous fun x => (ψ x).toReal :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hcoe : ∀ x, ψ x = (((ψ x).toReal : ℝ) : EReal) := fun x =>
    (EReal.coe_toReal (hfin x) (hψ.1 x)).symm
  have hmeas : Measurable ψ := by
    have : ψ = fun x => (((ψ x).toReal : ℝ) : EReal) := funext hcoe
    rw [this]
    exact continuous_coe_real_ereal.measurable.comp hcont.measurable
  set φ : E → ℝ := fun x => (ψ x).toReal + Real.log m with hφdef
  have hφψ : (fun x => (φ x : EReal)) = fun y => ψ y - ((-Real.log m : ℝ) : EReal) := by
    funext y
    rw [hcoe y, ← EReal.coe_sub]
    congr 1
    simp only [hφdef, sub_neg_eq_add]
  have hexp : ENNReal.ofReal (Real.exp (-Real.log m)) = ENNReal.ofReal m⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hm0]
  have hmass : ∫⁻ x, ENNReal.ofReal (Real.exp (-φ x)) ∂(volume : Measure E) = 1 := by
    have h1 : ∫⁻ x, ENNReal.ofReal (Real.exp (-φ x)) ∂(volume : Measure E) =
        mass volume (fun x => (φ x : EReal)) := by
      refine lintegral_congr fun x => ?_
      rw [density, ← EReal.coe_neg, EReal.exp_coe]
    rw [h1, hφψ, mass_sub_const, hexp, ← ofPotential_univ, hm, ← ENNReal.ofReal_toReal
      (measure_ne_top μ univ), ← measureReal_def, ← hmdef, ← ENNReal.ofReal_mul
      (inv_nonneg.mpr hm0.le), inv_mul_cancel₀ hm0.ne', ENNReal.ofReal_one]
  have hφm : Measurable fun x => Real.exp (-φ x) :=
    Real.measurable_exp.comp (hcont.measurable.add_const _).neg
  have hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
      hφm.aestronglyMeasurable, hmass, ENNReal.toReal_one]
  refine ⟨φ, hconv.add_const _, hnorm, ?_, fun x => ?_⟩
  · rw [← ofPotential_coe_eq_map_gradient hnorm, hφψ, ofPotential_sub_const volume hψ hmeas,
      hexp, hm]
  · rw [hcoe x, hφdef]
    simp only [add_sub_cancel_right]

/-- **CEK Theorem 2, uniqueness up to translation, for finite potentials**
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2; Letwin arXiv:2607.24164v1, Lemma 2.1).
Let `μ` be a finite nonzero Borel measure on a finite-dimensional real inner-product space and let
`ψ₀, ψ₁ : E → ℝ ∪ {+∞}` be convex, finite everywhere, with moment measure `μ`: the push-forward of
`e^{-ψᵢ(x)} dx` under `∇ψᵢ` is `μ`. Then `ψ₁ = ψ₀(· − y₀)` for some `y₀`. The support of `μ` may
be unbounded; no moment or barycenter condition is needed. -/
theorem exists_eq_translate_of_ofPotential_eq_of_ne_top {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {ψ₀ ψ₁ : E → EReal} (hψ₀ : ConvexPotential ψ₀) (hψ₁ : ConvexPotential ψ₁)
    (hfin₀ : ∀ x, ψ₀ x ≠ ⊤) (hfin₁ : ∀ x, ψ₁ x ≠ ⊤)
    (hm₀ : ofPotential volume ψ₀ = μ) (hm₁ : ofPotential volume ψ₁ = μ) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  obtain ⟨φ₀, hc₀, hn₀, hmap₀, he₀⟩ := exists_normalized_of_ofPotential_eq hμ hψ₀ hfin₀ hm₀
  obtain ⟨φ₁, hc₁, hn₁, hmap₁, he₁⟩ := exists_normalized_of_ofPotential_eq hμ hψ₁ hfin₁ hm₁
  obtain ⟨y₀, hy₀⟩ :=
    exists_eq_translate_of_map_gradient_eq_unbounded hc₀ hc₁ hn₀ hn₁ hmap₀ hmap₁
  exact ⟨y₀, fun y => by rw [he₁, he₀, hy₀]⟩

end FinitePotential

section EssentiallyContinuousPotential

/-- Subtracting a real constant preserves convexity and essential continuity. -/
private theorem convexPotential_essentiallyContinuous_sub_const {ψ : E → EReal}
    (hψ : ConvexPotential ψ) (hess : EssentiallyContinuous ψ) (hne : ∃ x, ψ x ≠ ⊤) (b : ℝ) :
    ConvexPotential (fun y => ψ y - (b : EReal)) ∧
      EssentiallyContinuous (fun y => ψ y - (b : EReal)) := by
  have hbi := legendre_legendre_eq hψ hess.1 hne
  have hrepr : (fun y => ψ y - (b : EReal)) = legendre (affineSubtract (legendre ψ) 0 (-b)) := by
    funext y
    rw [legendre_affineSubtract, add_zero, hbi, sub_eq_add_neg, EReal.coe_neg]
  have hconv : ConvexPotential (fun y => ψ y - (b : EReal)) := by
    refine ⟨fun y h => ?_, ?_⟩
    · change ψ y - (b : EReal) = ⊥ at h
      rw [sub_eq_add_neg, ← EReal.coe_neg, EReal.add_eq_bot_iff] at h
      rcases h with h | h
      · exact hψ.1 y h
      · exact EReal.coe_ne_bot _ h
    · rw [hrepr]
      exact convex_epigraph_legendre _
  have hlsc : LowerSemicontinuous (fun y => ψ y - (b : EReal)) := by
    rw [hrepr]
    exact lowerSemicontinuous_legendre _
  have hdom : {y | ψ y - (b : EReal) ≠ ⊤} = {y | ψ y ≠ ⊤} := by
    ext y
    change ψ y - (b : EReal) ≠ ⊤ ↔ ψ y ≠ ⊤
    induction ψ y using EReal.rec with
    | bot => simp
    | top => simp
    | coe r => exact ⟨fun _ => EReal.coe_ne_top r, fun _ => by
        rw [← EReal.coe_sub]; exact EReal.coe_ne_top _⟩
  refine ⟨hconv, ?_⟩
  rw [hconv.essentiallyContinuous_iff, hdom]
  exact ⟨hlsc, (hψ.essentiallyContinuous_iff.mp hess).2⟩

/-- **CEK Theorem 2, uniqueness up to translation** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, Theorem 2; Letwin arXiv:2607.24164v1, Lemma 2.1). Let `μ` be a finite nonzero
Borel measure on a finite-dimensional real inner-product space and let
`ψ₀, ψ₁ : E → ℝ ∪ {+∞}` be convex and essentially continuous (CEK Definition 2) with moment
measure `μ`: the push-forward of `e^{-ψᵢ(x)} dx` under `∇ψᵢ` is `μ`. Then `ψ₁ = ψ₀(· − y₀)` for
some `y₀`, as extended-real functions on all of `E`. The support of `μ` may be unbounded and no
moment or barycenter condition is assumed. -/
theorem exists_eq_translate_of_ofPotential_eq_of_essentiallyContinuous {μ : Measure E}
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) {ψ₀ ψ₁ : E → EReal} (hψ₀ : ConvexPotential ψ₀)
    (hψ₁ : ConvexPotential ψ₁) (he₀ : EssentiallyContinuous ψ₀) (he₁ : EssentiallyContinuous ψ₁)
    (hm₀ : ofPotential volume ψ₀ = μ) (hm₁ : ofPotential volume ψ₁ = μ) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  set c : ℝ≥0∞ := μ univ with hc
  have hc0 : c ≠ 0 := (Measure.measure_univ_ne_zero).mpr hμ
  have hctop : c ≠ ⊤ := measure_ne_top μ univ
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  set b : ℝ := -Real.log c.toReal with hb
  have hexp : ENNReal.ofReal (Real.exp b) * c = 1 := by
    rw [hb, Real.exp_neg, Real.exp_log hcpos, ENNReal.ofReal_inv_of_pos hcpos,
      ENNReal.ofReal_toReal hctop, ENNReal.inv_mul_cancel hc0 hctop]
  have hmassi : ∀ {ψ : E → EReal}, ofPotential volume ψ = μ → mass volume ψ = c := fun h => by
    rw [← ofPotential_univ, h]
  have hnei : ∀ {ψ : E → EReal}, ConvexPotential ψ → ofPotential volume ψ = μ →
      ∃ x, ψ x ≠ ⊤ := fun hψ h => by
    obtain ⟨x, hx⟩ :=
      interior_domain_nonempty_of_mass_ne_zero volume hψ (by rw [hmassi h]; exact hc0)
    exact ⟨x, interior_subset hx⟩
  set ψ₀' : E → EReal := fun y => ψ₀ y - (b : EReal) with hψ₀'
  set ψ₁' : E → EReal := fun y => ψ₁ y - (b : EReal) with hψ₁'
  obtain ⟨hc₀', he₀'⟩ := convexPotential_essentiallyContinuous_sub_const hψ₀ he₀ (hnei hψ₀ hm₀) b
  obtain ⟨hc₁', he₁'⟩ := convexPotential_essentiallyContinuous_sub_const hψ₁ he₁ (hnei hψ₁ hm₁) b
  have hmass₀ : mass volume ψ₀' = 1 := by rw [hψ₀', mass_sub_const, hmassi hm₀, hexp]
  have hmass₁ : mass volume ψ₁' = 1 := by rw [hψ₁', mass_sub_const, hmassi hm₁, hexp]
  set ν : Measure E := ofPotential volume ψ₀' with hν
  have hν₁ : ofPotential volume ψ₁' = ν := by
    rw [hν, hψ₀', hψ₁', ofPotential_sub_const volume hψ₀ he₀.1.measurable,
      ofPotential_sub_const volume hψ₁ he₁.1.measurable, hm₀, hm₁]
  have hνprob : IsProbabilityMeasure ν := ⟨by rw [hν, ofPotential_univ, hmass₀]⟩
  have hne₀' : ∃ x, ψ₀' x ≠ ⊤ := by
    obtain ⟨x, hx⟩ := interior_domain_nonempty_of_mass_ne_zero volume hc₀'
      (by rw [hmass₀]; exact one_ne_zero)
    exact ⟨x, interior_subset hx⟩
  have hne₁' : ∃ x, ψ₁' x ≠ ⊤ := by
    obtain ⟨x, hx⟩ := interior_domain_nonempty_of_mass_ne_zero volume hc₁'
      (by rw [hmass₁]; exact one_ne_zero)
    exact ⟨x, interior_subset hx⟩
  have hbi₀ := legendre_legendre_eq hc₀' he₀'.1 hne₀'
  have hbi₁ := legendre_legendre_eq hc₁' he₁'.1 hne₁'
  have hpot₀ : PotentialIntegrable (legendre ψ₀') ν :=
    potentialIntegrable_legendre hc₀' he₀'.1 hmass₀
  have hpot₁ : PotentialIntegrable (legendre ψ₁') ν := by
    rw [← hν₁]; exact potentialIntegrable_legendre hc₁' he₁'.1 hmass₁
  have hmax₀ : ∀ f : E → EReal, PotentialIntegrable f ν →
      variationalFunctional volume ν f ≤ variationalFunctional volume ν (legendre ψ₀') :=
    fun f hf => variationalFunctional_le_legendre hc₀' he₀' hmass₀ hf
  have hmax₁ : ∀ f : E → EReal, PotentialIntegrable f ν →
      variationalFunctional volume ν f ≤ variationalFunctional volume ν (legendre ψ₁') := by
    intro f hf
    rw [← hν₁] at hf ⊢
    exact variationalFunctional_le_legendre hc₁' he₁' hmass₁ hf
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_legendre_of_maximizer hpot₀ hpot₁
    (by rw [hbi₀, hmass₀]) (by rw [hbi₁, hmass₁]) hmax₀ hmax₁
  refine ⟨y₀, fun y => ?_⟩
  have h := hy₀ y
  rw [hbi₀, hbi₁] at h
  rw [← sub_coe_add_coe (ψ₁ y) b, ← sub_coe_add_coe (ψ₀ (y - y₀)) b]
  exact congrArg (· + (b : EReal)) h

/-- **CEK Theorem 2** (Cordero-Erausquin–Klartag, arXiv:1304.0630v1, Theorem 2; Letwin
arXiv:2607.24164v1, Lemma 2.1): let `μ` be a finite nonzero Borel measure on a finite-dimensional
real inner-product space with finite first moment, barycenter `0`, and not supported in a proper
linear subspace. Then there is a convex, essentially continuous `ψ : E → ℝ ∪ {+∞}` whose moment
measure is `μ`, and every convex essentially continuous potential with moment measure `μ` is a
translate `ψ(· − y₀)` of it. -/
theorem exists_essentiallyContinuous_ofPotential_eq_unique {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ ψ : E → EReal, ConvexPotential ψ ∧ EssentiallyContinuous ψ ∧ ofPotential volume ψ = μ ∧
      ∀ ψ₁ : E → EReal, ConvexPotential ψ₁ → EssentiallyContinuous ψ₁ →
        ofPotential volume ψ₁ = μ → ∃ y₀ : E, ∀ y, ψ₁ y = ψ (y - y₀) := by
  obtain ⟨ψ, hconv, hess, -, -, hmom⟩ :=
    exists_ofPotential_eq_essentiallyContinuous volume μ hμ hsub hfirst hbar
  exact ⟨ψ, hconv, hess, hmom, fun ψ₁ hψ₁ he₁ hm₁ =>
    exists_eq_translate_of_ofPotential_eq_of_essentiallyContinuous hμ hconv hψ₁ hess he₁ hmom hm₁⟩

end EssentiallyContinuousPotential

end FunctionalInequalities.KLS.CEK
