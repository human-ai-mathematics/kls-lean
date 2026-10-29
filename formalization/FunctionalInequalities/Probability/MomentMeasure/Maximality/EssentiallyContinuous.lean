import FunctionalInequalities.Probability.MomentMeasure.Maximality.GradientVariation
import FunctionalInequalities.Probability.MomentMeasure.Maximality.Finite

/-!
# Maximality of essentially continuous moment potentials (CEK Theorem 8)

Let `ψ : E → ℝ ∪ {+∞}` be convex, lower semicontinuous, with `∫ e^{-ψ} = 1`, and let `μ` be its
moment measure, the push-forward of `e^{-ψ(x)} dx` under `∇ψ`.

* `lintegral_indicator_abs_inner_gradient_lt_top`, `integrable_norm_ofPotential`: `∫ |∇e^{-ψ}| < ∞`
  and `μ` has a finite first moment (Cordero-Erausquin–Klartag, *Moment measures*,
  arXiv:1304.0630v1, Lemma 4).
* `lintegral_indicator_inner_gradient_sub_le`: integrability of `⟪∇ψ(x), x − a⟫ e^{-ψ(x)}` (CEK
  Lemma 5, integrability part, with the bound `n 2^n + C₀` in place of `n`).
* `lintegral_le_exp_of_convexOn`: the finite form of Theorem 8 for an unnormalized finite convex
  potential.
* `potentialIntegrable_legendre`: `ψ*` is `μ`-integrable (CEK Proposition 7).
* `variationalFunctional_le_legendre`: if `ψ` is moreover essentially continuous, then `ψ*`
  maximizes `I_μ(f) = log ∫ e^{-f*} − ∫ f dμ` over all `μ`-integrable `f` (CEK Theorem 8, (18)).

The proof of Theorem 8 does not use optimal transport. The finite convex `k`-Lipschitz potentials
`ψₖ = (ψ*|_{B_{c+k}})*` (`BallTruncation.lean`) satisfy the finite form of Theorem 8
(`lintegral_le_exp_integral_of_map_gradient_of_integrable`, proved with the Prékopa–Leindler
inequality); their moment measures agree with that of `ψ` on `{‖∇ψ‖ ≤ c + k}`, and the remaining
gradient mass of `e^{-ψₖ}` tends to zero by the line-by-line variation estimate for essentially
continuous potentials (`GradientVariation.lean`). Essential continuity enters only there; without
it the conclusion fails (CEK Proposition 10).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ψ : E → EReal}

section Basic

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Fenchel equality** at an interior differentiability point of a convex potential:
`ψ*(∇ψ(x)) = ⟪x, ∇ψ(x)⟫ − ψ(x)` (CEK (12)). -/
theorem legendre_gradient_eq_of_mem_interior (hψ : ConvexPotential ψ) {x : E}
    (hx : x ∈ interior {y | ψ y ≠ ⊤}) (hd : DifferentiableAt ℝ (fun y => (ψ y).toReal) x) :
    legendre ψ (gradient (fun y => (ψ y).toReal) x) =
      ((inner ℝ x (gradient (fun y => (ψ y).toReal) x) - (ψ x).toReal : ℝ) : EReal) := by
  refine le_antisymm (legendre_gradient_le hψ hx hd) ?_
  have h := le_iSup (fun y => (inner ℝ y (gradient (fun y => (ψ y).toReal) x) : EReal) - ψ y) x
  rwa [← EReal.coe_toReal (interior_subset hx) (hψ.1 x), ← EReal.coe_sub] at h

/-- Almost every point of the effective domain of a convex potential is an interior
differentiability point. -/
theorem ae_mem_interior_differentiableAt (hψ : ConvexPotential ψ) :
    ∀ᵐ x ∂(volume : Measure E), ψ x ≠ ⊤ →
      x ∈ interior {y | ψ y ≠ ⊤} ∧ DifferentiableAt ℝ (fun y => (ψ y).toReal) x := by
  have hfront := hψ.convex_domain.addHaar_frontier (volume : Measure E)
  have hconvI : ConvexOn ℝ (interior {y | ψ y ≠ ⊤}) fun y => (ψ y).toReal :=
    hψ.convexOn_toReal.subset interior_subset hψ.convex_domain.interior
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hfront,
    hconvI.ae_differentiableAt_of_isOpen volume isOpen_interior] with x hx1 hx2 hK
  have hI : x ∈ interior {y | ψ y ≠ ⊤} := by
    by_contra h
    exact hx1 ⟨subset_closure hK, h⟩
  exact ⟨hI, hx2 hI⟩

/-- Lower integrals against the moment measure of a Borel potential. -/
theorem lintegral_ofPotential (hψ : Measurable ψ) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂ofPotential volume ψ =
      ∫⁻ x, density ψ x * g (gradient (fun y => (ψ y).toReal) x) := by
  have hd : Measurable (density ψ) := EReal.measurable_exp.comp hψ.neg
  rw [ofPotential, lintegral_map hg (measurable_gradient_toReal ψ), weightedMeasure]
  exact lintegral_withDensity_eq_lintegral_mul _ hd (hg.comp (measurable_gradient_toReal ψ))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The norm is dominated by the sum of the absolute coordinates in the standard orthonormal
basis. -/
theorem norm_le_sum_abs_inner (v : E) :
    ‖v‖ ≤ ∑ i, |inner ℝ v (stdOrthonormalBasis ℝ E i)| := by
  set B := stdOrthonormalBasis ℝ E
  conv_lhs => rw [← B.sum_repr' v]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, B.orthonormal.1 i, mul_one, Real.norm_eq_abs, real_inner_comm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- On the set where `‖∇ψ‖ ≤ c + k`, the truncated potential of radius `c + k` and its gradient
agree with those of `ψ` at common differentiability points. -/
theorem toReal_legendre_ballTruncate_eq (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    {c b : ℝ} (hc : 0 ≤ c) (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) {k : ℝ} (hk : c ≤ k)
    {x : E} (hx : x ∈ interior {y | ψ y ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun y => (ψ y).toReal) x)
    (hgk : ‖gradient (fun y => (ψ y).toReal) x‖ ≤ k)
    (hdk : DifferentiableAt ℝ (fun y => (legendre (ballTruncate (legendre ψ) k) y).toReal) x) :
    (legendre (ballTruncate (legendre ψ) k) x).toReal = (ψ x).toReal ∧
      gradient (fun y => (legendre (ballTruncate (legendre ψ) k) y).toReal) x =
        gradient (fun y => (ψ y).toReal) x := by
  have hx₁ : ψ x ≠ ⊤ := interior_subset hx
  have hne : ∃ y, ψ y ≠ ⊤ := ⟨x, hx₁⟩
  have hle := legendre_ballTruncate_le hψ hlsc hne k
  have hfin := legendre_ballTruncate_ne_top_ne_bot hlow hc hk hx₁
  have heq := legendre_ballTruncate_eq_of_norm_gradient_le hψ hx hd hgk hle
  exact ⟨by rw [heq], gradient_toReal_legendre_ballTruncate_eq hx hd hle (fun y => (hfin y).2) heq
    hdk⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The density of a potential at a finite value. -/
theorem density_eq_ofReal' {x : E} (ht : ψ x ≠ ⊤) (hb : ψ x ≠ ⊥) :
    density ψ x = ENNReal.ofReal (Real.exp (-(ψ x).toReal)) := by
  rw [density, ← EReal.coe_toReal ht hb, ← EReal.coe_neg, EReal.exp_coe, EReal.toReal_coe]

end Basic

section FirstMoment

/-- **The gradient of a moment potential is integrable** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, Lemma 4, first part, `∫ |∇ρ| < ∞` for `ρ = e^{-ψ}`): for a convex, lower
semicontinuous `ψ` with `0 < ∫ e^{-ψ} < ∞`, the coordinate derivatives satisfy
`∫_G |⟪∇ψ, θ⟫| e^{-ψ} < ∞` for every unit vector `θ`, where `G` is the set of interior
differentiability points. -/
theorem lintegral_indicator_abs_inner_gradient_lt_top (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (h0 : mass volume ψ ≠ 0) (htop : mass volume ψ ≠ ⊤)
    {θ : E} (hθ : ‖θ‖ = 1) :
    ∫⁻ x, (interior {x | ψ x ≠ ⊤} ∩
        {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x}).indicator
        (fun x => ENNReal.ofReal (|inner ℝ (gradient (fun x => (ψ x).toReal) x) θ| *
          Real.exp (-(ψ x).toReal))) x < ⊤ := by
  obtain ⟨c, hc, b, hlow⟩ := exists_linear_lower_bound_of_mass hψ hlsc h0 htop
  obtain ⟨x₁, hx₁I⟩ := interior_domain_nonempty_of_mass_ne_zero volume hψ h0
  have hx₁ : ψ x₁ ≠ ⊤ := interior_subset hx₁I
  obtain ⟨C, hCt, hC⟩ := lintegral_directional_truncate_le_const hc hlow hx₁ hθ
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set G := interior {x | ψ x ≠ ⊤} ∩ {x | DifferentiableAt ℝ Ψ x} with hG
  set F : E → ℝ≥0∞ := fun x => ENNReal.ofReal (|inner ℝ (gradient Ψ x) θ| * Real.exp (-Ψ x))
    with hF
  have hΨm : Measurable Ψ := measurable_ereal_toReal.comp hlsc.measurable
  have hFm : Measurable F :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Measurable.inner (measurable_gradient_toReal ψ) measurable_const)).mul
      (Real.measurable_exp.comp hΨm.neg))
  have hGm : MeasurableSet G :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ)
  set A : ℕ → Set E := fun k => G ∩ {x | ‖gradient Ψ x‖ ≤ c + k} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hGm.inter (measurableSet_le (continuous_norm.measurable.comp (measurable_gradient_toReal ψ))
      measurable_const)
  have hk : ∀ k : ℕ, c ≤ c + k := fun k => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hstep : ∀ k : ℕ, ∫⁻ x, (A k).indicator F x ≤ C := by
    intro k
    refine le_trans (lintegral_mono_ae ?_) (hC k)
    have hconv := convexOn_toReal_legendre_ballTruncate hlow hc.le (hk k) hx₁
    filter_upwards [hconv.ae_differentiableAt_of_isOpen volume isOpen_univ] with x hdk
    by_cases hx : x ∈ A k
    · rw [indicator_of_mem hx]
      obtain ⟨h1, h2⟩ := toReal_legendre_ballTruncate_eq hψ hlsc hc.le hlow (hk k) hx.1.1 hx.1.2
        hx.2 (hdk (mem_univ x))
      simp only [hF, h1, h2]
      exact le_rfl
    · rw [indicator_of_notMem hx]; exact zero_le
  have hsup : G.indicator F = fun x => ⨆ k : ℕ, (A k).indicator F x := by
    funext x
    by_cases hxG : x ∈ G
    · obtain ⟨k, hk'⟩ := exists_nat_ge (‖gradient Ψ x‖ - c)
      refine le_antisymm ?_ (iSup_le fun j => indicator_le_indicator_of_subset
        inter_subset_left (fun _ => zero_le) x)
      refine le_trans (le_of_eq ?_) (le_iSup _ k)
      rw [indicator_of_mem hxG, indicator_of_mem (show x ∈ A k from
        ⟨hxG, show ‖gradient Ψ x‖ ≤ c + k by linarith⟩)]
    · rw [indicator_of_notMem hxG]
      refine le_antisymm zero_le (iSup_le fun j => ?_)
      rw [indicator_of_notMem fun h => hxG h.1]
  rw [hsup, lintegral_iSup (fun k => hFm.indicator (hAm k)) (fun i j hij x =>
    indicator_le_indicator_of_subset (fun y (hy : y ∈ A i) => by
      have h2 : ‖gradient Ψ y‖ ≤ c + i := hy.2
      have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
      exact show y ∈ A j from ⟨hy.1, show ‖gradient Ψ y‖ ≤ c + j by linarith⟩)
      (fun _ => zero_le) x)]
  exact lt_of_le_of_lt (iSup_le hstep) (lt_top_iff_ne_top.mpr hCt)

/-- **Finite first moment of a moment measure** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, Lemma 4 and the remark before Proposition 1): for a convex, lower
semicontinuous `ψ` with `0 < ∫ e^{-ψ} < ∞`, `∫ ‖p‖ dμ(p) < ∞` for the moment measure `μ` of `ψ`. -/
theorem integrable_norm_ofPotential (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    (h0 : mass volume ψ ≠ 0) (htop : mass volume ψ ≠ ⊤) :
    Integrable (fun p : E => ‖p‖) (ofPotential volume ψ) := by
  set B := stdOrthonormalBasis ℝ E
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set G := interior {x | ψ x ≠ ⊤} ∩ {x | DifferentiableAt ℝ Ψ x} with hG
  have hfin : ∀ i, ∫⁻ x, G.indicator (fun x => ENNReal.ofReal (|inner ℝ (gradient Ψ x) (B i)| *
      Real.exp (-Ψ x))) x < ⊤ := fun i =>
    lintegral_indicator_abs_inner_gradient_lt_top hψ hlsc h0 htop (B.orthonormal.1 i)
  refine ⟨measurable_norm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have heq : ∀ p : E, ‖‖p‖‖ₑ = ENNReal.ofReal ‖p‖ := fun p =>
    Real.enorm_eq_ofReal (norm_nonneg p)
  simp_rw [heq]
  rw [lintegral_ofPotential (g := fun p => ENNReal.ofReal ‖p‖) hlsc.measurable
    (ENNReal.measurable_ofReal.comp measurable_norm)]
  calc ∫⁻ x, density ψ x * ENNReal.ofReal ‖gradient Ψ x‖
      ≤ ∫⁻ x, ∑ i, G.indicator (fun x => ENNReal.ofReal (|inner ℝ (gradient Ψ x) (B i)| *
          Real.exp (-Ψ x))) x := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_interior_differentiableAt hψ] with x hx
        by_cases hxt : ψ x = ⊤
        · simp [density, hxt]
        obtain ⟨hxI, hxd⟩ := hx hxt
        have hxG : x ∈ G := ⟨hxI, hxd⟩
        simp only [indicator_of_mem hxG]
        rw [density_eq_ofReal' hxt (hψ.1 x), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_le_sum_abs_inner _) (Real.exp_pos _).le
    _ = ∑ i, ∫⁻ x, G.indicator (fun x => ENNReal.ofReal (|inner ℝ (gradient Ψ x) (B i)| *
          Real.exp (-Ψ x))) x := by
        refine lintegral_finsetSum _ fun i _ => ?_
        exact (ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
          (Measurable.inner (measurable_gradient_toReal ψ) measurable_const)).mul
          (Real.measurable_exp.comp (measurable_ereal_toReal.comp hlsc.measurable).neg))).indicator
          (isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ))
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun i _ => hfin i

end FirstMoment

section Scaling

/-- Homothety from `a`: `∫ e^{-ψ(a + t(x − a))} dx = t^{-n} ∫ e^{-ψ}`. -/
private theorem lintegral_density_homothety (hψm : Measurable ψ) (a : E) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, density ψ (a + t • (x - a)) =
      ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * mass volume ψ := by
  have hdm : Measurable (density ψ) := EReal.measurable_exp.comp hψm.neg
  have h1 : ∫⁻ x, density ψ (a + t • (x - a)) = ∫⁻ y, density ψ (a + t • y) := by
    rw [← lintegral_add_right_eq_self (fun x => density ψ (a + t • (x - a))) a]
    simp only [add_sub_cancel_right]
  have h2 : ∫⁻ y, density ψ (a + t • y) =
      ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * ∫⁻ z, density ψ (a + z) := by
    have hm : Measurable fun z => density ψ (a + z) := hdm.comp (measurable_const_add a)
    have h := lintegral_map hm (measurable_const_smul t) (μ := (volume : Measure E))
    rw [Measure.map_addHaar_smul volume ht.ne', lintegral_smul_measure,
      abs_of_pos (inv_pos.mpr (pow_pos ht _))] at h
    exact h.symm
  rw [h1, h2, lintegral_add_left_eq_self (density ψ) a, mass]

/-- Bernoulli-type bound used for the homothety quotient: `t^{-n} ≤ 1 + (1 − t) n 2^n` for
`1/2 ≤ t ≤ 1`. -/
private theorem inv_pow_le (n : ℕ) {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1) :
    (t ^ n)⁻¹ ≤ 1 + (1 - t) * (n * 2 ^ n) := by
  have htpos : 0 < t := by linarith
  have hpow : 0 < t ^ n := pow_pos htpos n
  have hbern : 1 - n * (1 - t) ≤ t ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 - t) by linarith) n
    have heq : 1 + -(1 - t) = t := by ring
    rw [heq] at this
    linarith
  have hlow : (1 / 2 : ℝ) ^ n ≤ t ^ n := pow_le_pow_left₀ (by norm_num) ht n
  have h2n : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [inv_le_iff_one_le_mul₀ hpow]
  have hnt : 0 ≤ (n : ℝ) * (1 - t) := mul_nonneg (Nat.cast_nonneg n) (by linarith)
  have key : (n : ℝ) * (1 - t) ≤ (1 - t) * (n * 2 ^ n) * t ^ n := by
    have : (1 - t) * (n * 2 ^ n) * t ^ n ≥ (1 - t) * (n * 2 ^ n) * (1 / 2) ^ n :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    have h' : (1 - t) * (n * 2 ^ n) * (1 / 2) ^ n = n * (1 - t) := by
      calc (1 - t) * (n * 2 ^ n) * (1 / 2) ^ n = (n * (1 - t)) * (2 ^ n * (1 / 2) ^ n) := by ring
        _ = n * (1 - t) := by rw [h2n, mul_one]
    linarith
  nlinarith

/-- **Integration by parts inequality** (Cordero-Erausquin–Klartag, arXiv:1304.0630v1,
Lemma 5, integrability part), in lower-integral form: for a convex, lower semicontinuous `ψ` with
`∫ e^{-ψ} = 1`, a point `a` in the interior of its domain and `C₀ ≥ 0` with
`ψ(a) − C₀ ≤ ψ` on the domain,
`∫_G e^{-ψ(x)} (⟪∇ψ(x), x − a⟫ + C₀) dx ≤ n 2^n + C₀`. The proof differentiates the homothety
identity `∫ e^{-ψ(a + t(x − a))} dx = t^{-n}` at `t = 1` with Fatou's lemma. -/
theorem lintegral_indicator_inner_gradient_sub_le (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (hmass : mass volume ψ = 1) {a : E}
    (ha : a ∈ interior {x | ψ x ≠ ⊤}) {C₀ : ℝ} (hC₀0 : 0 ≤ C₀)
    (hC₀ : ∀ x, ψ x ≠ ⊤ → (ψ a).toReal - C₀ ≤ (ψ x).toReal) :
    ∫⁻ x, (interior {x | ψ x ≠ ⊤} ∩
        {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x}).indicator
        (fun x => ENNReal.ofReal (Real.exp (-(ψ x).toReal) *
          (inner ℝ (gradient (fun x => (ψ x).toReal) x) (x - a) + C₀))) x ≤
      ENNReal.ofReal (Module.finrank ℝ E * 2 ^ Module.finrank ℝ E + C₀) := by
  set n := Module.finrank ℝ E
  set K := {x | ψ x ≠ ⊤} with hK
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set G := interior K ∩ {x | DifferentiableAt ℝ Ψ x} with hG
  have hΨm : Measurable Ψ := measurable_ereal_toReal.comp hlsc.measurable
  have hGm : MeasurableSet G :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ)
  have hconvK : ConvexOn ℝ K Ψ := hψ.convexOn_toReal
  have hcoe : ∀ x ∈ K, ψ x = (Ψ x : EReal) := fun x hx => (EReal.coe_toReal hx (hψ.1 x)).symm
  -- the difference quotients along the homotheties from `a`
  set q : ℝ → E → ℝ := fun t x => (Ψ x - Ψ (a + t • (x - a))) / (1 - t) with hq
  have hpt : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ x ∈ interior K, a + t • (x - a) ∈ interior K := by
    intro t ht0 ht1 x hx
    have h := hψ.convex_domain.interior ha hx (by linarith : (0 : ℝ) ≤ 1 - t) ht0
      (by ring)
    convert h using 1
    module
  have hqlow : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ x ∈ interior K, -C₀ ≤ q t x := by
    intro t ht0 ht1 x hx
    have hcomb := hconvK.2 (interior_subset ha) (interior_subset hx) (by linarith : (0 : ℝ) ≤ 1 - t)
      ht0 (by ring)
    have heq : (1 - t) • a + t • x = a + t • (x - a) := by module
    rw [heq, smul_eq_mul, smul_eq_mul] at hcomb
    have h1 := hC₀ x (interior_subset hx)
    rw [hq, le_div_iff₀ (by linarith)]
    nlinarith
  set f : ℝ → E → ℝ≥0∞ := fun t => G.indicator fun x =>
    ENNReal.ofReal (Real.exp (-Ψ x) * (q t x + C₀)) with hf
  have hfm : ∀ t, Measurable (f t) := fun t =>
    (ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hΨm.neg).mul
      (((hΨm.sub (hΨm.comp ((measurable_const_add a).comp
        ((measurable_const_smul t).comp (measurable_id.sub_const a))))).div_const _).add
        measurable_const))).indicator hGm
  -- the bound for each homothety ratio `t ∈ [1/2, 1)`
  have hbound : ∀ t : ℝ, 1 / 2 ≤ t → t < 1 →
      ∫⁻ x, f t x ≤ ENNReal.ofReal (n * 2 ^ n + C₀) := by
    intro t ht ht1
    have ht0 : 0 ≤ t := by linarith
    have h1t : 0 < 1 - t := by linarith
    have hpoint : ∀ᵐ x ∂(volume : Measure E),
        density ψ x + ENNReal.ofReal (1 - t) * f t x ≤
          density ψ (a + t • (x - a)) + ENNReal.ofReal ((1 - t) * C₀) * density ψ x := by
      filter_upwards [ae_mem_interior_differentiableAt hψ] with x hx
      by_cases hxK : ψ x = ⊤
      · simp [density, hxK, f, show x ∉ G from fun h => interior_subset h.1 hxK]
      obtain ⟨hxI, hxd⟩ := hx hxK
      have hxG : x ∈ G := ⟨hxI, hxd⟩
      have hyI := hpt t ht0 ht1 x hxI
      rw [hf]
      simp only [indicator_of_mem hxG]
      rw [density_eq_ofReal' hxK (hψ.1 x), density_eq_ofReal' (interior_subset hyI) (hψ.1 _)]
      have hqx := hqlow t ht0 ht1 x hxI
      have hd : Ψ x - Ψ (a + t • (x - a)) = (1 - t) * q t x := by
        rw [hq]; field_simp
      have hexp : Real.exp (-Ψ x) * (1 + (Ψ x - Ψ (a + t • (x - a)))) ≤
          Real.exp (-Ψ (a + t • (x - a))) := by
        have h := Real.add_one_le_exp (Ψ x - Ψ (a + t • (x - a)))
        have h2 : Real.exp (-Ψ (a + t • (x - a))) =
            Real.exp (-Ψ x) * Real.exp (Ψ x - Ψ (a + t • (x - a))) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      rw [← ENNReal.ofReal_mul h1t.le, ← ENNReal.ofReal_add (Real.exp_pos _).le
        (mul_nonneg h1t.le (mul_nonneg (Real.exp_pos _).le (by linarith))),
        ← ENNReal.ofReal_mul (mul_nonneg h1t.le hC₀0), ← ENNReal.ofReal_add (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg h1t.le hC₀0) (Real.exp_pos _).le)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hd] at hexp
      nlinarith [Real.exp_pos (-Ψ x)]
    have hint := lintegral_mono_ae hpoint
    have hdm : Measurable (density ψ) := EReal.measurable_exp.comp hlsc.measurable.neg
    have hhm : Measurable fun x => density ψ (a + t • (x - a)) :=
      hdm.comp ((measurable_const_add a).comp ((measurable_const_smul t).comp
        (measurable_id.sub_const a)))
    rw [lintegral_add_left hdm, lintegral_const_mul _ (hfm t),
      lintegral_add_left (f := fun x => density ψ (a + t • (x - a))) hhm,
      lintegral_const_mul _ hdm,
      lintegral_density_homothety hlsc.measurable a (by linarith)] at hint
    rw [← mass, hmass, mul_one, mul_one] at hint
    have hreal := inv_pow_le n ht ht1.le
    have hR : ENNReal.ofReal ((t ^ n)⁻¹) + ENNReal.ofReal ((1 - t) * C₀) ≤
        1 + ENNReal.ofReal (1 - t) * ENNReal.ofReal (n * 2 ^ n + C₀) := by
      rw [← ENNReal.ofReal_mul h1t.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg h1t.le (by positivity))]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    have h3 := (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp (hint.trans hR)
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr h1t).ne'
      ENNReal.ofReal_ne_top).mp h3
  -- Fatou along `t_j = 1 − 1/(j + 2)`
  set tj : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2) with htj
  have htj1 : ∀ j, tj j < 1 := fun j => by
    have : 0 < 1 / ((j : ℝ) + 2) := by positivity
    simp only [htj]; linarith
  have htj2 : ∀ j, 1 / 2 ≤ tj j := fun j => by
    have h : 1 / ((j : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    simp only [htj]; linarith
  have hlimit : ∀ x, G.indicator (fun x => ENNReal.ofReal (Real.exp (-Ψ x) *
      (inner ℝ (gradient Ψ x) (x - a) + C₀))) x ≤ liminf (fun j => f (tj j) x) atTop := by
    intro x
    by_cases hxG : x ∈ G
    · rw [indicator_of_mem hxG]
      have hconv : Tendsto (fun j => q (tj j) x) atTop (𝓝 (inner ℝ (gradient Ψ x) (x - a))) := by
        have hline : HasDerivAt (fun s : ℝ => x + s • (x - a)) (x - a) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add x
        have hg : HasDerivAt (fun s : ℝ => Ψ (x + s • (x - a)))
            (fderiv ℝ Ψ x (x - a)) 0 := by
          exact hxG.2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
        have hgrad : fderiv ℝ Ψ x (x - a) = inner ℝ (gradient Ψ x) (x - a) := by
          rw [show gradient Ψ x = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ Ψ x) from rfl,
            InnerProductSpace.toDual_symm_apply]
        rw [hgrad] at hg
        have hs : Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 2))) atTop (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
          · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
            have h2 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0) := by
              refine squeeze_zero (fun j => by positivity) (fun j => ?_) h
              exact one_div_le_one_div_of_le (by positivity) (by linarith)
            simpa using h2.neg
          · simp only [mem_compl_iff, mem_singleton_iff, neg_eq_zero]
            positivity
        refine (hg.tendsto_slope_zero.comp hs).congr fun j => ?_
        simp only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_eq_mul, hq, htj]
        have hpos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
        have h1 : a + (1 - 1 / ((j : ℝ) + 2)) • (x - a) = x + -(1 / ((j : ℝ) + 2)) • (x - a) := by
          module
        rw [h1]
        field_simp
        ring
      have hf' : Tendsto (fun j => f (tj j) x) atTop
          (𝓝 (ENNReal.ofReal (Real.exp (-Ψ x) * (inner ℝ (gradient Ψ x) (x - a) + C₀)))) := by
        simp only [hf, indicator_of_mem hxG]
        exact (ENNReal.continuous_ofReal.tendsto _).comp
          ((tendsto_const_nhds.mul (hconv.add tendsto_const_nhds)))
      exact hf'.liminf_eq.ge
    · rw [indicator_of_notMem hxG]; exact zero_le
  calc ∫⁻ x, G.indicator (fun x => ENNReal.ofReal (Real.exp (-Ψ x) *
        (inner ℝ (gradient Ψ x) (x - a) + C₀))) x
      ≤ ∫⁻ x, liminf (fun j => f (tj j) x) atTop := lintegral_mono hlimit
    _ ≤ liminf (fun j => ∫⁻ x, f (tj j) x) atTop := lintegral_liminf_le fun j => hfm _
    _ ≤ ENNReal.ofReal (n * 2 ^ n + C₀) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun j => hbound _ (htj2 j) (htj1 j))

end Scaling

section Integrability

/-- `|s| e^{-s} ≤ 2e^{-s/2} + |b| e^{-s}` for `s ≥ −b`. -/
private theorem abs_mul_exp_neg_le {s b : ℝ} (hs : -b ≤ s) :
    |s| * Real.exp (-s) ≤ 2 * Real.exp (-(s / 2)) + |b| * Real.exp (-s) := by
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h]
    have h1 : s ≤ 2 * Real.exp (s / 2) := by linarith [Real.add_one_le_exp (s / 2)]
    have h2 : Real.exp (-s) = Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 := Real.exp_pos (-(s / 2))
    calc s * Real.exp (-s) = s * Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by rw [h2]; ring
      _ ≤ 2 * Real.exp (s / 2) * Real.exp (-(s / 2)) * Real.exp (-(s / 2)) := by gcongr
      _ = 2 * Real.exp (-(s / 2)) := by rw [mul_assoc 2, h3, mul_one]
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · rw [abs_of_neg h]
    have : -s ≤ |b| := by linarith [le_abs_self b]
    have h5 := Real.exp_pos (-(s / 2))
    nlinarith [Real.exp_pos (-s)]

variable (ψ) in
/-- The set of interior differentiability points of a potential. -/
private abbrev goodSet : Set E :=
  interior {x | ψ x ≠ ⊤} ∩ {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x}

/-- The directional gradient density is integrable on the good set. -/
private theorem integrable_indicator_inner_gradient (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (h0 : mass volume ψ ≠ 0) (htop : mass volume ψ ≠ ⊤)
    {θ : E} (hθ : ‖θ‖ = 1) :
    Integrable ((goodSet ψ).indicator fun x => Real.exp (-(ψ x).toReal) *
      inner ℝ (gradient (fun x => (ψ x).toReal) x) θ) := by
  have hfin := lintegral_indicator_abs_inner_gradient_lt_top hψ hlsc h0 htop hθ
  have hΨm : Measurable fun x => (ψ x).toReal := measurable_ereal_toReal.comp hlsc.measurable
  have hm : Measurable ((goodSet ψ).indicator fun x => Real.exp (-(ψ x).toReal) *
      inner ℝ (gradient (fun x => (ψ x).toReal) x) θ) :=
    ((Real.measurable_exp.comp hΨm.neg).mul
      (Measurable.inner (measurable_gradient_toReal ψ) measurable_const)).indicator
      (isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ _))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hfin
  by_cases hx : x ∈ goodSet ψ
  · rw [indicator_of_mem hx, indicator_of_mem hx, Real.enorm_eq_ofReal_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), mul_comm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, enorm_zero]

/-- **The conjugate of a moment potential is integrable** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, Proposition 7): for a convex, lower semicontinuous `ψ : E → ℝ ∪ {+∞}` with
`∫ e^{-ψ} = 1` and moment measure `μ`, the conjugate `ψ*` is `μ`-integrable. -/
theorem potentialIntegrable_legendre (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    (hmass : mass volume ψ = 1) : PotentialIntegrable (legendre ψ) (ofPotential volume ψ) := by
  have h0 : mass volume ψ ≠ 0 := by rw [hmass]; exact one_ne_zero
  have htop : mass volume ψ ≠ ⊤ := by rw [hmass]; exact ENNReal.one_ne_top
  obtain ⟨c, hc, b, hlow⟩ := exists_linear_lower_bound_of_mass hψ hlsc h0 htop
  obtain ⟨a, ha⟩ := interior_domain_nonempty_of_mass_ne_zero volume hψ h0
  have hne : ∃ x, ψ x ≠ ⊤ := ⟨a, interior_subset ha⟩
  set K := {x | ψ x ≠ ⊤} with hK
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set G := goodSet ψ with hG
  have hΨm : Measurable Ψ := measurable_ereal_toReal.comp hlsc.measurable
  have hGm : MeasurableSet G :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ)
  have hdm : Measurable (density ψ) := EReal.measurable_exp.comp hlsc.measurable.neg
  have hΨlow : ∀ x ∈ K, c * ‖x‖ - b ≤ Ψ x := fun x hx => by
    have h := hlow x
    rwa [← EReal.coe_toReal hx (hψ.1 x), EReal.coe_le_coe_iff] at h
  set C₀ : ℝ := max 0 (b + Ψ a) with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_left _ _
  have hC₀le : ∀ x, ψ x ≠ ⊤ → Ψ a - C₀ ≤ Ψ x := fun x hx => by
    have h1 := hΨlow x hx
    have h2 := le_max_right 0 (b + Ψ a)
    nlinarith [norm_nonneg x]
  have hφ : ∀ x ∈ G, legendre ψ (gradient Ψ x) = ((inner ℝ x (gradient Ψ x) - Ψ x : ℝ) : EReal) :=
    fun x hx => legendre_gradient_eq_of_mem_interior hψ hx.1 hx.2
  refine ⟨fun p => legendre_ne_bot ψ ⟨hψ.1, hne⟩ p, ?_, ?_⟩
  · -- almost every gradient value has a finite conjugate
    have hset : MeasurableSet {p : E | legendre ψ p ≠ ⊤} :=
      ((lowerSemicontinuous_legendre ψ).measurable (measurableSet_singleton ⊤)).compl
    rw [ofPotential, ae_map_iff (measurable_gradient_toReal ψ).aemeasurable hset, weightedMeasure,
      ae_withDensity_iff hdm]
    filter_upwards [ae_mem_interior_differentiableAt hψ] with x hx hdx
    have hxt : ψ x ≠ ⊤ := fun h => hdx (by simp [density, h])
    obtain ⟨hxI, hxd⟩ := hx hxt
    show legendre ψ (gradient Ψ x) ≠ ⊤
    rw [hφ x ⟨hxI, hxd⟩]
    exact EReal.coe_ne_top _
  · -- integrability through the density
    have hφm : Measurable fun p => (legendre ψ p).toReal :=
      measurable_ereal_toReal.comp (lowerSemicontinuous_legendre ψ).measurable
    rw [ofPotential, integrable_map_measure hφm.aestronglyMeasurable
      (measurable_gradient_toReal ψ).aemeasurable, weightedMeasure,
      integrable_withDensity_iff hdm (Eventually.of_forall fun x => by
        rw [density, EReal.exp_lt_top_iff, lt_top_iff_ne_top]
        exact fun h => hψ.1 x (EReal.neg_eq_top_iff.mp h))]
    -- the four pieces
    set B := stdOrthonormalBasis ℝ E
    set e : E → ℝ := fun x => Real.exp (-Ψ x) with he
    have hem : Measurable e := Real.measurable_exp.comp hΨm.neg
    have hbound : ∀ (c' b' : ℝ), 0 < c' →
        Integrable fun x : E => Real.exp (b' - c' * ‖x‖) := fun c' b' hc' =>
      integrable_exp_sub_norm volume hc' b'
    have hT1 : Integrable (G.indicator fun x => e x * (inner ℝ (gradient Ψ x) (x - a) + C₀)) := by
      have hm : Measurable (G.indicator fun x => e x * (inner ℝ (gradient Ψ x) (x - a) + C₀)) :=
        (hem.mul ((Measurable.inner (measurable_gradient_toReal ψ)
          (measurable_id.sub_const a)).add_const _)).indicator hGm
      have hnn : ∀ x, 0 ≤ G.indicator (fun x => e x * (inner ℝ (gradient Ψ x) (x - a) + C₀)) x := by
        intro x
        by_cases hx : x ∈ G
        · rw [indicator_of_mem hx]
          refine mul_nonneg (Real.exp_pos _).le ?_
          have hsupp := convex_support_of_hasFDerivWithinAt hψ.convexOn_toReal
            hx.2.hasFDerivAt.hasFDerivWithinAt (interior_subset hx.1) (interior_subset ha)
          have hg : fderiv ℝ Ψ x (a - x) = inner ℝ (gradient Ψ x) (a - x) := by
            rw [show gradient Ψ x = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ Ψ x) from rfl,
              InnerProductSpace.toDual_symm_apply]
          rw [hg] at hsupp
          have hneg : inner ℝ (gradient Ψ x) (a - x) = -inner ℝ (gradient Ψ x) (x - a) := by
            rw [← inner_neg_right, neg_sub]
          have h1 := hC₀le x (interior_subset hx.1)
          change Ψ x + inner ℝ (gradient Ψ x) (a - x) ≤ Ψ a at hsupp
          linarith
        · rw [indicator_of_notMem hx]
      refine (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
        (Eventually.of_forall hnn)).mp (ne_of_lt (lt_of_le_of_lt (le_of_eq
          (lintegral_congr fun x => ?_)) (lt_of_le_of_lt
          (lintegral_indicator_inner_gradient_sub_le hψ hlsc hmass ha hC₀0 hC₀le)
          ENNReal.ofReal_lt_top)))
      by_cases hx : x ∈ G
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
    have hT2 : Integrable (G.indicator fun x => e x * C₀) := by
      refine Integrable.mono' ((hbound c b hc).mul_const C₀)
        ((hem.mul_const C₀).indicator hGm).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ G
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
          hC₀0)]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hC₀0
        linarith [hΨlow x (interior_subset hx.1)]
      · rw [indicator_of_notMem hx, norm_zero]; positivity
    have hT3 : Integrable (G.indicator fun x => e x * inner ℝ (gradient Ψ x) a) := by
      have hsum : (G.indicator fun x => e x * inner ℝ (gradient Ψ x) a) =
          fun x => ∑ i, inner ℝ (B i) a * G.indicator (fun x => e x *
            inner ℝ (gradient Ψ x) (B i)) x := by
        funext x
        by_cases hx : x ∈ G
        · simp only [indicator_of_mem hx]
          rw [← B.sum_inner_mul_inner (gradient Ψ x) a, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        · simp only [indicator_of_notMem hx, mul_zero, Finset.sum_const_zero]
      rw [hsum]
      exact integrable_finsetSum _ fun i _ =>
        (integrable_indicator_inner_gradient hψ hlsc h0 htop (B.orthonormal.1 i)).const_mul _
    have hT4 : Integrable (G.indicator fun x => e x * Ψ x) := by
      refine Integrable.mono' (((hbound (c / 2) (b / 2) (by positivity)).const_mul 2).add
        ((hbound c b hc).const_mul |b|)) ((hem.mul hΨm).indicator hGm).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ G
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
        have hl := hΨlow x (interior_subset hx.1)
        have hkey := abs_mul_exp_neg_le (show -b ≤ Ψ x by nlinarith [norm_nonneg x])
        refine hkey.trans (add_le_add ?_ ?_)
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          linarith
        · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (abs_nonneg _)
      · rw [indicator_of_notMem hx, norm_zero]
        exact add_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    refine (((hT1.sub hT2).add hT3).sub hT4).congr ?_
    filter_upwards [ae_mem_interior_differentiableAt hψ] with x hx
    by_cases hxt : ψ x = ⊤
    · have hxG : x ∉ G := fun h => interior_subset h.1 hxt
      simp only [Pi.sub_apply, Pi.add_apply, indicator_of_notMem hxG, sub_zero, add_zero,
        Function.comp_apply]
      simp [density, hxt]
    obtain ⟨hxI, hxd⟩ := hx hxt
    have hxG : x ∈ G := ⟨hxI, hxd⟩
    simp only [Pi.sub_apply, Pi.add_apply, indicator_of_mem hxG, Function.comp_apply]
    rw [hφ x hxG, EReal.toReal_coe, density_eq_ofReal' hxt (hψ.1 x),
      ENNReal.toReal_ofReal (Real.exp_pos _).le, inner_sub_right, real_inner_comm x (gradient Ψ x)]
    ring

end Integrability

section Truncation

variable {c b : ℝ} {x₁ : E}

/-- The masses of the truncated potentials converge to the mass of `ψ`. -/
private theorem tendsto_lintegral_density_truncate (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (hc : 0 < c) (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x)
    (hx₁ : ψ x₁ ≠ ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x, density (legendre (ballTruncate (legendre ψ) (c + k))) x) atTop
      (𝓝 (mass volume ψ)) := by
  have hne : ∃ x, ψ x ≠ ⊤ := ⟨x₁, hx₁⟩
  have hk : ∀ k : ℕ, c ≤ c + k := fun k => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine tendsto_lintegral_of_dominated_convergence
    (fun x => ENNReal.ofReal (Real.exp (b - c * ‖x‖)))
    (fun k => measurable_density_legendre _) (fun k => Eventually.of_forall fun x => ?_)
    ?_ (Eventually.of_forall fun x => ?_)
  · have h1 := linear_lower_bound_legendre_ballTruncate hlow hc.le (hk k) x
    have h2 := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr h1)
    rw [← EReal.coe_neg, EReal.exp_coe, neg_sub] at h2
    exact h2
  · exact ((integrable_exp_sub_norm volume hc b).lintegral_lt_top).ne
  · have hmono : Monotone fun k : ℕ => legendre (ballTruncate (legendre ψ) (c + k)) x :=
      fun i j hij => legendre_ballTruncate_mono _ (by
        have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
        linarith) x
    have hlim : Tendsto (fun k : ℕ => legendre (ballTruncate (legendre ψ) (c + k)) x) atTop
        (𝓝 (ψ x)) := by
      have h := tendsto_atTop_iSup hmono
      rwa [iSup_legendre_ballTruncate_add hψ hlsc hne hc.le x] at h
    exact (ENNReal.continuous_exp.tendsto _).comp ((continuous_neg.tendsto _).comp hlim)

/-- The gradient mass of the truncations outside the agreement set tends to zero (essential
continuity). -/
private theorem tendsto_lintegral_compl_directional (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (h0 : mass volume ψ ≠ 0) (htop : mass volume ψ ≠ ⊤)
    (hc : 0 < c) (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hx₁ : ψ x₁ ≠ ⊤)
    {θ : E} (hθ : ‖θ‖ = 1) :
    Tendsto (fun k : ℕ => ∫⁻ x, (goodSet ψ ∩
        {x | ‖gradient (fun x => (ψ x).toReal) x‖ ≤ c + k})ᶜ.indicator (fun x =>
        ENNReal.ofReal (|inner ℝ (gradient (fun x =>
          (legendre (ballTruncate (legendre ψ) (c + k)) x).toReal) x) θ| *
        Real.exp (-(legendre (ballTruncate (legendre ψ) (c + k)) x).toReal))) x) atTop (𝓝 0) := by
  have hlsc := hess.1
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set G := goodSet ψ with hG
  set F₀ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (|inner ℝ (gradient Ψ x) θ| * Real.exp (-Ψ x))
    with hF₀
  set Fk : ℕ → E → ℝ≥0∞ := fun k x => ENNReal.ofReal (|inner ℝ (gradient (fun x =>
      (legendre (ballTruncate (legendre ψ) (c + k)) x).toReal) x) θ| *
      Real.exp (-(legendre (ballTruncate (legendre ψ) (c + k)) x).toReal)) with hFk
  set A : ℕ → Set E := fun k => G ∩ {x | ‖gradient Ψ x‖ ≤ c + k} with hA
  have hΨm : Measurable Ψ := measurable_ereal_toReal.comp hlsc.measurable
  have hGm : MeasurableSet G :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ)
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hGm.inter (measurableSet_le (continuous_norm.measurable.comp (measurable_gradient_toReal ψ))
      measurable_const)
  have hF₀m : Measurable F₀ :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Measurable.inner (measurable_gradient_toReal ψ) measurable_const)).mul
      (Real.measurable_exp.comp hΨm.neg))
  have hk : ∀ k : ℕ, c ≤ c + k := fun k => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hAmono : Monotone A := fun i j hij x (hx : x ∈ A i) => by
    have h2 : ‖gradient Ψ x‖ ≤ c + i := hx.2
    have : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    exact show x ∈ A j from ⟨hx.1, show ‖gradient Ψ x‖ ≤ c + j by linarith⟩
  -- the agreement integrals increase to the finite limit
  set L := ∫⁻ x, G.indicator F₀ x with hL
  have hLt : L < ⊤ := lintegral_indicator_abs_inner_gradient_lt_top hψ hlsc h0 htop hθ
  have hsup : G.indicator F₀ = fun x => ⨆ k : ℕ, (A k).indicator F₀ x := by
    funext x
    by_cases hxG : x ∈ G
    · obtain ⟨k, hk'⟩ := exists_nat_ge (‖gradient Ψ x‖ - c)
      refine le_antisymm ?_ (iSup_le fun j => indicator_le_indicator_of_subset
        inter_subset_left (fun _ => zero_le) x)
      refine le_trans (le_of_eq ?_) (le_iSup _ k)
      rw [indicator_of_mem hxG, indicator_of_mem (show x ∈ A k from
        ⟨hxG, show ‖gradient Ψ x‖ ≤ c + k by linarith⟩)]
    · rw [indicator_of_notMem hxG]
      refine le_antisymm zero_le (iSup_le fun j => ?_)
      rw [indicator_of_notMem fun h => hxG h.1]
  have hamono : Monotone fun k => ∫⁻ x, (A k).indicator F₀ x := fun i j hij =>
    lintegral_mono fun x => indicator_le_indicator_of_subset (hAmono hij) (fun _ => zero_le) x
  have halim : Tendsto (fun k => ∫⁻ x, (A k).indicator F₀ x) atTop (𝓝 L) := by
    have h := tendsto_atTop_iSup hamono
    rwa [← lintegral_iSup (fun k => hF₀m.indicator (hAm k)) (fun i j hij x =>
      indicator_le_indicator_of_subset (hAmono hij) (fun _ => zero_le) x), ← hsup] at h
  -- on the agreement set the truncated and original integrands coincide
  have hagree : ∀ k, ∫⁻ x, (A k).indicator (Fk k) x = ∫⁻ x, (A k).indicator F₀ x := by
    intro k
    refine lintegral_congr_ae ?_
    have hconv := convexOn_toReal_legendre_ballTruncate hlow hc.le (hk k) hx₁
    filter_upwards [hconv.ae_differentiableAt_of_isOpen volume isOpen_univ] with x hdk
    by_cases hx : x ∈ A k
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      obtain ⟨h1, h2⟩ := toReal_legendre_ballTruncate_eq hψ hlsc hc.le hlow (hk k) hx.1.1 hx.1.2
        hx.2 (hdk (mem_univ x))
      simp only [hFk, hF₀]
      rw [h1, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  have hFkm : ∀ k, Measurable (Fk k) := fun k =>
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Measurable.inner (measurable_gradient_toReal _) measurable_const)).mul
      (Real.measurable_exp.comp (measurable_ereal_toReal.comp
        (lowerSemicontinuous_legendre _).measurable).neg))
  have hsplit : ∀ k, (∫⁻ x, (A k).indicator (Fk k) x) + (∫⁻ x, (A k)ᶜ.indicator (Fk k) x) =
      ∫⁻ x, Fk k x := fun k => by
    exact (lintegral_add_left ((hFkm k).indicator (hAm k)) _).symm.trans
      (lintegral_congr fun x => indicator_self_add_compl_apply _ _ _)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  have hupper := eventually_lintegral_directional_truncate_le hψ hess hc hlow hx₁ hθ (ε / 2) hε2
  have hlower : ∀ᶠ k in atTop, L ≤ (∫⁻ x, (A k).indicator F₀ x) + ε / 2 := by
    by_cases hL0 : L = 0
    · exact Eventually.of_forall fun k => by rw [hL0]; exact zero_le
    have hlt : L - ε / 2 < L := ENNReal.sub_lt_self hLt.ne hL0 hε2
    filter_upwards [halim.eventually (lt_mem_nhds hlt)] with k hk'
    exact (tsub_le_iff_right.mp hk'.le)
  filter_upwards [hupper, hlower] with k hu hl
  have hakL : ∫⁻ x, (A k).indicator F₀ x ≤ L := by
    rw [hL, hsup]
    exact lintegral_mono fun x => le_iSup (fun j : ℕ => (A j).indicator F₀ x) k
  have hak : ∫⁻ x, (A k).indicator F₀ x ≠ ⊤ := ne_top_of_le_ne_top hLt.ne hakL
  have hkey : (∫⁻ x, (A k)ᶜ.indicator (Fk k) x) + (∫⁻ x, (A k).indicator F₀ x) ≤
      ε + ∫⁻ x, (A k).indicator F₀ x := by
    calc (∫⁻ x, (A k)ᶜ.indicator (Fk k) x) + (∫⁻ x, (A k).indicator F₀ x)
        = ∫⁻ x, Fk k x := by rw [← hsplit k, hagree k, add_comm]
      _ ≤ L + ε / 2 := hu
      _ ≤ (∫⁻ x, (A k).indicator F₀ x) + ε / 2 + ε / 2 := by gcongr
      _ = ε + ∫⁻ x, (A k).indicator F₀ x := by rw [add_assoc, ENNReal.add_halves, add_comm]
  exact (ENNReal.add_le_add_iff_right hak).mp hkey

end Truncation

section FiniteMaximality

/-- **CEK Theorem 8 for a finite potential, unnormalized form.** For a finite convex `Φ` with
`Z = ∫ e^{-Φ} < ∞`, a measurable `H` with `e^{-Φ} H(∇Φ)` integrable and a measurable `g ≥ 0` with
`g(y) ≤ exp(H(∇Φ(w)) − Φ(w) − ⟪∇Φ(w), y − w⟫)` at differentiability points `w`,
`∫ g ≤ exp(Z⁻¹ ∫ e^{-Φ} H(∇Φ) + log Z)`. This is
`lintegral_le_exp_integral_of_map_gradient_of_integrable` for `Φ + log Z`. -/
theorem lintegral_le_exp_of_convexOn {Φ : E → ℝ} (hΦ : ConvexOn ℝ univ Φ)
    (hint : Integrable fun x => Real.exp (-Φ x)) {H : E → ℝ} (hHm : Measurable H)
    (hHint : Integrable fun w => Real.exp (-Φ w) * H (gradient Φ w))
    {g : E → ℝ≥0∞} (hgm : Measurable g)
    (hdom : ∀ w, DifferentiableAt ℝ Φ w → ∀ y,
      g y ≤ ENNReal.ofReal (Real.exp (H (gradient Φ w) - Φ w - inner ℝ (gradient Φ w) (y - w)))) :
    ∫⁻ y, g y ≤ ENNReal.ofReal (Real.exp ((∫ w, Real.exp (-Φ w) * H (gradient Φ w)) /
      (∫ w, Real.exp (-Φ w)) + Real.log (∫ w, Real.exp (-Φ w)))) := by
  set Z := ∫ w, Real.exp (-Φ w) with hZ
  have hZpos : 0 < Z := integral_exp_pos hint
  set Φ' : E → ℝ := fun x => Φ x + Real.log Z with hΦ'
  have hexp' : ∀ x, Real.exp (-Φ' x) = Real.exp (-Φ x) / Z := fun x => by
    rw [hΦ', neg_add, Real.exp_add, Real.exp_neg (Real.log Z), Real.exp_log hZpos, div_eq_mul_inv]
  have hgrad : gradient Φ' = gradient Φ := by
    funext x
    simp only [gradient, hΦ', fderiv_add_const]
  have hΦ'c : ConvexOn ℝ univ Φ' := hΦ.add_const _
  have hnorm : ∫ x, Real.exp (-Φ' x) = 1 := by
    simp_rw [hexp']
    rw [integral_div, ← hZ, div_self hZpos.ne']
  have hint' : Integrable fun x => Real.exp (-Φ' x) := by
    simp_rw [hexp']; exact hint.div_const Z
  set μ' := ((volume : Measure E).tilted (-Φ')).map (gradient Φ') with hμ'
  have hgm' : AEMeasurable (gradient Φ') ((volume : Measure E).tilted (-Φ')) := by
    rw [hgrad]
    exact (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.measurable_gradient
      Φ).aemeasurable
  have hint'' : Integrable (fun x => Real.exp ((-Φ') x)) := hint'
  have : IsProbabilityMeasure ((volume : Measure E).tilted (-Φ')) :=
    isProbabilityMeasure_tilted hint''
  have : IsProbabilityMeasure μ' := Measure.isProbabilityMeasure_map hgm'
  have hHμ : Integrable H μ' := by
    rw [hμ', integrable_map_measure hHm.aestronglyMeasurable hgm',
      integrable_tilted_iff hint'']
    refine (hHint.div_const Z).congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, hgrad, smul_eq_mul, Pi.neg_apply, hexp']
    ring
  have hmain := lintegral_le_exp_integral_of_map_gradient_of_integrable hΦ'c hnorm (μ := μ')
    rfl (h := fun p => H p + Real.log Z) (hHm.add_const _) (hHμ.add (integrable_const _)) hgm (by
      filter_upwards [hΦ.ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw y
      rw [hgrad]
      refine (hdom w (hw (mem_univ w)) y).trans (le_of_eq ?_)
      congr 2
      simp only [hΦ']
      ring)
  refine hmain.trans (le_of_eq ?_)
  congr 2
  have hnorm' : ∫ x, Real.exp ((-Φ') x) = 1 := hnorm
  rw [integral_add hHμ (integrable_const _), integral_const, probReal_univ, one_smul,
    hμ', integral_map hgm' hHm.aestronglyMeasurable, integral_tilted, hnorm']
  simp only [div_one, hgrad, smul_eq_mul, Pi.neg_apply]
  simp_rw [hexp']
  rw [← integral_div]
  congr 2
  funext w
  ring

end FiniteMaximality

section Bounds

/-- Exponential integrability of a potential with linear growth, with the weights `1`, `‖x‖` and
`|Φ|`. -/
private theorem integrable_exp_neg_of_linear {Φ : E → ℝ} (hΦm : Measurable Φ) {c b : ℝ}
    (hc : 0 < c) (hlow : ∀ x, c * ‖x‖ - b ≤ Φ x) :
    Integrable (fun x => Real.exp (-Φ x)) ∧ Integrable (fun x => ‖x‖ * Real.exp (-Φ x)) ∧
      Integrable (fun x => |Φ x| * Real.exp (-Φ x)) := by
  have hem : Measurable fun x => Real.exp (-Φ x) := Real.measurable_exp.comp hΦm.neg
  have hb1 := integrable_exp_sub_norm (volume : Measure E) hc b
  have hb2 := integrable_exp_sub_norm (volume : Measure E) (half_pos hc) (b + Real.log (2 / c))
  have hb3 := integrable_exp_sub_norm (volume : Measure E) (half_pos hc) (b / 2)
  have h1 : ∀ x, Real.exp (-Φ x) ≤ Real.exp (b - c * ‖x‖) := fun x =>
    Real.exp_le_exp.mpr (by linarith [hlow x])
  refine ⟨Integrable.mono' hb1 hem.aestronglyMeasurable (Eventually.of_forall fun x => ?_),
    Integrable.mono' hb2 (continuous_norm.measurable.mul hem).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_),
    Integrable.mono' ((hb3.const_mul 2).add (hb1.const_mul |b|))
      (continuous_abs.measurable.comp hΦm |>.mul hem).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)⟩
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact h1 x
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    have hn : c / 2 * ‖x‖ ≤ Real.exp (c / 2 * ‖x‖) := by
      linarith [Real.add_one_le_exp (c / 2 * ‖x‖)]
    have hnorm : ‖x‖ ≤ 2 / c * Real.exp (c / 2 * ‖x‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
    calc ‖x‖ * Real.exp (-Φ x) ≤ (2 / c * Real.exp (c / 2 * ‖x‖)) * Real.exp (b - c * ‖x‖) :=
          mul_le_mul hnorm (h1 x) (Real.exp_pos _).le (by positivity)
      _ = Real.exp (b + Real.log (2 / c) - c / 2 * ‖x‖) := by
          rw [show b + Real.log (2 / c) - c / 2 * ‖x‖ =
              Real.log (2 / c) + (c / 2 * ‖x‖ + (b - c * ‖x‖)) by ring,
            Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
          ring
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    have hl := hlow x
    have hkey := abs_mul_exp_neg_le (show -b ≤ Φ x by nlinarith [norm_nonneg x])
    refine hkey.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    · exact mul_le_mul_of_nonneg_left (h1 x) (abs_nonneg _)

end Bounds

section Maximality

/-- The estimate of CEK Theorem 8 for the part of `e^{-f*}` in a ball. -/
private theorem lintegral_indicator_closedBall_le (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (hmass : mass volume ψ = 1) {f : E → EReal}
    (hf : PotentialIntegrable f (ofPotential volume ψ)) (R : ℕ) :
    ∫⁻ y, (closedBall (0 : E) R).indicator (density (legendre f)) y ≤
      ENNReal.ofReal (Real.exp ((∫ p, (f p).toReal ∂ofPotential volume ψ) -
        ∫ p, (legendre ψ p).toReal ∂ofPotential volume ψ)) := by
  have hlsc := hess.1
  set μ := ofPotential volume ψ with hμ
  have h0 : mass volume ψ ≠ 0 := by rw [hmass]; exact one_ne_zero
  have htop : mass volume ψ ≠ ⊤ := by rw [hmass]; exact ENNReal.one_ne_top
  have hprob : IsProbabilityMeasure μ := ⟨by rw [hμ, ofPotential_univ, hmass]⟩
  obtain ⟨c, hc, b, hlow⟩ := exists_linear_lower_bound_of_mass hψ hlsc h0 htop
  obtain ⟨x₁, hx₁I⟩ := interior_domain_nonempty_of_mass_ne_zero volume hψ h0
  have hx₁ : ψ x₁ ≠ ⊤ := interior_subset hx₁I
  set D := density (legendre f) with hD
  set g := (closedBall (0 : E) R).indicator D with hg
  have hgm : Measurable g := (measurable_density_legendre f).indicator measurableSet_closedBall
  by_cases hfin : ∃ y₀ ∈ closedBall (0 : E) R, legendre f y₀ ≠ ⊤
  swap
  · push Not at hfin
    have hg0 : ∀ y, g y = 0 := fun y => by
      by_cases hy : y ∈ closedBall (0 : E) R
      · rw [hg, indicator_of_mem hy, hD, density, hfin y hy]; simp
      · rw [hg, indicator_of_notMem hy]
    simp only [hg0, lintegral_zero, zero_le]
  obtain ⟨y₀, hy₀, hy₀t⟩ := hfin
  have hfprop : ProperPotential f := by
    obtain ⟨p, hp⟩ := hf.2.1.exists
    exact ⟨hf.1, p, hp⟩
  obtain ⟨p₁, hp₁⟩ := hfprop.2
  set A₁ := (f p₁).toReal with hA₁
  have hp₁A : f p₁ ≤ (A₁ : EReal) := (EReal.coe_toReal hp₁ (hf.1 p₁)).ge
  have hy₀b : legendre f y₀ ≠ ⊥ := legendre_ne_bot f hfprop y₀
  set B₀ := (legendre f y₀).toReal with hB₀
  have hy₀norm : ‖y₀‖ ≤ R := by simpa using hy₀
  set FR := legendre (ballTruncate (legendre f) R) with hFR
  have hFRlow : ∀ p, ((inner ℝ y₀ p - B₀ : ℝ) : EReal) ≤ FR p := by
    intro p
    have h := le_iSup (fun q => (inner ℝ q p : EReal) - ballTruncate (legendre f) R q) y₀
    rwa [ballTruncate_of_norm_le _ hy₀norm, ← EReal.coe_toReal hy₀t hy₀b, ← EReal.coe_sub] at h
  have hFRup : ∀ p, FR p ≤ ((R * ‖p - p₁‖ + A₁ : ℝ) : EReal) := fun p =>
    legendre_ballTruncate_le_add hp₁A R p
  have hFRle : ∀ p, FR p ≤ f p := fun p =>
    (legendre_antitone (le_ballTruncate _ R) p).trans (biconjugate_le f hfprop p)
  set FRr : E → ℝ := fun p => (FR p).toReal with hFRr
  have hFRr_eq : ∀ p, FR p = (FRr p : EReal) := fun p =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hFRup p))
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hFRlow p))).symm
  set CF : ℝ := R * ‖p₁‖ + |A₁| + |B₀| with hCF
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hFRbd : ∀ p, |FRr p| ≤ R * ‖p‖ + CF := by
    intro p
    have h1 := hFRlow p
    rw [hFRr_eq, EReal.coe_le_coe_iff] at h1
    have h2 := hFRup p
    rw [hFRr_eq, EReal.coe_le_coe_iff] at h2
    have hin : |inner ℝ y₀ p| ≤ R * ‖p‖ :=
      (abs_real_inner_le_norm y₀ p).trans (mul_le_mul_of_nonneg_right hy₀norm (norm_nonneg _))
    have hn : ‖p - p₁‖ ≤ ‖p‖ + ‖p₁‖ := norm_sub_le _ _
    have hRn : R * ‖p - p₁‖ ≤ R * (‖p‖ + ‖p₁‖) := mul_le_mul_of_nonneg_left hn hR0
    rw [abs_le]
    constructor
    · nlinarith [le_abs_self B₀, (abs_le.mp hin).1, abs_nonneg A₁,
        mul_nonneg hR0 (norm_nonneg p₁)]
    · nlinarith [le_abs_self A₁, abs_nonneg B₀]
  have hFRm : Measurable FRr :=
    measurable_ereal_toReal.comp (lowerSemicontinuous_legendre _).measurable
  have hFRdom : ∀ y ∈ closedBall (0 : E) R, ∀ p,
      D y ≤ ENNReal.ofReal (Real.exp (FRr p - inner ℝ p y)) := by
    intro y hy p
    by_cases hyt : legendre f y = ⊤
    · rw [hD, density, hyt]; simp
    have hyb := legendre_ne_bot f hfprop y
    have h := le_iSup (fun q => (inner ℝ q p : EReal) - ballTruncate (legendre f) R q) y
    rw [ballTruncate_of_norm_le _ (by simpa using hy), ← EReal.coe_toReal hyt hyb,
      ← EReal.coe_sub] at h
    change _ ≤ FR p at h
    rw [hFRr_eq, EReal.coe_le_coe_iff] at h
    rw [hD, density_eq_ofReal' hyt hyb]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by rw [real_inner_comm]; linarith))
  -- the perturbation `H = F_R − ψ*`
  set φ := legendre ψ with hφ
  set H : E → ℝ := fun p => FRr p - (φ p).toReal with hH
  have hφm : Measurable fun p => (φ p).toReal :=
    measurable_ereal_toReal.comp (lowerSemicontinuous_legendre ψ).measurable
  have hHm : Measurable H := hFRm.sub hφm
  have hφint := potentialIntegrable_legendre hψ hlsc hmass
  have hnormμ := integrable_norm_ofPotential hψ hlsc h0 htop
  have hFRμ : Integrable FRr μ :=
    Integrable.mono' ((hnormμ.const_mul R).add (integrable_const CF)) hFRm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hFRbd p)
  have hHμ : Integrable H μ := hFRμ.sub hφint.2.2
  have hHle : ∫ p, H p ∂μ ≤ (∫ p, (f p).toReal ∂μ) - ∫ p, (φ p).toReal ∂μ := by
    rw [integral_sub hFRμ hφint.2.2]
    have hmono : ∫ p, FRr p ∂μ ≤ ∫ p, (f p).toReal ∂μ := by
      refine integral_mono_ae hFRμ hf.2.2 ?_
      filter_upwards [hf.2.1] with p hp
      exact EReal.toReal_le_toReal (hFRle p) (by rw [hFRr_eq]; exact EReal.coe_ne_bot _) hp
    linarith
  suffices hHmain : ∫⁻ y, g y ≤ ENNReal.ofReal (Real.exp (∫ p, H p ∂μ)) from
    hHmain.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hHle))
  -- the truncated potentials
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set G := goodSet ψ with hG
  have hΨm : Measurable Ψ := measurable_ereal_toReal.comp hlsc.measurable
  have hGm : MeasurableSet G :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ)
  set Ψk : ℕ → E → ℝ := fun k x => (legendre (ballTruncate φ (c + k)) x).toReal with hΨk
  have hk : ∀ k : ℕ, c ≤ c + k := fun k => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hfink := fun k : ℕ => legendre_ballTruncate_ne_top_ne_bot hlow hc.le (hk k) hx₁
  have hconvk : ∀ k, ConvexOn ℝ univ (Ψk k) := fun k =>
    convexOn_toReal_legendre_ballTruncate hlow hc.le (hk k) hx₁
  have hcontk : ∀ k, Continuous (Ψk k) := fun k =>
    continuousOn_univ.mp ((hconvk k).continuousOn isOpen_univ)
  have hlowk : ∀ k x, c * ‖x‖ - b ≤ Ψk k x := fun k x => by
    have h := linear_lower_bound_legendre_ballTruncate hlow hc.le (hk k) x
    rwa [← EReal.coe_toReal (hfink k x).1 (hfink k x).2, EReal.coe_le_coe_iff] at h
  have hgradk : ∀ k x, ‖gradient (Ψk k) x‖ ≤ c + k := fun k x =>
    norm_gradient_toReal_legendre_ballTruncate_le hlow hc.le (hk k) hx₁ x
  have hattk : ∀ k x, DifferentiableAt ℝ (Ψk k) x →
      φ (gradient (Ψk k) x) = ((inner ℝ x (gradient (Ψk k) x) - Ψk k x : ℝ) : EReal) :=
    fun k x hd => (legendre_gradient_toReal_legendre_ballTruncate hψ hlow hc.le (hk k) hx₁ hd).2
  have hbdk := fun k => integrable_exp_neg_of_linear (hcontk k).measurable hc (hlowk k)
  -- `H` at gradient points
  have hφx₁ : ∀ p, ((inner ℝ x₁ p - Ψ x₁ : ℝ) : EReal) ≤ φ p := fun p => by
    have h := le_iSup (fun x => (inner ℝ x p : EReal) - ψ x) x₁
    rwa [← EReal.coe_toReal hx₁ (hψ.1 x₁), ← EReal.coe_sub] at h
  set C₁ : ℝ := |CF| + |Ψ x₁| with hC₁
  set C₂ : ℝ := R + ‖x₁‖ with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hHup : ∀ k x, DifferentiableAt ℝ (Ψk k) x →
      H (gradient (Ψk k) x) ≤ C₁ + C₂ * ‖gradient (Ψk k) x‖ := by
    intro k x hd
    set p := gradient (Ψk k) x
    have h1 := hφx₁ p
    rw [hattk k x hd, EReal.coe_le_coe_iff] at h1
    have h2 : (φ p).toReal = inner ℝ x p - Ψk k x := by rw [hattk k x hd, EReal.toReal_coe]
    have hin : -(‖x₁‖ * ‖p‖) ≤ inner ℝ x₁ p := by
      have := abs_real_inner_le_norm x₁ p
      linarith [neg_abs_le (inner ℝ x₁ p)]
    have hF := (abs_le.mp (hFRbd p)).2
    simp only [hH, h2]
    nlinarith [le_abs_self CF, le_abs_self (Ψ x₁), neg_abs_le (Ψ x₁)]
  have hHabs : ∀ k x, DifferentiableAt ℝ (Ψk k) x →
      |H (gradient (Ψk k) x)| ≤ (R * (c + k) + CF) + (c + k) * ‖x‖ + |Ψk k x| := by
    intro k x hd
    set p := gradient (Ψk k) x
    have h2 : (φ p).toReal = inner ℝ x p - Ψk k x := by rw [hattk k x hd, EReal.toReal_coe]
    have hF := hFRbd p
    have hpn := hgradk k x
    have hpx : ‖p‖ * ‖x‖ ≤ (c + k) * ‖x‖ := mul_le_mul_of_nonneg_right hpn (norm_nonneg _)
    have hin : |inner ℝ x p| ≤ (c + k) * ‖x‖ :=
      (abs_real_inner_le_norm x p).trans (by rw [mul_comm]; exact hpx)
    have hRp : R * ‖p‖ ≤ R * (c + k) := mul_le_mul_of_nonneg_left hpn hR0
    simp only [hH, h2]
    calc |FRr p - (inner ℝ x p - Ψk k x)| ≤ |FRr p| + |inner ℝ x p| + |Ψk k x| := by
          have := abs_sub (FRr p) (inner ℝ x p - Ψk k x)
          have := abs_sub (inner ℝ x p) (Ψk k x)
          linarith
      _ ≤ _ := by linarith
  have hHintk : ∀ k, Integrable fun w => Real.exp (-Ψk k w) * H (gradient (Ψk k) w) := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hbdk k
    refine Integrable.mono' (((h1.const_mul (R * (c + k) + CF)).add (h2.const_mul (c + k))).add h3)
      ((Real.measurable_exp.comp (hcontk k).measurable.neg).mul
        (hHm.comp
          (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.measurable_gradient
            (Ψk k)))).aestronglyMeasurable ?_
    filter_upwards [(hconvk k).ae_differentiableAt_of_isOpen volume isOpen_univ] with w hw
    have hb := hHabs k w (hw (mem_univ w))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he := Real.exp_pos (-Ψk k w)
    calc Real.exp (-Ψk k w) * |H (gradient (Ψk k) w)| ≤
        Real.exp (-Ψk k w) * ((R * (c + k) + CF) + (c + k) * ‖w‖ + |Ψk k w|) :=
          mul_le_mul_of_nonneg_left hb he.le
      _ = _ := by simp only [Pi.add_apply]; ring
  -- the finite Theorem 8 for each truncation
  have hstep : ∀ k, ∫⁻ y, g y ≤ ENNReal.ofReal (Real.exp ((∫ w, Real.exp (-Ψk k w) *
      H (gradient (Ψk k) w)) / (∫ w, Real.exp (-Ψk k w)) +
        Real.log (∫ w, Real.exp (-Ψk k w)))) := by
    intro k
    refine lintegral_le_exp_of_convexOn (hconvk k) (hbdk k).1 hHm (hHintk k) hgm fun w hw y => ?_
    by_cases hy : y ∈ closedBall (0 : E) R
    · rw [hg, indicator_of_mem hy]
      refine (hFRdom y hy (gradient (Ψk k) w)).trans (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (le_of_eq ?_)))
      have h2 : (φ (gradient (Ψk k) w)).toReal = inner ℝ w (gradient (Ψk k) w) - Ψk k w := by
        rw [hattk k w hw, EReal.toReal_coe]
      simp only [hH, h2, inner_sub_right, real_inner_comm w]
      ring
    · rw [hg, indicator_of_notMem hy]; exact zero_le
  -- the agreement sets
  set B := stdOrthonormalBasis ℝ E with hB
  set A : ℕ → Set E := fun k => G ∩ {x | ‖gradient Ψ x‖ ≤ c + k} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hGm.inter (measurableSet_le (continuous_norm.measurable.comp (measurable_gradient_toReal ψ))
      measurable_const)
  have hAev : ∀ x ∈ G, ∀ᶠ k : ℕ in atTop, x ∈ A k := by
    intro x hx
    obtain ⟨K, hK⟩ := exists_nat_ge (‖gradient Ψ x‖ - c)
    filter_upwards [eventually_ge_atTop K] with k hk'
    have : (K : ℝ) ≤ k := Nat.cast_le.mpr hk'
    exact ⟨hx, show ‖gradient Ψ x‖ ≤ c + k by linarith⟩
  have hagree : ∀ k, ∀ᵐ x ∂(volume : Measure E), x ∈ A k →
      Ψk k x = Ψ x ∧ gradient (Ψk k) x = gradient Ψ x := by
    intro k
    filter_upwards [(hconvk k).ae_differentiableAt_of_isOpen volume isOpen_univ] with x hdk hx
    exact toReal_legendre_ballTruncate_eq hψ hlsc hc.le hlow (hk k) hx.1.1 hx.1.2 hx.2
      (hdk (mem_univ x))
  -- the limit densities
  set g₀ : E → ℝ := G.indicator fun x => Real.exp (-Ψ x) * H (gradient Ψ x) with hg₀
  set g₁ : E → ℝ := G.indicator fun x => Real.exp (-Ψ x) with hg₁
  have hdm : Measurable (density ψ) := EReal.measurable_exp.comp hlsc.measurable.neg
  have hdens_ae : ∀ᵐ x ∂(volume : Measure E), (density ψ x).toReal = g₁ x := by
    filter_upwards [ae_mem_interior_differentiableAt hψ] with x hx
    by_cases hxt : ψ x = ⊤
    · have hxG : x ∉ G := fun h => interior_subset h.1 hxt
      rw [hg₁, indicator_of_notMem hxG, density, hxt]; simp
    have hxG : x ∈ G := hx hxt
    rw [hg₁, indicator_of_mem hxG, density_eq_ofReal' hxt (hψ.1 x),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hHint0 : Integrable fun x => H (gradient Ψ x) * (density ψ x).toReal := by
    have h := hHμ
    rw [hμ, ofPotential, integrable_map_measure hHm.aestronglyMeasurable
      (measurable_gradient_toReal ψ).aemeasurable, weightedMeasure,
      integrable_withDensity_iff hdm (Eventually.of_forall fun x => by
        rw [density, EReal.exp_lt_top_iff, lt_top_iff_ne_top]
        exact fun h => hψ.1 x (EReal.neg_eq_top_iff.mp h))] at h
    exact h
  have hg₀ae : (fun x => H (gradient Ψ x) * (density ψ x).toReal) =ᵐ[volume] g₀ := by
    filter_upwards [hdens_ae] with x hx
    rw [hx, hg₀, hg₁]
    by_cases hxG : x ∈ G
    · rw [indicator_of_mem hxG, indicator_of_mem hxG, mul_comm]
    · rw [indicator_of_notMem hxG, indicator_of_notMem hxG, mul_zero]
  have hg₀int : Integrable g₀ := hHint0.congr hg₀ae
  have hg₀μ : ∫ x, g₀ x = ∫ p, H p ∂μ := by
    rw [hμ, integral_ofPotential volume hlsc.measurable hψ.1 hHm, ← integral_congr_ae hg₀ae]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hg₁int : Integrable g₁ := by
    have h : Integrable fun x => (density ψ x).toReal :=
      integrable_toReal_of_lintegral_ne_top hdm.aemeasurable (by rw [← mass, hmass]; simp)
    exact h.congr hdens_ae
  have hg₁one : ∫ x, g₁ x = 1 := by
    rw [← integral_congr_ae hdens_ae, integral_toReal hdm.aemeasurable
      (Eventually.of_forall fun x => by
        rw [density, EReal.exp_lt_top_iff, lt_top_iff_ne_top]
        exact fun h => hψ.1 x (EReal.neg_eq_top_iff.mp h)), ← mass, hmass, ENNReal.toReal_one]
  -- convergence of the truncated masses
  set Z : ℕ → ℝ := fun k => ∫ w, Real.exp (-Ψk k w) with hZ
  have hZpos : ∀ k, 0 < Z k := fun k => integral_exp_pos (hbdk k).1
  have hZlim : Tendsto Z atTop (𝓝 1) := by
    have h := tendsto_lintegral_density_truncate hψ hlsc hc hlow hx₁
    rw [hmass] at h
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
    rw [ENNReal.toReal_one] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, hZ]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w => (Real.exp_pos _).le)
      (hbdk k).1.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun w => ?_
    exact density_eq_ofReal' (hfink k w).1 (hfink k w).2
  -- the three error terms
  set P1 : ℕ → ℝ := fun k => ∫ x, (A k).indicator g₀ x with hP1
  set P2 : ℕ → ℝ := fun k => ∫ x, (A k)ᶜ.indicator (fun x => Real.exp (-Ψk k x)) x with hP2
  set P3 : ℕ → Fin (Module.finrank ℝ E) → ℝ := fun k i => ∫ x, (A k)ᶜ.indicator
    (fun x => |inner ℝ (gradient (Ψk k) x) (B i)| * Real.exp (-Ψk k x)) x with hP3
  set U : ℕ → ℝ := fun k => P1 k + C₁ * P2 k + C₂ * ∑ i, P3 k i with hU
  have hP3int : ∀ k i, Integrable ((A k)ᶜ.indicator
      (fun x => |inner ℝ (gradient (Ψk k) x) (B i)| * Real.exp (-Ψk k x))) := by
    intro k i
    refine (Integrable.mono' ((hbdk k).1.const_mul (c + k)) ?_ (Eventually.of_forall fun x => ?_)
      ).indicator ((hAm k).compl)
    · exact ((continuous_abs.measurable.comp (Measurable.inner
        (FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.measurable_gradient
          (Ψk k)) measurable_const)).mul
        (Real.measurable_exp.comp (hcontk k).measurable.neg)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      exact (abs_real_inner_le_norm _ _).trans (by
        rw [(B.orthonormal.1 i), mul_one]; exact hgradk k x)
  have hTU : ∀ k, (∫ w, Real.exp (-Ψk k w) * H (gradient (Ψk k) w)) ≤ U k := by
    intro k
    have hint_u : Integrable fun x => (A k).indicator g₀ x +
        C₁ * (A k)ᶜ.indicator (fun x => Real.exp (-Ψk k x)) x +
        C₂ * ∑ i, (A k)ᶜ.indicator
          (fun x => |inner ℝ (gradient (Ψk k) x) (B i)| * Real.exp (-Ψk k x)) x :=
      ((hg₀int.indicator (hAm k)).add (((hbdk k).1.indicator (hAm k).compl).const_mul C₁)).add
        ((integrable_finsetSum _ fun i _ => hP3int k i).const_mul C₂)
    have hU_eq : U k = ∫ x, ((A k).indicator g₀ x +
        C₁ * (A k)ᶜ.indicator (fun x => Real.exp (-Ψk k x)) x +
        C₂ * ∑ i, (A k)ᶜ.indicator
          (fun x => |inner ℝ (gradient (Ψk k) x) (B i)| * Real.exp (-Ψk k x)) x) := by
      have h1 : Integrable fun x => (A k).indicator g₀ x := hg₀int.indicator (hAm k)
      have h2 : Integrable fun x => C₁ * (A k)ᶜ.indicator (fun x => Real.exp (-Ψk k x)) x :=
        ((hbdk k).1.indicator (hAm k).compl).const_mul C₁
      have h3 : Integrable fun x => C₂ * ∑ i, (A k)ᶜ.indicator
          (fun x => |inner ℝ (gradient (Ψk k) x) (B i)| * Real.exp (-Ψk k x)) x :=
        (integrable_finsetSum _ fun i _ => hP3int k i).const_mul C₂
      have h12 : Integrable fun x => (A k).indicator g₀ x +
          C₁ * (A k)ᶜ.indicator (fun x => Real.exp (-Ψk k x)) x := h1.add h2
      rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun i _ => hP3int k i]
    rw [hU_eq]
    refine integral_mono_ae (hHintk k) hint_u ?_
    filter_upwards [hagree k, (hconvk k).ae_differentiableAt_of_isOpen volume isOpen_univ]
      with x hxa hdk
    by_cases hx : x ∈ A k
    · obtain ⟨h1, h2⟩ := hxa hx
      have hxc : x ∉ (A k)ᶜ := fun h => h hx
      rw [indicator_of_mem hx]
      simp only [indicator_of_notMem hxc, mul_zero, Finset.sum_const_zero, add_zero]
      rw [hg₀, indicator_of_mem hx.1, h1, h2]
    · rw [indicator_of_notMem hx, indicator_of_mem (show x ∈ (A k)ᶜ from hx), zero_add]
      simp only [indicator_of_mem (show x ∈ (A k)ᶜ from hx)]
      have hup := hHup k x (hdk (mem_univ x))
      have hnorm := norm_le_sum_abs_inner (gradient (Ψk k) x)
      have he := Real.exp_pos (-Ψk k x)
      calc Real.exp (-Ψk k x) * H (gradient (Ψk k) x)
          ≤ Real.exp (-Ψk k x) * (C₁ + C₂ * ∑ i, |inner ℝ (gradient (Ψk k) x) (B i)|) := by
            refine mul_le_mul_of_nonneg_left (hup.trans ?_) he.le
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hC₂0)
        _ = C₁ * Real.exp (-Ψk k x) + C₂ * ∑ i, |inner ℝ (gradient (Ψk k) x) (B i)| *
            Real.exp (-Ψk k x) := by rw [← Finset.sum_mul]; ring
  -- limits of the error terms
  have hP1lim : Tendsto P1 atTop (𝓝 (∫ p, H p ∂μ)) := by
    rw [← hg₀μ]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g₀ x‖)
      (fun k => (hg₀int.indicator (hAm k)).aestronglyMeasurable) hg₀int.norm
      (fun k => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _)
      (Eventually.of_forall fun x => ?_)
    by_cases hxG : x ∈ G
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [hAev x hxG] with k hk'
        show g₀ x = (A k).indicator g₀ x
        rw [indicator_of_mem hk'])
    · have h0' : g₀ x = 0 := by rw [hg₀, indicator_of_notMem hxG]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
      show g₀ x = (A k).indicator g₀ x
      by_cases hk' : x ∈ A k
      · rw [indicator_of_mem hk']
      · rw [indicator_of_notMem hk', h0']
  have hQlim : Tendsto (fun k => ∫ x, (A k).indicator g₁ x) atTop (𝓝 1) := by
    rw [← hg₁one]
    refine tendsto_integral_of_dominated_convergence (fun x => ‖g₁ x‖)
      (fun k => (hg₁int.indicator (hAm k)).aestronglyMeasurable) hg₁int.norm
      (fun k => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _)
      (Eventually.of_forall fun x => ?_)
    by_cases hxG : x ∈ G
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [hAev x hxG] with k hk'
        show g₁ x = (A k).indicator g₁ x
        rw [indicator_of_mem hk'])
    · have h0' : g₁ x = 0 := by rw [hg₁, indicator_of_notMem hxG]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
      show g₁ x = (A k).indicator g₁ x
      by_cases hk' : x ∈ A k
      · rw [indicator_of_mem hk']
      · rw [indicator_of_notMem hk', h0']
  have hP2eq : ∀ k, P2 k = Z k - ∫ x, (A k).indicator g₁ x := by
    intro k
    have hsplit : ∫ x, Real.exp (-Ψk k x) = (∫ x, (A k).indicator (fun x => Real.exp (-Ψk k x)) x) +
        ∫ x, (A k)ᶜ.indicator (fun x => Real.exp (-Ψk k x)) x := by
      rw [← integral_add ((hbdk k).1.indicator (hAm k)) ((hbdk k).1.indicator (hAm k).compl)]
      exact integral_congr_ae (Eventually.of_forall fun x =>
        (indicator_self_add_compl_apply (A k) (fun x => Real.exp (-Ψk k x)) x).symm)
    have hag : ∫ x, (A k).indicator (fun x => Real.exp (-Ψk k x)) x =
        ∫ x, (A k).indicator g₁ x := by
      refine integral_congr_ae ?_
      filter_upwards [hagree k] with x hxa
      by_cases hx : x ∈ A k
      · rw [indicator_of_mem hx, indicator_of_mem hx, hg₁, indicator_of_mem hx.1, (hxa hx).1]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx]
    simp only [hP2, hZ]
    rw [hsplit, hag]
    ring
  have hP2lim : Tendsto P2 atTop (𝓝 0) := by
    have h := hZlim.sub hQlim
    rw [sub_self] at h
    exact h.congr fun k => (hP2eq k).symm
  have hP3lim : ∀ i, Tendsto (fun k => P3 k i) atTop (𝓝 0) := by
    intro i
    have h := tendsto_lintegral_compl_directional hψ hess h0 htop hc hlow hx₁ (B.orthonormal.1 i)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, hP3]
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
        indicator_nonneg (fun y _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) x)
      (hP3int k i).aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ (A k)ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
  have hUlim : Tendsto U atTop (𝓝 (∫ p, H p ∂μ)) := by
    have h := (hP1lim.add (hP2lim.const_mul C₁)).add
      ((tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        fun i _ => hP3lim i).const_mul C₂)
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at h
    exact h
  have hlim : Tendsto (fun k => U k / Z k + Real.log (Z k)) atTop (𝓝 (∫ p, H p ∂μ)) := by
    have h := (hUlim.div hZlim one_ne_zero).add
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hZlim)
    simp only [div_one, Real.log_one, add_zero] at h
    exact h
  refine ge_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp
    ((Real.continuous_exp.tendsto _).comp hlim)) fun k => ?_
  refine (hstep k).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hd := div_le_div_of_nonneg_right (hTU k) (hZpos k).le
  change _ / Z k + Real.log (Z k) ≤ _
  linarith

/-- **CEK Theorem 8 for essentially continuous potentials** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, Theorem 8, (18)), in the form `ψ*` maximizes `I_μ`: let
`ψ : E → ℝ ∪ {+∞}` be convex and essentially continuous with `∫ e^{-ψ} = 1` and moment measure
`μ`. Then for every `μ`-integrable `f : E → ℝ ∪ {±∞}`,
`log ∫ e^{-f*} − ∫ f dμ ≤ log ∫ e^{-ψ**} − ∫ ψ* dμ = −∫ ψ* dμ`. With `f = ψ₁*` for a convex
`ψ₁`, this is (18): `log ∫ e^{-ψ₁} ≤ ∫ (ψ₁* − ψ*) dμ`. -/
theorem variationalFunctional_le_legendre (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (hmass : mass volume ψ = 1) {f : E → EReal}
    (hf : PotentialIntegrable f (ofPotential volume ψ)) :
    variationalFunctional volume (ofPotential volume ψ) f ≤
      variationalFunctional volume (ofPotential volume ψ) (legendre ψ) := by
  have hlsc := hess.1
  set μ := ofPotential volume ψ with hμ
  have h0 : mass volume ψ ≠ 0 := by rw [hmass]; exact one_ne_zero
  obtain ⟨x₁, hx₁I⟩ := interior_domain_nonempty_of_mass_ne_zero volume hψ h0
  have hne : ∃ x, ψ x ≠ ⊤ := ⟨x₁, interior_subset hx₁I⟩
  have hbi : legendre (legendre ψ) = ψ := legendre_legendre_eq hψ hlsc hne
  set L := (∫ p, (f p).toReal ∂μ) - ∫ p, (legendre ψ p).toReal ∂μ with hL
  -- the whole mass, by monotone convergence over balls
  have hmain : mass volume (legendre f) ≤ ENNReal.ofReal (Real.exp L) := by
    have hsup : density (legendre f) = fun y =>
        ⨆ R : ℕ, (closedBall (0 : E) R).indicator (density (legendre f)) y := by
      funext y
      obtain ⟨R, hR⟩ := exists_nat_ge ‖y‖
      refine le_antisymm ?_ (iSup_le fun R => indicator_le_self _ _ y)
      refine le_trans (le_of_eq ?_) (le_iSup _ R)
      rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hR)]
    rw [mass, hsup, lintegral_iSup (fun R => (measurable_density_legendre f).indicator
      measurableSet_closedBall) (fun i j hij y => indicator_le_indicator_of_subset
        (closedBall_subset_closedBall (Nat.cast_le.mpr hij)) (fun _ => zero_le) y)]
    exact iSup_le fun R => lintegral_indicator_closedBall_le hψ hess hmass hf R
  simp only [variationalFunctional, hbi, hmass, ENNReal.log_one, zero_sub]
  have hlog := ENNReal.log_le_log hmain
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at hlog
  calc ENNReal.log (mass volume (legendre f)) - ((∫ p, (f p).toReal ∂μ : ℝ) : EReal)
      ≤ (L : EReal) - ((∫ p, (f p).toReal ∂μ : ℝ) : EReal) := EReal.sub_le_sub hlog le_rfl
    _ = -((∫ p, (legendre ψ p).toReal ∂μ : ℝ) : EReal) := by
        rw [← EReal.coe_sub, ← EReal.coe_neg, hL]
        congr 1
        ring

end Maximality

end FunctionalInequalities.Probability.MomentMeasure
