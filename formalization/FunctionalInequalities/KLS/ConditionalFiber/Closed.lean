import FunctionalInequalities.Energy.Dirichlet
import FunctionalInequalities.Energy.WeightedGradient.Core
import FunctionalInequalities.KLS.ConditionalFiber
import FunctionalInequalities.Probability.TwoPointVariance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# The conditional-fiber form is a Dirichlet energy

Source: Blueprint `lem:conditional-fiber-form`: the conditional-fiber form of
`def:conditional-fiber-form` is densely defined, closed, symmetric, Markovian and reversible.
Read `twoPointMeasure`, `jump`, `energyAt_eq_jump_div`, then `energy_le_of_lipschitzWith`,
`dense_domain`, `lowerSemicontinuous_form`, `closedQuadratic`, `markovian` and `dirichlet`.

On a nondegenerate fiber the normalized variance is the integral of the squared two-point
difference against the symmetric two-point measure `μ_{θ,z} ⊗ μ_{θ,z}`, divided by twice the
fiber variance (`energyAt_eq_jump_div`, using the two-point variance identity). This jump
representation gives every structural property at once: the two-point measure is invariant
under the swap of its coordinates (reversibility, `twoPointMeasure_swap`); the integrand is a
symmetric quadratic expression, giving the quadratic identities; Fatou's lemma along an
almost-everywhere convergent subsequence gives lower semicontinuity on `L²(μ)`; normal
contractions decrease every squared difference (the Markov property); and a globally
`L`-Lipschitz test has fiber energy at most `L²`, so the smooth compactly supported classes lie
in the finite domain, which is therefore dense.

No hypothesis on the law `μ` or on the direction law `ρ` is needed: the statements hold for every
Borel probability law on a finite-dimensional inner-product space and every probability law on the
unit sphere. Nothing here compares the form with a gradient energy, bounds it by a fiber Poincaré
constant, or asserts a frame bound or a Poincaré inequality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.KLS.ConditionalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

section Fiber

variable (κ : Kernel (Direction E × E) ℝ) [IsMarkovKernel κ] (b : Direction E × E)

/-- The two-point measure of a conditional fiber: the product of the fiber law with itself. -/
abbrev twoPointMeasure : Measure (ℝ × ℝ) := (κ b).prod (κ b)

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- Reversibility: the two-point measure is invariant under exchanging its two coordinates. -/
theorem twoPointMeasure_swap :
    (twoPointMeasure κ b).map Prod.swap = twoPointMeasure κ b :=
  Measure.prod_swap

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- Every two-point functional integrates equally in the two orders of its arguments. -/
theorem lintegral_twoPointMeasure_swap (F : ℝ × ℝ → ENNReal) :
    ∫⁻ p, F p.swap ∂twoPointMeasure κ b = ∫⁻ p, F p ∂twoPointMeasure κ b :=
  lintegral_prod_swap F

/-- The squared jump integral of a test along a conditional fiber. -/
def jump (f : E → ℝ) : ENNReal :=
  ∫⁻ p, ‖f (reconstruct b p.1) - f (reconstruct b p.2)‖ₑ ^ 2 ∂twoPointMeasure κ b

omit [SecondCountableTopology E] [IsMarkovKernel κ] in
/-- The jump integrand of a Borel test is measurable on the two-point space. -/
theorem measurable_jump_integrand {f : E → ℝ} (hf : Measurable f) :
    Measurable fun p : ℝ × ℝ ↦ ‖f (reconstruct b p.1) - f (reconstruct b p.2)‖ₑ ^ 2 :=
  ((hf.comp ((measurable_reconstruct_left b).comp measurable_fst)).sub
    (hf.comp ((measurable_reconstruct_left b).comp measurable_snd))).enorm.pow_const 2

omit [SecondCountableTopology E] in
/-- The two-point identity along a fiber: twice the fiber variance of a Borel test is its squared
jump integral. -/
theorem two_mul_evariance_eq_jump {f : E → ℝ} (hf : Measurable f) :
    2 * evariance (fun t ↦ f (reconstruct b t)) (κ b) = jump κ b f :=
  Probability.two_mul_evariance_eq_lintegral_prod (κ b)
    (hf.comp (measurable_reconstruct_left b)).aestronglyMeasurable

omit [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] in
/-- Twice the fiber variance of the scalar coordinate is the two-point integral of `|t - s|²`. -/
theorem two_mul_evariance_id :
    2 * evariance id (κ b) = ∫⁻ p, ‖p.1 - p.2‖ₑ ^ 2 ∂twoPointMeasure κ b :=
  Probability.two_mul_evariance_eq_lintegral_prod (κ b) aestronglyMeasurable_id

omit [BorelSpace E] [SecondCountableTopology E] [IsMarkovKernel κ] in
/-- Degenerate fibers contribute zero, by definition. -/
theorem energyAt_of_not_nondegenerate (hb : ¬ Nondegenerate κ b) (f : E → ℝ) :
    energyAt κ b f = 0 := by
  unfold energyAt
  rw [if_neg hb]

omit [SecondCountableTopology E] in
/-- Jump representation of the fiber energy: on a nondegenerate fiber the normalized variance is
the squared jump integral divided by twice the fiber variance of the coordinate. -/
theorem energyAt_eq_jump_div {f : E → ℝ} (hf : Measurable f) (hb : Nondegenerate κ b) :
    energyAt κ b f = jump κ b f / (2 * evariance id (κ b)) := by
  rw [← two_mul_evariance_eq_jump κ b hf,
    ENNReal.mul_div_mul_left _ _ two_ne_zero ENNReal.ofNat_ne_top]
  unfold energyAt
  rw [if_pos hb]

omit [BorelSpace E] [SecondCountableTopology E] in
/-- A globally `L`-Lipschitz test has squared jump integral at most `L²` times the two-point
integral of `|t - s|²`, because `‖θ‖ = 1`. -/
theorem jump_le_of_lipschitzWith {g : E → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    jump κ b g ≤ (L : ENNReal) ^ 2 * (2 * evariance id (κ b)) := by
  rw [two_mul_evariance_id, ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  refine lintegral_mono fun p ↦ ?_
  rw [← mul_pow]
  refine pow_le_pow_left' ?_ 2
  have hdiff : reconstruct b p.1 - reconstruct b p.2 = (p.1 - p.2) • b.1.1 := by
    simp only [reconstruct, sub_smul]
    abel
  calc ‖g (reconstruct b p.1) - g (reconstruct b p.2)‖ₑ
      = edist (g (reconstruct b p.1)) (g (reconstruct b p.2)) := (edist_eq_enorm_sub _ _).symm
    _ ≤ L * edist (reconstruct b p.1) (reconstruct b p.2) := hg.edist_le_mul _ _
    _ = L * ‖p.1 - p.2‖ₑ := by
      rw [edist_eq_enorm_sub, hdiff, enorm_smul, ← ofReal_norm b.1.1, b.1.2,
        ENNReal.ofReal_one, mul_one]

omit [SecondCountableTopology E] in
/-- A globally `L`-Lipschitz test has fiber energy at most `L²` on every fiber. -/
theorem energyAt_le_of_lipschitzWith {g : E → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    energyAt κ b g ≤ (L : ENNReal) ^ 2 := by
  by_cases hb : Nondegenerate κ b
  · rw [energyAt_eq_jump_div κ b hg.continuous.measurable hb]
    have hσ0 : 2 * evariance id (κ b) ≠ 0 := mul_ne_zero two_ne_zero hb.2.2
    have hσtop : 2 * evariance id (κ b) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top hb.2.1.evariance_ne_top
    rw [ENNReal.div_le_iff hσ0 hσtop]
    exact jump_le_of_lipschitzWith κ b hg
  · rw [energyAt_of_not_nondegenerate κ b hb]
    exact zero_le

omit [BorelSpace E] [SecondCountableTopology E] [IsMarkovKernel κ] in
/-- The zero test has zero fiber energy. -/
theorem energyAt_zero : energyAt κ b (0 : E → ℝ) = 0 := by
  unfold energyAt
  split_ifs
  · have h : (fun t : ℝ ↦ (0 : E → ℝ) (reconstruct b t)) = (0 : ℝ → ℝ) := rfl
    rw [h, evariance_zero, ENNReal.zero_div]
  · rfl

omit [BorelSpace E] [SecondCountableTopology E] [IsMarkovKernel κ] in
/-- Fiber energy is homogeneous of degree two, including the zero scalar. -/
theorem energyAt_mul (c : ℝ) (f : E → ℝ) :
    energyAt κ b (fun x ↦ c * f x) = ENNReal.ofReal (c ^ 2) * energyAt κ b f := by
  unfold energyAt
  split_ifs
  · have h : (fun t : ℝ ↦ (fun x ↦ c * f x) (reconstruct b t)) =
        fun t ↦ c * f (reconstruct b t) := rfl
    rw [h, evariance_mul, mul_div_assoc]
  · rw [mul_zero]

omit [BorelSpace E] [SecondCountableTopology E] [IsMarkovKernel κ] in
private theorem enorm_sq_parallelogram (a c : ℝ) :
    ‖a + c‖ₑ ^ 2 + ‖a - c‖ₑ ^ 2 = 2 * ‖a‖ₑ ^ 2 + 2 * ‖c‖ₑ ^ 2 := by
  have h : ∀ x : ℝ, ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := fun x ↦ by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  have h2 : ∀ x : ℝ, (2 : ENNReal) * ENNReal.ofReal (x ^ 2) = ENNReal.ofReal (2 * x ^ 2) :=
    fun x ↦ by rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  rw [h, h, h, h, h2, h2, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

omit [SecondCountableTopology E] in
/-- The parallelogram identity of the fiber energy, in `[0, ∞]`. -/
theorem energyAt_add_sub {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) :
    energyAt κ b (fun x ↦ f x + g x) + energyAt κ b (fun x ↦ f x - g x) =
      2 * energyAt κ b f + 2 * energyAt κ b g := by
  by_cases hb : Nondegenerate κ b
  · rw [energyAt_eq_jump_div κ b (f := fun x ↦ f x + g x) (hf.add hg) hb,
      energyAt_eq_jump_div κ b (f := fun x ↦ f x - g x) (hf.sub hg) hb,
      energyAt_eq_jump_div κ b hf hb, energyAt_eq_jump_div κ b hg hb, ← ENNReal.add_div,
      ← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div]
    congr 1
    unfold jump
    beta_reduce
    rw [← lintegral_add_left (measurable_jump_integrand b (f := fun x ↦ f x + g x) (hf.add hg)),
      ← lintegral_const_mul _ (measurable_jump_integrand b hf),
      ← lintegral_const_mul _ (measurable_jump_integrand b hg),
      ← lintegral_add_left ((measurable_jump_integrand b hf).const_mul _)]
    refine lintegral_congr fun p ↦ ?_
    have e1 : f (reconstruct b p.1) + g (reconstruct b p.1) -
        (f (reconstruct b p.2) + g (reconstruct b p.2)) =
        (f (reconstruct b p.1) - f (reconstruct b p.2)) +
          (g (reconstruct b p.1) - g (reconstruct b p.2)) := by ring
    have e2 : f (reconstruct b p.1) - g (reconstruct b p.1) -
        (f (reconstruct b p.2) - g (reconstruct b p.2)) =
        (f (reconstruct b p.1) - f (reconstruct b p.2)) -
          (g (reconstruct b p.1) - g (reconstruct b p.2)) := by ring
    rw [e1, e2]
    exact enorm_sq_parallelogram _ _
  · simp only [energyAt_of_not_nondegenerate κ b hb, add_zero, mul_zero]

omit [SecondCountableTopology E] in
/-- Normal contractions do not increase the fiber energy: every squared difference decreases. -/
theorem energyAt_comp_le (φ : Energy.NormalContraction) {f : E → ℝ} (hf : Measurable f) :
    energyAt κ b (fun x ↦ φ (f x)) ≤ energyAt κ b f := by
  by_cases hb : Nondegenerate κ b
  · rw [energyAt_eq_jump_div κ b (f := fun x ↦ φ (f x)) (φ.lipschitz.continuous.measurable.comp hf) hb,
      energyAt_eq_jump_div κ b hf hb]
    refine ENNReal.div_le_div_right (lintegral_mono fun p ↦ ?_) _
    refine pow_le_pow_left' ?_ 2
    rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub]
    simpa using φ.lipschitz.edist_le_mul (f (reconstruct b p.1)) (f (reconstruct b p.2))
  · rw [energyAt_of_not_nondegenerate κ b hb]
    exact zero_le

omit [SecondCountableTopology E] in
/-- Fatou along a fiber: almost-everywhere convergence of Borel tests along the fiber gives lower
semicontinuity of the fiber energy. -/
theorem energyAt_le_liminf {fs : ℕ → E → ℝ} {f : E → ℝ} (hfs : ∀ n, Measurable (fs n))
    (hf : Measurable f)
    (h : ∀ᵐ t ∂κ b, Tendsto (fun n ↦ fs n (reconstruct b t)) atTop (𝓝 (f (reconstruct b t)))) :
    energyAt κ b f ≤ liminf (fun n ↦ energyAt κ b (fs n)) atTop := by
  by_cases hb : Nondegenerate κ b
  · simp_rw [energyAt_eq_jump_div κ b hf hb, energyAt_eq_jump_div κ b (hfs _) hb]
    have hjump : jump κ b f ≤ liminf (fun n ↦ jump κ b (fs n)) atTop := by
      have h1 : ∀ᵐ p ∂twoPointMeasure κ b,
          Tendsto (fun n ↦ fs n (reconstruct b p.1)) atTop (𝓝 (f (reconstruct b p.1))) :=
        Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h
      have h2 : ∀ᵐ p ∂twoPointMeasure κ b,
          Tendsto (fun n ↦ fs n (reconstruct b p.2)) atTop (𝓝 (f (reconstruct b p.2))) :=
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually h
      have hpt : ∀ᵐ p ∂twoPointMeasure κ b,
          ‖f (reconstruct b p.1) - f (reconstruct b p.2)‖ₑ ^ 2 =
            liminf (fun n ↦ ‖fs n (reconstruct b p.1) - fs n (reconstruct b p.2)‖ₑ ^ 2) atTop := by
        filter_upwards [h1, h2] with p hp1 hp2
        exact (((ENNReal.continuous_pow 2).tendsto _).comp (hp1.sub hp2).enorm).liminf_eq.symm
      unfold jump
      rw [lintegral_congr_ae hpt]
      exact lintegral_liminf_le fun n ↦ measurable_jump_integrand b (hfs n)
    calc jump κ b f / (2 * evariance id (κ b))
        ≤ liminf (fun n ↦ jump κ b (fs n)) atTop / (2 * evariance id (κ b)) :=
          ENNReal.div_le_div_right hjump _
      _ ≤ liminf (fun n ↦ jump κ b (fs n) / (2 * evariance id (κ b))) atTop := by
          simp_rw [div_eq_mul_inv]
          have := ENNReal.le_liminf_mul (u := fun n ↦ jump κ b (fs n))
            (v := fun _ ↦ (2 * evariance id (κ b))⁻¹) (f := atTop)
          rwa [liminf_const] at this
  · simp only [energyAt_of_not_nondegenerate κ b hb]
    exact zero_le

end Fiber

variable (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))

/-- A globally `L`-Lipschitz Borel test has conditional-fiber energy at most `d L²`. -/
theorem energy_le_of_lipschitzWith {g : E → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    energy μ ρ g ≤ (Module.finrank ℝ E : ENNReal) * (L : ENNReal) ^ 2 := by
  unfold energy energyWithKernel
  refine mul_le_mul' le_rfl ?_
  calc ∫⁻ b, energyAt (kernel μ ρ) b g ∂baseLaw μ ρ
      ≤ ∫⁻ _, (L : ENNReal) ^ 2 ∂baseLaw μ ρ :=
        lintegral_mono fun b ↦ energyAt_le_of_lipschitzWith _ b hg
    _ = (L : ENNReal) ^ 2 := by simp

/-- A globally Lipschitz Borel test has finite conditional-fiber energy. -/
theorem energy_ne_top_of_lipschitzWith {g : E → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    energy μ ρ g ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (energy_le_of_lipschitzWith μ ρ hg)

/-- The conditional-fiber form as an extended energy functional on `L²(μ)`. -/
def functional : Energy.Functional (Lp ℝ 2 (μ : Measure E)) := ⟨form μ ρ⟩

@[simp]
theorem functional_apply (f : Lp ℝ 2 (μ : Measure E)) : functional μ ρ f = form μ ρ f := rfl

/-- The finite domain of the functional is the maximal domain of the definition. -/
theorem domain_functional : (functional μ ρ).domain = domain μ ρ := rfl

/-- The form of an `L²` class is the energy of any Borel representative. -/
theorem form_eq_energy_of_ae_eq {f : Lp ℝ 2 (μ : Measure E)} {g : E → ℝ} (hg : Measurable g)
    (h : ⇑f =ᵐ[(μ : Measure E)] g) : form μ ρ f = energy μ ρ g :=
  energy_congr_ae μ ρ _ g (Lp.stronglyMeasurable f).measurable hg (Lp.memLp f)
    ((Lp.memLp f).ae_eq h) h

section Dense

variable [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Smooth compactly supported classes have finite conditional-fiber energy. -/
theorem smoothCore_subset_domain :
    (Energy.WeightedGradient.smoothCore μ : Set (Lp ℝ 2 (μ : Measure E))) ⊆
      (functional μ ρ).domain := by
  intro f hf
  obtain ⟨g, hg, hs, rfl⟩ := (Energy.WeightedGradient.mem_smoothCore_iff μ f).1 hf
  obtain ⟨L, hL⟩ := Energy.WeightedGradient.lipschitzWith_of_contDiff_hasCompactSupport hg hs
  change form μ ρ _ ≠ ⊤
  rw [form_toLp μ ρ g hg.continuous.measurable]
  exact energy_ne_top_of_lipschitzWith μ ρ hL

/-- The conditional-fiber form is densely defined. -/
theorem dense_domain : Dense (functional μ ρ).domain :=
  (Energy.WeightedGradient.dense_smoothCore μ).mono (smoothCore_subset_domain μ ρ)

end Dense

/-- The zero class has zero form. -/
theorem form_zero : form μ ρ 0 = 0 := by
  rw [form_eq_energy_of_ae_eq μ ρ (g := (0 : E → ℝ)) measurable_zero
    (Lp.coeFn_zero ℝ 2 (μ : Measure E))]
  unfold energy energyWithKernel
  simp [energyAt_zero]

/-- The form is homogeneous of degree two. -/
theorem form_smul (c : ℝ) (f : Lp ℝ 2 (μ : Measure E)) :
    form μ ρ (c • f) = ENNReal.ofReal (c ^ 2) * form μ ρ f := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have h : ⇑(c • f) =ᵐ[(μ : Measure E)] fun x ↦ c * f x := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx]
    rfl
  rw [form_eq_energy_of_ae_eq μ ρ (g := fun x ↦ c * f x) (measurable_const.mul hf) h]
  unfold form energy energyWithKernel
  simp_rw [energyAt_mul]
  rw [lintegral_const_mul _ (measurable_energyAt _ _ hf), mul_left_comm]

/-- The extended parallelogram identity of the form. -/
theorem form_parallelogram (f g : Lp ℝ 2 (μ : Measure E)) :
    form μ ρ (f + g) + form μ ρ (f - g) = 2 * form μ ρ f + 2 * form μ ρ g := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hadd : ⇑(f + g) =ᵐ[(μ : Measure E)] fun x ↦ f x + g x := by
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx]
    rfl
  have hsub : ⇑(f - g) =ᵐ[(μ : Measure E)] fun x ↦ f x - g x := by
    filter_upwards [Lp.coeFn_sub f g] with x hx
    rw [hx]
    rfl
  rw [form_eq_energy_of_ae_eq μ ρ (hf.add hg) hadd, form_eq_energy_of_ae_eq μ ρ (hf.sub hg) hsub]
  unfold form energy energyWithKernel
  rw [← mul_add, ← lintegral_add_left (measurable_energyAt _ _ (hf.add hg)),
    mul_left_comm (2 : ENNReal), mul_left_comm (2 : ENNReal), ← mul_add,
    ← lintegral_const_mul _ (measurable_energyAt _ _ hf),
    ← lintegral_const_mul _ (measurable_energyAt _ _ hg),
    ← lintegral_add_left ((measurable_energyAt _ _ hf).const_mul _)]
  congr 1
  exact lintegral_congr fun b ↦ energyAt_add_sub _ b hf hg

/-- Normal contractions of `L²(μ)` classes do not increase the form. -/
theorem form_compL2_le (φ : Energy.NormalContraction) (f : Lp ℝ 2 (μ : Measure E)) :
    form μ ρ (φ.compL2 (μ : Measure E) f) ≤ form μ ρ f := by
  have hf := (Lp.stronglyMeasurable f).measurable
  rw [form_eq_energy_of_ae_eq μ ρ (φ.lipschitz.continuous.measurable.comp hf)
    (φ.coeFn_compL2 (μ : Measure E) f)]
  unfold form energy energyWithKernel
  exact mul_le_mul' le_rfl (lintegral_mono fun b ↦ energyAt_comp_le _ b φ hf)

/-- The conditional-fiber form is Markovian. -/
theorem markovian : Energy.Markovian (μ : Measure E) (functional μ ρ) :=
  fun φ f ↦ form_compL2_le μ ρ φ f

/-- Disintegration and Fatou: the energy of Borel representatives is lower semicontinuous along
`μ`-almost-everywhere convergent sequences. -/
theorem energy_le_liminf {fs : ℕ → E → ℝ} {f : E → ℝ} (hfs : ∀ n, Measurable (fs n))
    (hf : Measurable f)
    (h : ∀ᵐ x ∂(μ : Measure E), Tendsto (fun n ↦ fs n x) atTop (𝓝 (f x))) :
    energy μ ρ f ≤ liminf (fun n ↦ energy μ ρ (fs n)) atTop := by
  have hS : MeasurableSet {q : (Direction E × E) × ℝ |
      Tendsto (fun n ↦ fs n (reconstruct q.1 q.2) - f (reconstruct q.1 q.2)) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 0) fun n ↦
      ((hfs n).comp measurable_reconstruct).sub (hf.comp measurable_reconstruct)
  have hjoint : ∀ᵐ q ∂jointLaw μ ρ,
      Tendsto (fun n ↦ fs n (reconstruct q.1 q.2) - f (reconstruct q.1 q.2)) atTop (𝓝 0) := by
    rw [jointLaw, ae_map_iff measurable_coordinates.aemeasurable hS]
    simp only [reconstruct_coordinates]
    have h' : ∀ᵐ x ∂(μ : Measure E), Tendsto (fun n ↦ fs n x - f x) atTop (𝓝 0) :=
      h.mono fun x hx ↦ tendsto_sub_nhds_zero_iff.2 hx
    exact Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually h'
  rw [← compProd_baseLaw_kernel] at hjoint
  have hbase := Measure.ae_ae_of_ae_compProd hjoint
  have hb : ∀ᵐ b ∂baseLaw μ ρ,
      energyAt (kernel μ ρ) b f ≤ liminf (fun n ↦ energyAt (kernel μ ρ) b (fs n)) atTop := by
    filter_upwards [hbase] with b hb
    exact energyAt_le_liminf _ b hfs hf (hb.mono fun t ht ↦ tendsto_sub_nhds_zero_iff.1 ht)
  unfold energy energyWithKernel
  calc (Module.finrank ℝ E : ENNReal) * ∫⁻ b, energyAt (kernel μ ρ) b f ∂baseLaw μ ρ
      ≤ (Module.finrank ℝ E : ENNReal) *
          ∫⁻ b, liminf (fun n ↦ energyAt (kernel μ ρ) b (fs n)) atTop ∂baseLaw μ ρ :=
        mul_le_mul' le_rfl (lintegral_mono_ae hb)
    _ ≤ (Module.finrank ℝ E : ENNReal) *
          liminf (fun n ↦ ∫⁻ b, energyAt (kernel μ ρ) b (fs n) ∂baseLaw μ ρ) atTop :=
        mul_le_mul' le_rfl (lintegral_liminf_le fun n ↦ measurable_energyAt _ _ (hfs n))
    _ ≤ liminf (fun n ↦ (Module.finrank ℝ E : ENNReal) *
          ∫⁻ b, energyAt (kernel μ ρ) b (fs n) ∂baseLaw μ ρ) atTop := by
        have := ENNReal.le_liminf_mul (u := fun _ ↦ (Module.finrank ℝ E : ENNReal))
          (v := fun n ↦ ∫⁻ b, energyAt (kernel μ ρ) b (fs n) ∂baseLaw μ ρ) (f := atTop)
        rwa [liminf_const] at this

/-- Closedness: the conditional-fiber form is lower semicontinuous on `L²(μ)`. -/
theorem lowerSemicontinuous_form :
    LowerSemicontinuous fun f : Lp ℝ 2 (μ : Measure E) ↦ form μ ρ f := by
  apply LowerSemicontinuous.of_frequently
  intro f y hfreq
  obtain ⟨fs, hfs, hbound⟩ := exists_seq_forall_of_frequently hfreq
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' fs f).1 hfs
  have hinm : TendstoInMeasure (μ : Measure E) (fun n ↦ ⇑(fs n)) atTop ⇑f :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun n ↦ Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable f) hnorm
  obtain ⟨ns, -, hae⟩ := hinm.exists_seq_tendsto_ae
  calc form μ ρ f = energy μ ρ ⇑f := rfl
    _ ≤ liminf (fun k ↦ energy μ ρ ⇑(fs (ns k))) atTop :=
        energy_le_liminf μ ρ (fun k ↦ (Lp.stronglyMeasurable _).measurable)
          (Lp.stronglyMeasurable f).measurable hae
    _ ≤ y := by
        refine liminf_le_of_le (by isBoundedDefault) fun c hc ↦ ?_
        obtain ⟨k, hk⟩ := hc.exists
        exact hk.trans (hbound (ns k))

section Closed

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The conditional-fiber form is a densely defined closed quadratic form on `L²(μ)`. -/
theorem closedQuadratic : Energy.ClosedQuadratic (functional μ ρ) where
  zero := form_zero μ ρ
  smul_of_ne_zero c _ f := form_smul μ ρ c f
  parallelogram := form_parallelogram μ ρ
  lowerSemicontinuous := lowerSemicontinuous_form μ ρ
  dense_domain := dense_domain μ ρ

/-- The conditional-fiber form is a Dirichlet energy: densely defined, closed, quadratic and
Markovian. -/
theorem dirichlet : Energy.Dirichlet (μ : Measure E) (functional μ ρ) :=
  ⟨closedQuadratic μ ρ, markovian μ ρ⟩

end Closed

end FunctionalInequalities.KLS.ConditionalFiber
