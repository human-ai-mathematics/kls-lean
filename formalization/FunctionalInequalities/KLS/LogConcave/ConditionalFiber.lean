module

public import FunctionalInequalities.KLS.ConditionalFiber.EnergyComparison
public import FunctionalInequalities.KLS.ConditionalFiber.SliceKernel
public import FunctionalInequalities.KLS.LogConcave.Isotropic
public import FunctionalInequalities.KLS.LogConcave.Line.OfDensity
public import FunctionalInequalities.KLS.LogConcave.Line.SharpPoincare

/-!
# Log-concave conditional fibers

Source: Blueprint `cor:conditional-fiber-twelve-bound`. Read `ae_conditionalFiber_logConcave`
(almost every conditional fiber of a full-dimensional log-concave law is a log-concave law on the
line), then the glue on top of the certified comparison
`lem:conditional-fiber-energy-comparison` and the sharp one-dimensional bound
`thm:one-dimensional-logconcave-poincare`: the fiber hypothesis `FiberBound μ ρ 4`, the energy
comparison `D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ`, the constant transfer `C_P^lit(μ) ≤ 4 C`, and the
Blueprint's literal `12` versions derived from `4`.

The analytic content is the disintegration of the Borell density along lines. Absolute continuity
gives full affine support, hence a Borell density `p` for `μ` relative to the reference Haar
measure. `KLS/ConditionalFiber/SliceKernel.lean` builds the explicit Markov kernel with density
`t ↦ p (z + tθ) / Z(θ, z)` and proves that it disintegrates the joint law, so by Mathlib's
uniqueness of conditional kernels it agrees base-law almost everywhere with the chosen kernel. On
base points with positive finite slice mass the normalized line density inherits measurability,
nonnegativity, upper semicontinuity and log-concavity from `p` along the affine reconstruction
map, and `KLS/LogConcave/Line/OfDensity.lean` (one-dimensional Prekopa--Leindler) turns it into
compact-set log-concavity; the remaining base points carry a Dirac law, which is log-concave.

No ledger, certificate, or Blueprint `\leanok` claim is made by this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS.LogConcave

open ConditionalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E} {ρ : ProbabilityMeasure (Direction E)}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- On a base point with positive finite slice mass, the normalized line density is a Borell
density of the explicit slice kernel: measurability, nonnegativity, upper semicontinuity and
log-concavity all descend from the ambient Borell density along the affine reconstruction map. -/
private theorem isBorellDensity_sliceKernel {m : Measure E} [Measure.IsAddHaarMeasure m]
    {p : E → ℝ} (hp : IsBorellDensity (μ : Measure E) m p) {b : Direction E × E}
    (hb : b ∈ ConditionalFiber.SliceGood p) :
    IsBorellDensity (ConditionalFiber.sliceKernel p hp.measurable b) volume
      (fun t ↦ (ConditionalFiber.sliceMass p b).toReal⁻¹ * p (reconstruct b t)) := by
  have hZpos : 0 < (ConditionalFiber.sliceMass p b).toReal :=
    ENNReal.toReal_pos hb.1.ne' hb.2.ne
  have hcpos : 0 < (ConditionalFiber.sliceMass p b).toReal⁻¹ := inv_pos.2 hZpos
  have hrec : Continuous (reconstruct b) := by
    unfold reconstruct
    fun_prop
  refine ⟨(hp.measurable.comp (measurable_reconstruct_left b)).const_mul _,
    fun t ↦ mul_nonneg hcpos.le (hp.nonneg _),
    Continuous.comp_upperSemicontinuous (g := fun x : ℝ ↦ _ * x)
      (continuous_const.mul continuous_id) (hp.upperSemicontinuous.comp hrec)
      (fun a c hac ↦ mul_le_mul_of_nonneg_left hac hcpos.le), ?_, ?_⟩
  · intro x y s hs0 hs1
    have hcomb : s • reconstruct b x + (1 - s) • reconstruct b y =
        reconstruct b (s • x + (1 - s) • y) := by
      simp only [reconstruct, smul_add, smul_smul, smul_eq_mul, add_smul]
      module
    have hlc := hp.logConcave (reconstruct b x) (reconstruct b y) s hs0 hs1
    rw [hcomb] at hlc
    calc ((ConditionalFiber.sliceMass p b).toReal⁻¹ * p (reconstruct b x)) ^ s *
          ((ConditionalFiber.sliceMass p b).toReal⁻¹ * p (reconstruct b y)) ^ (1 - s)
        = ((ConditionalFiber.sliceMass p b).toReal⁻¹ ^ s *
            (ConditionalFiber.sliceMass p b).toReal⁻¹ ^ (1 - s)) *
            (p (reconstruct b x) ^ s * p (reconstruct b y) ^ (1 - s)) := by
          rw [Real.mul_rpow hcpos.le (hp.nonneg _), Real.mul_rpow hcpos.le (hp.nonneg _)]
          ring
      _ = (ConditionalFiber.sliceMass p b).toReal⁻¹ *
            (p (reconstruct b x) ^ s * p (reconstruct b y) ^ (1 - s)) := by
          rw [← Real.rpow_add hcpos]
          norm_num
      _ ≤ (ConditionalFiber.sliceMass p b).toReal⁻¹ *
            p (reconstruct b (s • x + (1 - s) • y)) := mul_le_mul_of_nonneg_left hlc hcpos.le
  · rw [ConditionalFiber.sliceKernel_eq_withDensity_of_good hp.measurable hb]
    congr 1
    funext t
    rw [ENNReal.ofReal_mul hcpos.le, ENNReal.ofReal_inv_of_pos hZpos,
      ENNReal.ofReal_toReal hb.2.ne, ConditionalFiber.sliceDensity, ENNReal.div_eq_inv_mul]

-- The corollary block retains admissibility and ambient structure in its shared interface.
-- The unused explicit `hρ` keeps its local unused-variable exception.
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] μ ρ in
set_option linter.unusedVariables false in
/-- Blueprint: "Fubini disintegration of the log-concave density gives conditional densities
proportional to `t ↦ ρ_μ(z + tθ)` wherever the normalizing slice integral is finite and positive.
These densities are log-concave. The remaining fibers are null." The chosen disintegration kernel
of the joint law is, base-law almost everywhere, a log-concave law on the line. -/
theorem ae_conditionalFiber_logConcave
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} {ρ : ProbabilityMeasure (Direction E)}
    (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
    ∀ᵐ b ∂baseLaw μ ρ,
      LogConcave (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ) := by
  obtain ⟨p, hp⟩ := hμ.exists_isBorellDensity_of_interior_support_nonempty m
    (hμ.interior_support_nonempty_of_affineSupport_eq_top
      (ConditionalFiber.affineSupport_eq_top_of_absolutelyContinuous μ m hac)) hac
  filter_upwards [ConditionalFiber.ae_sliceKernel_eq μ ρ m hp.measurable hp.withDensity_eq]
    with b hb
  have hlc : LogConcave (⟨ConditionalFiber.sliceKernel p hp.measurable b, inferInstance⟩ :
      ProbabilityMeasure ℝ) := by
    by_cases hg : b ∈ ConditionalFiber.SliceGood p
    · exact LineDensity.logConcave ⟨_, isBorellDensity_sliceKernel hp hg⟩
    · intro K₀ K₁ hK₀ hK₁ t ht0 ht1
      have hd := logConcave_dirac (0 : ℝ) K₀ K₁ hK₀ hK₁ t ht0 ht1
      simpa [ConditionalFiber.sliceKernel_apply_of_not_good hp.measurable hg] using hd
  have hb' : (⟨ConditionalFiber.sliceKernel p hp.measurable b, inferInstance⟩ :
      ProbabilityMeasure ℝ) = ⟨kernel μ ρ b, inferInstance⟩ := Subtype.ext hb
  rwa [hb'] at hlc

/-- Blueprint: "Apply `thm:one-dimensional-logconcave-poincare`": the sharp bound `4 Var` on every
log-concave fiber is the fiber hypothesis of the comparison lemma with `κ = 4`. -/
theorem conditionalFiber_fiberBound_four (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
    FiberBound μ ρ 4 := by
  filter_upwards [hμ.ae_conditionalFiber_logConcave hρ m hac] with b hb _
  have h := hb.localSlope_constant_le_four_evariance
  simpa using h

/-- The Blueprint's displayed inequality with the sharp input: `D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ < ∞` on
the literature test domain. -/
theorem conditionalFiber_energy_le_four_mul (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m)
    {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ 4 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤ := by
  have h := energy_le_of_fiberBound μ ρ hρ m hac (hμ.conditionalFiber_fiberBound_four hρ m hac) hf
  simpa using h

/-- The Blueprint's "A finite form-gap bound `C` therefore gives `C_P^lit(μ) ≤ κ C`" with the sharp
input `κ = 4`. -/
theorem conditionalFiber_literatureConstant_le_four_mul (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * (C : ENNReal) := by
  have h := literatureConstant_le_of_fiberBound μ ρ hρ m hac
    (hμ.conditionalFiber_fiberBound_four hρ m hac) hform
  simpa using h

/-- The Blueprint's literal statement `D_{μ,ρ}(f) ≤ 12 ∫‖∇f‖² dμ`, derived from the sharp `4`. -/
theorem conditionalFiber_energy_le_twelve_mul_of_four (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m)
    {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ 12 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤ := by
  obtain ⟨h4, hfin⟩ := hμ.conditionalFiber_energy_le_four_mul hρ m hac hf
  refine ⟨h4.trans (mul_le_mul_left ?_ _), hfin⟩
  norm_num

/-- The Blueprint's literal conclusion `C_P^lit(μ) ≤ 12 C`, derived from the sharp `4`. -/
theorem conditionalFiber_literatureConstant_le_twelve_mul_of_four (hμ : LogConcave μ)
    (hρ : Admissible μ ρ) (m : Measure E) [Measure.IsAddHaarMeasure m]
    (hac : (μ : Measure E) ≪ m) {C : NNReal}
    (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 12 * (C : ENNReal) := by
  refine (hμ.conditionalFiber_literatureConstant_le_four_mul hρ m hac hform).trans
    (mul_le_mul_left ?_ _)
  norm_num

end FunctionalInequalities.KLS.LogConcave
