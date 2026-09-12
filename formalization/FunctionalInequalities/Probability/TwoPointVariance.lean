import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Two-point representation of the variance

Source: Blueprint `lem:conditional-fiber-form`, the identity
`Var(X) = (1/2) ∬ (X(t) - X(s))² dν(t) dν(s)` used for the jump-form representation of the
conditional-fiber energy. For a probability law `ν` the extended variance of a real variable `X`
equals one half of the integral of `‖X t - X s‖ₑ²` against `ν ⊗ ν`; the identity holds in
`[0, ∞]` without a square-integrability premise, both sides being `⊤` exactly when `X ∉ L²(ν)`.
-/

open MeasureTheory ProbabilityTheory Filter

namespace FunctionalInequalities.Probability

variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

/-- The real two-point identity for a square-integrable variable. -/
theorem integral_sub_sq_prod {X : Ω → ℝ} (hX : MemLp X 2 ν) :
    ∫ p, (X p.1 - X p.2) ^ 2 ∂(ν.prod ν) = 2 * variance X ν := by
  set m : ℝ := ∫ ω, X ω ∂ν with hm
  set Y : Ω → ℝ := fun ω ↦ X ω - m with hY
  have hY2 : MemLp Y 2 ν := hX.sub (memLp_const m)
  have hYsq : Integrable (fun ω ↦ Y ω ^ 2) ν := hY2.integrable_sq
  have hYint : Integrable Y ν := hY2.integrable one_le_two
  have hYmean : ∫ ω, Y ω ∂ν = 0 := by
    show ∫ ω, (X ω - m) ∂ν = 0
    rw [integral_sub (hX.integrable one_le_two) (integrable_const m), integral_const,
      probReal_univ, one_smul, hm, sub_self]
  have hν0 : ν ≠ 0 := IsProbabilityMeasure.ne_zero ν
  have h1 : Integrable (fun p : Ω × Ω ↦ Y p.1 ^ 2) (ν.prod ν) :=
    (Integrable.comp_fst_iff hν0).2 hYsq
  have h2 : Integrable (fun p : Ω × Ω ↦ Y p.2 ^ 2) (ν.prod ν) :=
    (Integrable.comp_snd_iff hν0).2 hYsq
  have h3 : Integrable (fun p : Ω × Ω ↦ Y p.1 * Y p.2) (ν.prod ν) := hYint.mul_prod hYint
  have hpt : ∀ p : Ω × Ω,
      (X p.1 - X p.2) ^ 2 = Y p.1 ^ 2 + Y p.2 ^ 2 - 2 * (Y p.1 * Y p.2) := by
    intro p
    simp only [hY]
    ring
  have h12 : Integrable (fun p : Ω × Ω ↦ Y p.1 ^ 2 + Y p.2 ^ 2) (ν.prod ν) := h1.add h2
  simp_rw [hpt]
  rw [integral_sub h12 (h3.const_mul 2), integral_add h1 h2, integral_const_mul,
    integral_prod_mul, hYmean, mul_zero, mul_zero, sub_zero]
  have hfst : ∫ p : Ω × Ω, Y p.1 ^ 2 ∂(ν.prod ν) = ∫ ω, Y ω ^ 2 ∂ν := by
    rw [integral_prod _ h1]
    simp
  have hsnd : ∫ p : Ω × Ω, Y p.2 ^ 2 ∂(ν.prod ν) = ∫ ω, Y ω ^ 2 ∂ν := by
    rw [integral_prod _ h2]
    simp
  rw [hfst, hsnd, variance_eq_integral hX.1.aemeasurable]
  ring

/-- The extended two-point identity: twice the extended variance is the integral of the squared
two-point difference against the product law. Both sides are `⊤` when `X ∉ L²(ν)`. -/
theorem two_mul_evariance_eq_lintegral_prod {X : Ω → ℝ} (hX : AEStronglyMeasurable X ν) :
    2 * evariance X ν = ∫⁻ p, ‖X p.1 - X p.2‖ₑ ^ 2 ∂(ν.prod ν) := by
  have hmeas : AEStronglyMeasurable (fun p : Ω × Ω ↦ X p.1 - X p.2) (ν.prod ν) :=
    (hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
      (hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  by_cases hL : MemLp X 2 ν
  · have hprod : MemLp (fun p : Ω × Ω ↦ X p.1 - X p.2) 2 (ν.prod ν) :=
      (hL.comp_measurePreserving measurePreserving_fst).sub
        (hL.comp_measurePreserving measurePreserving_snd)
    have hint : Integrable (fun p : Ω × Ω ↦ (X p.1 - X p.2) ^ 2) (ν.prod ν) :=
      hprod.integrable_sq
    rw [← ofReal_variance hL,
      show (2 : ENNReal) * ENNReal.ofReal (variance X ν) = ENNReal.ofReal (2 * variance X ν) by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat],
      ← integral_sub_sq_prod ν hL,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    refine lintegral_congr fun p ↦ ?_
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  · rw [evariance_eq_top hX hL, ENNReal.mul_top two_ne_zero]
    by_contra hne
    have hlt : ∫⁻ p, ‖X p.1 - X p.2‖ₑ ^ 2 ∂(ν.prod ν) < ⊤ :=
      lt_top_iff_ne_top.2 (Ne.symm hne)
    have hae : AEMeasurable (fun p : Ω × Ω ↦ ‖X p.1 - X p.2‖ₑ ^ 2) (ν.prod ν) :=
      hmeas.aemeasurable.enorm.pow_const 2
    rw [lintegral_prod _ hae] at hlt
    obtain ⟨x₀, hx₀⟩ := (ae_lt_top' hae.lintegral_prod_right' hlt.ne).exists
    have hmem : MemLp (fun y ↦ X x₀ - X y) 2 ν := by
      refine ⟨aestronglyMeasurable_const.sub hX, ?_⟩
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
      simpa [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hx₀
    have : MemLp X 2 ν := by
      have h : MemLp (fun y ↦ X x₀ - (X x₀ - X y)) 2 ν := (memLp_const (X x₀)).sub hmem
      simpa using h
    exact hL this

end FunctionalInequalities.Probability
