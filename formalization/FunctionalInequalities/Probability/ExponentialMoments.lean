import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exponential integrability from moment growth

On an arbitrary measure space, moment bounds `∫ |f|^k ≤ A (C k)^k` for every `k` give integrability of `exp(σ|f|)` with
`∫ exp(σ|f|) ≤ 2A` whenever `σ C e ≤ 1/2` (`k^k/k! ≤ e^k` and a geometric series). Extended-valued moments give the same
estimate for `f.toReal` and almost-everywhere finiteness as a conclusion. Moments from order two on suffice with the
prefactor `A(1 + 4C²)`, and a scale `K > 0` in the moments becomes the reciprocal scale `σ/K` in the exponent. These are
the exponential-integrability steps of Gilbarg–Trudinger (2001), Lemma 7.20.
A centered exponential moment of `log s` bounds the product of the positive and negative power moments of `s`
(`integral_rpow_mul_integral_rpow_neg_le_of_log_exp`).
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Probability

/-- **Moment growth gives exponential integrability.** If `∫ |f|^k ≤ A (C k)^k` for every `k` (the case `k = 0` bounds
the total mass by `A`) and `σ C e ≤ 1/2`, then `exp(σ|f|)` is integrable with `∫ exp(σ|f|) ≤ 2A`. -/
theorem integrable_exp_abs_of_moment_growth
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ} {A C σ : ℝ}
    (hf : AEStronglyMeasurable f μ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hsmall : σ * C * Real.exp 1 ≤ 1 / 2)
    (hmom : ∀ k : ℕ, Integrable (fun x => |f x| ^ k) μ ∧
      (∫ x, |f x| ^ k ∂μ) ≤ A * (C * (k : ℝ)) ^ k) :
    Integrable (fun x => Real.exp (σ * |f x|)) μ ∧
      (∫ x, Real.exp (σ * |f x|) ∂μ) ≤ 2 * A := by
  let F := fun (k : ℕ) x => (σ * |f x|) ^ k / (k.factorial : ℝ)
  have hF0 (k : ℕ) (x : X) : 0 ≤ F k x := by dsimp only [F]; positivity
  have hFi (k : ℕ) : Integrable (F k) μ := by
    convert (hmom k).1.const_mul (σ ^ k / (k.factorial : ℝ)) using 1
    ext x
    dsimp only [F]
    rw [mul_pow]
    ring
  have hFb (k : ℕ) : (∫ x, F k x ∂μ) ≤ A * (1 / 2 : ℝ) ^ k := by
    have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hnum : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp 1 ^ k := by
      simpa only [← Real.exp_nat_mul, mul_one] using Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
    have heq : F k = fun x => (σ ^ k / (k.factorial : ℝ)) * |f x| ^ k := by
      ext x
      dsimp only [F]
      rw [mul_pow]
      ring
    rw [heq, integral_const_mul]
    calc
      _ ≤ (σ ^ k / (k.factorial : ℝ)) * (A * (C * (k : ℝ)) ^ k) :=
        mul_le_mul_of_nonneg_left (hmom k).2 (by positivity)
      _ = (A * (σ * C) ^ k) * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by rw [mul_pow, mul_pow]; ring
      _ ≤ (A * (σ * C) ^ k) * Real.exp 1 ^ k := mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = A * (σ * C * Real.exp 1) ^ k := by rw [mul_pow, mul_pow]; ring
      _ ≤ A * (1 / 2 : ℝ) ^ k := by gcongr
  have hgeom : Summable (fun k : ℕ => A * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left A
  have hIs (k : ℕ) : 0 ≤ ∫ x, F k x ∂μ := integral_nonneg (hF0 k)
  have hsum : Summable (fun k : ℕ => ∫ x, F k x ∂μ) :=
    Summable.of_nonneg_of_le hIs hFb hgeom
  have hsumle : (∑' k : ℕ, ∫ x, F k x ∂μ) ≤ 2 * A := by
    calc
      _ ≤ ∑' k : ℕ, A * (1 / 2 : ℝ) ^ k := hsum.tsum_le_tsum hFb hgeom
      _ = 2 * A := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
        ring
  have hpoint (x : X) : HasSum (fun k : ℕ => F k x) (Real.exp (σ * |f x|)) := by
    simpa only [F, Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (σ * |f x|)
  have hlin : (∫⁻ x, ENNReal.ofReal (Real.exp (σ * |f x|)) ∂μ) ≤ ENNReal.ofReal (2 * A) := by
    calc
      _ = ∫⁻ x, ∑' k : ℕ, ENNReal.ofReal (F k x) ∂μ := by
        apply lintegral_congr
        intro x
        rw [← (hpoint x).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 k x) (hpoint x).summable]
      _ = ∑' k : ℕ, ∫⁻ x, ENNReal.ofReal (F k x) ∂μ :=
        lintegral_tsum (fun k => (hFi k).1.aemeasurable.ennreal_ofReal)
      _ = ∑' k : ℕ, ENNReal.ofReal (∫ x, F k x ∂μ) := by
        congr 1
        ext k
        exact (ofReal_integral_eq_lintegral_ofReal (hFi k) (ae_of_all _ (hF0 k))).symm
      _ = ENNReal.ofReal (∑' k : ℕ, ∫ x, F k x ∂μ) :=
        (ENNReal.ofReal_tsum_of_nonneg hIs hsum).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hsumle
  have hExp : Integrable (fun x => Real.exp (σ * |f x|)) μ := by
    refine ⟨?_, ?_⟩
    · simpa only [Real.norm_eq_abs] using
        Real.continuous_exp.comp_aestronglyMeasurable (hf.norm.const_mul σ)
    · apply (hasFiniteIntegral_iff_norm _).mpr
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hExp, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 2 * A)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hExp (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact hlin

/-- **Extended-valued moments.** For `f` with values in `ℝ≥0∞` and `∫ f^k ≤ A (C k)^k` for every `k`, `f` is finite
almost everywhere and `exp(σ f.toReal)` is integrable with integral at most `2A`. -/
theorem integrable_exp_toReal_of_moment_growth
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ≥0∞} {A C σ : ℝ}
    (hf : AEMeasurable f μ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hsmall : σ * C * Real.exp 1 ≤ 1 / 2)
    (hmom : ∀ k : ℕ, (∫⁻ x, (f x) ^ k ∂μ) ≤ ENNReal.ofReal (A * (C * (k : ℝ)) ^ k)) :
    (∀ᵐ x ∂μ, f x < ∞) ∧ Integrable (fun x => Real.exp (σ * (f x).toReal)) μ ∧
      (∫ x, Real.exp (σ * (f x).toReal) ∂μ) ≤ 2 * A := by
  have hfR : AEStronglyMeasurable (fun x => (f x).toReal) μ :=
    hf.ennreal_toReal.aestronglyMeasurable
  have hbound (k : ℕ) : (∫⁻ x, ENNReal.ofReal (|(f x).toReal| ^ k) ∂μ) ≤
      ENNReal.ofReal (A * (C * (k : ℝ)) ^ k) := by
    refine (lintegral_mono fun x => ?_).trans (hmom k)
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    gcongr
    exact ENNReal.ofReal_toReal_le
  have hreal (k : ℕ) : Integrable (fun x => |(f x).toReal| ^ k) μ ∧
      (∫ x, |(f x).toReal| ^ k ∂μ) ≤ A * (C * (k : ℝ)) ^ k := by
    have hi : Integrable (fun x => |(f x).toReal| ^ k) μ := by
      refine ⟨?_, ?_⟩
      · simpa only [Real.norm_eq_abs] using
          (hfR.norm.aemeasurable.pow_const k).aestronglyMeasurable
      · apply (hasFiniteIntegral_iff_norm _).mpr
        simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
          (hbound k).trans_lt ENNReal.ofReal_lt_top
    refine ⟨hi, ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ A * (C * (k : ℝ)) ^ k)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => by positivity)]
    exact hbound k
  have hfin : (∫⁻ x, f x ∂μ) < ∞ := by
    simpa only [pow_one] using (hmom 1).trans_lt ENNReal.ofReal_lt_top
  have hexp := integrable_exp_abs_of_moment_growth μ hfR hA hC hσ hsmall hreal
  refine ⟨ae_lt_top' hf hfin.ne, ?_⟩
  simpa only [abs_of_nonneg ENNReal.toReal_nonneg] using hexp

/-- Moments from order two on, together with the mass bound, suffice with the prefactor `A (1 + 4 C²)` (`C ≥ 1`). -/
private theorem integrable_exp_toReal_of_high_moment_growth
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ≥0∞} {A C σ : ℝ}
    (hf : AEMeasurable f μ) (hA : 0 ≤ A) (hC : 1 ≤ C) (hσ : 0 ≤ σ)
    (hsmall : σ * C * Real.exp 1 ≤ 1 / 2)
    (hmass : μ Set.univ ≤ ENNReal.ofReal A)
    (hmom : ∀ k : ℕ, 2 ≤ k → (∫⁻ x, (f x) ^ k ∂μ) ≤
      ENNReal.ofReal (A * (C * (k : ℝ)) ^ k)) :
    (∀ᵐ x ∂μ, f x < ∞) ∧ Integrable (fun x => Real.exp (σ * (f x).toReal)) μ ∧
      (∫ x, Real.exp (σ * (f x).toReal) ∂μ) ≤ 2 * (A * (1 + 4 * C ^ 2)) := by
  let A' := A * (1 + 4 * C ^ 2)
  have hC0 : 0 ≤ C := by linarith
  have hA' : 0 ≤ A' := by dsimp only [A']; positivity
  have hAA : A ≤ A' := by dsimp only [A']; nlinarith [mul_nonneg hA (sq_nonneg C)]
  have hpoint (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
    by_cases hx : x ≤ 1
    · exact hx.trans (le_add_of_nonneg_right zero_le)
    · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hx)
      calc
        x = x * 1 := by rw [mul_one]
        _ ≤ x * x := mul_le_mul le_rfl hx1 zero_le zero_le
        _ ≤ 1 + x ^ 2 := by rw [pow_two]; exact le_add_of_nonneg_left zero_le
  have h2 : (∫⁻ x, (f x) ^ 2 ∂μ) ≤ ENNReal.ofReal (4 * A * C ^ 2) := by
    have ht := hmom 2 le_rfl
    norm_num only [Nat.cast_ofNat] at ht
    rw [show A * (C * 2) ^ 2 = 4 * A * C ^ 2 by ring] at ht
    exact ht
  have h1 : (∫⁻ x, f x ∂μ) ≤ ENNReal.ofReal A' := by
    calc
      _ ≤ ∫⁻ x, (1 + (f x) ^ 2) ∂μ := lintegral_mono fun x => hpoint (f x)
      _ = μ Set.univ + ∫⁻ x, (f x) ^ 2 ∂μ := by rw [lintegral_add_left measurable_const]; simp
      _ ≤ ENNReal.ofReal A + ENNReal.ofReal (4 * A * C ^ 2) := add_le_add hmass h2
      _ = ENNReal.ofReal A' := by rw [← ENNReal.ofReal_add hA (by positivity)]; congr 1; dsimp only [A']; ring
  have hall (k : ℕ) : (∫⁻ x, (f x) ^ k ∂μ) ≤ ENNReal.ofReal (A' * (C * (k : ℝ)) ^ k) := by
    rcases k with _ | k
    · simpa using hmass.trans (ENNReal.ofReal_le_ofReal hAA)
    rcases k with _ | k
    · simpa using h1.trans (ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right hA' hC))
    · exact (hmom (k + 2) (by omega)).trans (ENNReal.ofReal_le_ofReal (by gcongr))
  exact integrable_exp_toReal_of_moment_growth μ hf hA' hC0 hσ hsmall hall

/-- **Scaled high moments.** If `∫ f^k ≤ A (C K k)^k` for `k ≥ 2` and the mass is at most `A` (`C ≥ 1`, `K > 0`), then
`f < ∞` a.e. and `exp((σ/K) f.toReal)` is integrable with integral at most `2A(1 + 4C²)`; `K` enters only the exponent. -/
theorem integrable_exp_toReal_of_scaled_high_moment_growth
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ≥0∞} {A C K σ : ℝ}
    (hf : AEMeasurable f μ) (hA : 0 ≤ A) (hC : 1 ≤ C) (hK : 0 < K) (hσ : 0 ≤ σ)
    (hsmall : σ * C * Real.exp 1 ≤ 1 / 2)
    (hmass : μ Set.univ ≤ ENNReal.ofReal A)
    (hmom : ∀ k : ℕ, 2 ≤ k → (∫⁻ x, (f x) ^ k ∂μ) ≤
      ENNReal.ofReal (A * (C * K * (k : ℝ)) ^ k)) :
    (∀ᵐ x ∂μ, f x < ∞) ∧ Integrable (fun x => Real.exp ((σ / K) * (f x).toReal)) μ ∧
      (∫ x, Real.exp ((σ / K) * (f x).toReal) ∂μ) ≤ 2 * (A * (1 + 4 * C ^ 2)) := by
  let g := fun x => ENNReal.ofReal (K⁻¹) * f x
  have hg : AEMeasurable g μ := hf.const_mul _
  have hgmom (k : ℕ) (hk : 2 ≤ k) : (∫⁻ x, (g x) ^ k ∂μ) ≤
      ENNReal.ofReal (A * (C * (k : ℝ)) ^ k) := by
    dsimp only [g]
    simp_rw [mul_pow]
    rw [lintegral_const_mul'' _ (hf.pow_const k)]
    calc
      _ ≤ ENNReal.ofReal (K⁻¹) ^ k * ENNReal.ofReal (A * (C * K * (k : ℝ)) ^ k) :=
        mul_le_mul le_rfl (hmom k hk) zero_le zero_le
      _ = _ := by
        rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hK.le),
          ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hK.le) k)]
        congr 1
        rw [show K⁻¹ ^ k * (A * (C * K * (k : ℝ)) ^ k) =
          A * (K⁻¹ * (C * K * (k : ℝ))) ^ k by rw [mul_pow]; ring]
        congr 2
        field_simp [hK.ne']
        rw [mul_pow]
  have H := integrable_exp_toReal_of_high_moment_growth μ hg hA hC hσ hsmall hmass hgmom
  have hfin : ∀ᵐ x ∂μ, f x < ∞ := by
    filter_upwards [H.1] with x hx
    by_contra h
    have hfTop : f x = ∞ := top_unique (not_lt.mp h)
    have hpos : ENNReal.ofReal (K⁻¹) ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hK)).ne'
    simp only [g, hfTop, ENNReal.mul_top hpos, lt_self_iff_false] at hx
  have he (x : X) : σ * (g x).toReal = (σ / K) * (f x).toReal := by
    dsimp only [g]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hK.le)]
    ring
  refine ⟨hfin, ?_⟩
  simpa only [he] using H.2

/-- **Centered log moment controls power moments.** If `s > 0` a.e., `log s` is a.e. measurable and
`∫ exp(p |log s − m|) ≤ A` (`p ≥ 0`), then `s^p` and `s^{-p}` are integrable and `∫ s^p · ∫ s^{-p} ≤ A²`. -/
theorem integral_rpow_mul_integral_rpow_neg_le_of_log_exp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {s : X → ℝ} {p m A : ℝ}
    (hp : 0 ≤ p) (hs : ∀ᵐ x ∂μ, 0 < s x)
    (hlog : AEStronglyMeasurable (fun x => Real.log (s x)) μ)
    (hExp : Integrable (fun x => Real.exp (p * |Real.log (s x) - m|)) μ)
    (hA : (∫ x, Real.exp (p * |Real.log (s x) - m|) ∂μ) ≤ A) :
    Integrable (fun x => (s x)^p) μ ∧ Integrable (fun x => (s x)^(-p)) μ ∧
      (∫ x, (s x)^p ∂μ) * (∫ x, (s x)^(-p) ∂μ) ≤ A^2 := by
  let I := ∫ x, Real.exp (p * |Real.log (s x) - m|) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun x => (Real.exp_pos _).le
  have hA0 : 0 ≤ A := hI.trans hA
  have hpowm (q : ℝ) : AEStronglyMeasurable (fun x => (s x)^q) μ := by
    refine (Real.continuous_exp.comp_aestronglyMeasurable (hlog.const_mul q)).congr ?_
    filter_upwards [hs] with x hx
    simp only [Real.rpow_def_of_pos hx,mul_comm]
  have heq (q : ℝ) (x : X) (hx : 0 < s x) :
      (s x)^q = Real.exp (q * m) * Real.exp (q * (Real.log (s x) - m)) := by
    rw [← Real.exp_add,Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hplus : ∀ᵐ x ∂μ, (s x)^p ≤ Real.exp (p * m) * Real.exp (p * |Real.log (s x) - m|) := by
    filter_upwards [hs] with x hx
    rw [heq p x hx]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hp
  have hminus : ∀ᵐ x ∂μ, (s x)^(-p) ≤ Real.exp (-p * m) * Real.exp (p * |Real.log (s x) - m|) := by
    filter_upwards [hs] with x hx
    rw [heq (-p) x hx]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    calc
      _ = p * (-(Real.log (s x) - m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (neg_le_abs _) hp
  have hplusI : Integrable (fun x => (s x)^p) μ :=
    (hExp.const_mul (Real.exp (p * m))).mono_nonneg (hpowm p)
      (hs.mono fun x hx => Real.rpow_nonneg hx.le _) hplus
  have hminusI : Integrable (fun x => (s x)^(-p)) μ :=
    (hExp.const_mul (Real.exp (-p * m))).mono_nonneg (hpowm (-p))
      (hs.mono fun x hx => Real.rpow_nonneg hx.le _) hminus
  have hplusB : (∫ x, (s x)^p ∂μ) ≤ Real.exp (p * m) * I := by
    simpa only [integral_const_mul] using integral_mono_ae hplusI (hExp.const_mul _) hplus
  have hminusB : (∫ x, (s x)^(-p) ∂μ) ≤ Real.exp (-p * m) * I := by
    simpa only [integral_const_mul] using integral_mono_ae hminusI (hExp.const_mul _) hminus
  have hplus0 : 0 ≤ ∫ x, (s x)^p ∂μ := integral_nonneg_of_ae (hs.mono fun x hx => Real.rpow_nonneg hx.le _)
  have hminus0 : 0 ≤ ∫ x, (s x)^(-p) ∂μ := integral_nonneg_of_ae (hs.mono fun x hx => Real.rpow_nonneg hx.le _)
  refine ⟨hplusI,hminusI,?_⟩
  calc
    _ ≤ (Real.exp (p * m) * I) * (Real.exp (-p * m) * I) :=
      mul_le_mul hplusB hminusB hminus0 (by positivity)
    _ = I^2 := by rw [mul_mul_mul_comm,← Real.exp_add]; simp only [neg_mul,add_neg_cancel,Real.exp_zero,one_mul,pow_two]
    _ ≤ A^2 := by nlinarith

end FunctionalInequalities.Probability
