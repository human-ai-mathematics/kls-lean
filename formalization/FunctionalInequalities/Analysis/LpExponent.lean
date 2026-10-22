import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The `L^p` norms of an essentially bounded function converge to its essential supremum

On a probability space, for an essentially bounded real `f` and ANY sequence of exponents `p k : ℝ≥0` tending to infinity
(no monotonicity, finitely many zero exponents allowed), `‖f‖_{p k} → ‖f‖_∞`, the essential supremum (not a pointwise
supremum). The upper bound is exponent monotonicity on a probability space. For the lower bound at `r < ‖f‖_∞` an
intermediate level `r < t < ‖f‖_∞` has positive finite mass `m`, Chebyshev gives `t m^{1/p} ≤ ‖f‖_p`, and `m^{1/p} → 1`.

This is the exponent limit of a Moser iteration (Gilbarg–Trudinger (2001), Theorem 8.18), not the iteration itself.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.Analysis

/-- A positive finite mass raised to reciprocal exponents tending to infinity tends to one. -/
private lemma tendsto_mass_rpow_inv {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmt : m ≠ ⊤)
    (p : ℕ → NNReal) (hp : Tendsto p atTop atTop) :
    Tendsto (fun k => m ^ ((p k : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun k => (p k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr hp)
  have hm : m.toNNReal ≠ 0 := (ENNReal.toNNReal_pos hm0 hmt).ne'
  have h := (NNReal.continuousAt_rpow (.inl hm)).tendsto.comp (tendsto_const_nhds.prodMk_nhds hinv)
  have he := (ENNReal.continuous_coe.tendsto (m.toNNReal ^ (0 : ℝ))).comp h
  change Tendsto (fun k => ((m.toNNReal ^ ((p k : ℝ)⁻¹) : NNReal) : ENNReal)) atTop
    (𝓝 ((m.toNNReal ^ (0 : ℝ) : NNReal) : ENNReal)) at he
  simpa only [NNReal.rpow_zero, ENNReal.coe_one, ENNReal.coe_rpow_of_ne_zero hm,
    ENNReal.coe_toNNReal hmt] using he

/-- **`L^p` to essential `L^∞`.** On a probability space, for essentially bounded real `f` and exponents `p k → ∞`,
`eLpNorm f (p k) μ → eLpNorm f ⊤ μ`. -/
theorem tendsto_eLpNorm_of_exponents_tendsto_atTop
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : MemLp f ⊤ μ) (p : ℕ → NNReal)
    (hp : Tendsto p atTop atTop) :
    Tendsto (fun k => eLpNorm f (p k : ENNReal) μ) atTop (nhds (eLpNorm f ⊤ μ)) := by
  let L := eLpNorm f ⊤ μ
  have hu (k : ℕ) : eLpNorm f (p k : ENNReal) μ ≤ L :=
    eLpNorm_le_eLpNorm_of_exponent_le le_top hf.1
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro r hr
    obtain ⟨t, hrt, htL⟩ := exists_between hr
    have ht0 : t ≠ 0 := (lt_of_le_of_lt bot_le hrt).ne'
    have htt : t ≠ ⊤ := (htL.trans_le le_top).ne
    let m := μ {x | t ≤ ‖f x‖ₑ}
    have hm0 : m ≠ 0 := by
      intro hm
      have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ t := by
        apply ae_iff.mpr
        apply measure_mono_null (fun x hx => ?_) hm
        exact (lt_of_not_ge hx).le
      have hle : L ≤ t := by
        simpa only [L, eLpNorm_exponent_top] using eLpNormEssSup_le_of_ae_enorm_bound hae
      exact (not_le_of_gt htL) hle
    have hmt : m ≠ ⊤ := measure_ne_top _ _
    have hlim : Tendsto (fun k => t * m ^ ((p k : ℝ)⁻¹)) atTop (𝓝 t) := by
      simpa only [mul_one] using ENNReal.Tendsto.const_mul (a := t) (tendsto_mass_rpow_inv hm0 hmt p hp) (Or.inl one_ne_zero)
    filter_upwards [(tendsto_order.mp hlim).1 r hrt,
      hp.eventually (eventually_gt_atTop (0 : NNReal))] with k hk hpk
    have hpkE : (p k : ENNReal) ≠ 0 := by exact_mod_cast hpk.ne'
    have hpkR : 0 < (p k : ℝ) := by exact_mod_cast hpk
    have hb := mul_meas_ge_le_pow_eLpNorm' μ hpkE ENNReal.coe_ne_top hf.1 t
    have hb' := ENNReal.rpow_le_rpow hb (inv_nonneg.mpr hpkR.le)
    have hleft : (t ^ (p k : ℝ) * m) ^ ((p k : ℝ)⁻¹) = t * m ^ ((p k : ℝ)⁻¹) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hpkR.le), ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hpkR.ne', ENNReal.rpow_one]
    change (t ^ (p k : ℝ) * m) ^ ((p k : ℝ)⁻¹) ≤
      (eLpNorm f (p k : ENNReal) μ ^ (p k : ℝ)) ^ ((p k : ℝ)⁻¹) at hb'
    rw [hleft, ← ENNReal.rpow_mul, mul_inv_cancel₀ hpkR.ne', ENNReal.rpow_one] at hb'
    exact hk.trans_le hb'

  · intro r hr
    exact Eventually.of_forall fun k => (hu k).trans_lt hr


/-! ## Finite measures, powers and essential infima

Measure-level tools for the Moser iterations and the weak Harnack inequality (Gilbarg–Trudinger 2001, Theorem 8.18):
the exponent limit on a finite measure, radius-normalized exponent comparison, exact power/integral and essential-norm
conversions, power integrability from a measurable logarithm, the essential infimum as an inverse `L^∞` norm with the
removal of a positive shift (explicit finite constant), and the moment-to-product step. No weak derivative appears. -/

section FiniteMeasureExponent

open Set

/-- The existing probability-space exponent limit extends to every finite nonzero measure,
by normalizing the measure and retaining the exact mass factor. -/
theorem tendsto_eLpNorm_finite_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    {f : X → ℝ} (hf : MemLp f ∞ μ) (p : ℕ → NNReal)
    (hp : Tendsto p atTop atTop) :
    Tendsto (fun k => eLpNorm f (p k : ENNReal) μ) atTop (𝓝 (eLpNorm f ∞ μ)) := by
  let m := μ univ
  have hm0 : m ≠ 0 := NeZero.ne (μ univ)
  have hmt : m ≠ ∞ := measure_ne_top μ univ
  let ν := m⁻¹ • μ
  have hc0 : m⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmt
  have hct : m⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm0
  have hν : MemLp f ∞ ν := hf.smul_measure hct
  have hlim := FunctionalInequalities.Analysis.tendsto_eLpNorm_of_exponents_tendsto_atTop ν hν p hp
  have hinv : Tendsto (fun k => (p k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr hp)
  have hmNN : m.toNNReal ≠ 0 := (ENNReal.toNNReal_pos hm0 hmt).ne'
  have hmassNN := (NNReal.continuousAt_rpow (.inl hmNN)).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds hinv)
  have hmass : Tendsto (fun k => m ^ ((p k : ℝ)⁻¹)) atTop (𝓝 1) := by
    have H := (ENNReal.continuous_coe.tendsto (m.toNNReal ^ (0 : ℝ))).comp hmassNN
    change Tendsto (fun k => ((m.toNNReal ^ ((p k : ℝ)⁻¹) : NNReal) : ENNReal)) atTop
      (𝓝 ((m.toNNReal ^ (0 : ℝ) : NNReal) : ENNReal)) at H
    simpa only [NNReal.rpow_zero, ENNReal.coe_one, ENNReal.coe_rpow_of_ne_zero hmNN,
      ENNReal.coe_toNNReal hmt] using H
  have hμ : m • ν = μ := by
    dsimp only [ν]
    rw [smul_smul, ENNReal.mul_inv_cancel hm0 hmt, one_smul]
  have hnorm (k : ℕ) : eLpNorm f (p k : ENNReal) μ =
      m ^ ((p k : ℝ)⁻¹) * eLpNorm f (p k : ENNReal) ν := by
    conv_lhs => rw [← hμ]
    rw [eLpNorm_smul_measure_of_ne_zero hm0]
    simp only [one_div, ENNReal.toReal_inv, ENNReal.coe_toReal, smul_eq_mul]
  have htop : eLpNorm f ∞ ν = eLpNorm f ∞ μ := by
    simp only [ν, eLpNorm_exponent_top, eLpNormEssSup_ennreal_smul_measure hc0]
  have H := ENNReal.Tendsto.mul hmass (Or.inl one_ne_zero) hlim (Or.inr ENNReal.one_ne_top)
  simpa only [one_mul, htop, ← hnorm] using H

/-- Exact radius cancellation in finite-measure exponent comparison. The dimensionless mass
factor is retained, including zero and infinite values. -/
theorem radius_normalized_norm_mono_exponent
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) {q p R N : ℝ} (hq : 0 < q) (hp : 0 < p)
    (hqp : q ≤ p) (hR : 0 < R) {M : ℝ≥0∞}
    (hmass : μ Set.univ = M*(ENNReal.ofReal R)^N) :
    (ENNReal.ofReal R)^(-N/q) * eLpNorm f (ENNReal.ofReal q) μ ≤
      M^(1/q-1/p) * ((ENNReal.ofReal R)^(-N/p) * eLpNorm f (ENNReal.ofReal p) μ) := by
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  have hd : 0 ≤ 1/q-1/p := by
    have H := one_div_le_one_div_of_le hq hqp
    linarith
  have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hqp) hf
  rw [ENNReal.toReal_ofReal hq.le,ENNReal.toReal_ofReal hp.le,hmass,
    ENNReal.mul_rpow_of_nonneg _ _ hd,← ENNReal.rpow_mul] at H
  have he : -N/q+N*(1/q-1/p) = -N/p := by ring
  calc
    _ ≤ (ENNReal.ofReal R)^(-N/q) *
        (eLpNorm f (ENNReal.ofReal p) μ * (M^(1/q-1/p)*(ENNReal.ofReal R)^(N*(1/q-1/p)))) :=
      mul_le_mul_of_nonneg_left H zero_le
    _ = M^(1/q-1/p) * (((ENNReal.ofReal R)^(-N/q)*(ENNReal.ofReal R)^(N*(1/q-1/p))) *
        eLpNorm f (ENNReal.ofReal p) μ) := by ac_rfl
    _ = _ := by rw [← ENNReal.rpow_add _ _ hR0 ENNReal.ofReal_ne_top,he]

end FiniteMeasureExponent

section PowerNorms


/-- Exact negative-power/norm conversion for the inverse Moser step, including infinite norms. -/
theorem inverse_power_eLpNorm_square
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : X → ℝ)
    (hs : ∀ x, 0 < s x) {p : ℝ} (hp : 0 < p) (q : ℝ≥0∞) :
    (eLpNorm (fun x => (s x) ^ (-p / 2)) q μ) ^ (2 : ℕ) =
      (eLpNorm (fun x => (s x) ^ (-1 : ℝ)) (q * ENNReal.ofReal (p / 2)) μ) ^ p := by
  have hf : (fun x => (s x) ^ (-p / 2)) =
      fun x => ‖(s x) ^ (-1 : ℝ)‖ ^ (p / 2) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hs x) _), ← Real.rpow_mul (hs x).le]
    congr 1
    ring
  rw [hf, eLpNorm_norm_rpow _ (by positivity : 0 < p / 2)]
  rw [← ENNReal.rpow_mul_natCast]
  congr 1
  simp

/-- The finite real power integral equals the p-th power of the extended Lp norm.
Integrability is an actual premise, so no Bochner junk integral is used. -/
theorem ofReal_integral_rpow_eq_eLpNorm_rpow
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p)
    (hi : Integrable (fun x => (f x) ^ p) μ) :
    ENNReal.ofReal (∫ x, (f x) ^ p ∂μ) = (eLpNorm f (ENNReal.ofReal p) μ) ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  have hcancel : (1 / p) * p = 1 := by field_simp
  rw [hcancel, ENNReal.rpow_one]
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => Real.rpow_nonneg (hf x) _)]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal (hf x), ← ENNReal.ofReal_rpow_of_nonneg (hf x) hp.le]

/-- A bounded `log s` (`s > 0`) gives every real power of `s` in every `L^p` of a finite measure. -/
theorem memLp_rpow_of_bounded_log
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {s : X → ℝ} {C q : ℝ} {p : ENNReal} (hs : ∀ x, 0 < s x)
    (hm : AEStronglyMeasurable (fun x => Real.log (s x)) μ)
    (hb : ∀ x, ‖Real.log (s x)‖ ≤ C) : MemLp (fun x => s x ^ q) p μ := by
  have he : (fun x => s x ^ q) = fun x => Real.exp (q * Real.log (s x)) := by
    funext x
    rw [Real.rpow_def_of_pos (hs x), mul_comm]
  rw [he]
  apply MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable (hm.const_mul q))
    (Real.exp (|q| * C))
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hC : |Real.log (s x)| ≤ C := by simpa only [Real.norm_eq_abs] using hb x
  calc
    _ ≤ |q * Real.log (s x)| := le_abs_self _
    _ = |q| * |Real.log (s x)| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hC (abs_nonneg q)

/-- Every nonpositive power of a positive lower bounded measurable function is in every `Lp`
on a finite measure space. The actual logarithm supplies measurability. -/
theorem memLp_nonpos_power_of_log_measurable
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {s : X → ℝ} {δ t : ℝ} (hδ : 0 < δ) (hs : ∀ x, δ ≤ s x) (ht : t ≤ 0)
    (hm : AEStronglyMeasurable (fun x => Real.log (s x)) μ) (p : ℝ≥0∞) :
    MemLp (fun x => s x ^ t) p μ := by
  have hsp (x : X) : 0 < s x := hδ.trans_le (hs x)
  have hsm : AEStronglyMeasurable s μ := by
    have H := Real.continuous_exp.comp_aestronglyMeasurable hm
    have he : (fun x => Real.exp (Real.log (s x))) = s := funext fun x => Real.exp_log (hsp x)
    rw [he] at H
    exact H
  apply MemLp.of_bound (hsm.aemeasurable.pow_const t).aestronglyMeasurable (δ ^ t)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hsp x) t)]
  exact Real.rpow_le_rpow_of_nonpos hδ (hs x) ht

/-- Convert an actual negative-power Sobolev estimate into an inverse-function `Lp` gain.
Both sides are extended norms, so the identity also handles infinite norms. -/
theorem inverse_norm_power_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (s : X → ℝ)
    (hs : ∀ x, 0 < s x) {p q A : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hI : Integrable (fun x => s x ^ (-p)) μ) {C : ℝ≥0∞}
    (hgain : (eLpNorm (fun x => s x ^ (-p/2)) (ENNReal.ofReal q) ν) ^ (2 : ℕ) ≤
      C * ENNReal.ofReal (A * (∫ x, s x ^ (-p) ∂μ))) :
    (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal ((q/2)*p)) ν) ^ p ≤
      C * ENNReal.ofReal A *
        (eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p) μ) ^ p := by
  have hpow : (fun x => s x ^ (-p)) = (fun x => (s x ^ (-1 : ℝ)) ^ p) := by
    funext x
    rw [← Real.rpow_mul (hs x).le]
    congr 1
    ring
  have hnorm := inverse_power_eLpNorm_square ν s hs hp (ENNReal.ofReal q)
  have hexp : ENNReal.ofReal q * ENNReal.ofReal (p/2) = ENNReal.ofReal ((q/2)*p) := by
    rw [← ENNReal.ofReal_mul hq]
    congr 1
    ring
  rw [hexp] at hnorm
  rw [hnorm, ENNReal.ofReal_mul hA, ← mul_assoc] at hgain
  rw [hpow] at hI hgain
  rw [ofReal_integral_rpow_eq_eLpNorm_rpow μ
    (fun x => s x ^ (-1 : ℝ)) (fun x => (Real.rpow_pos_of_pos (hs x) _).le) hp hI] at hgain
  exact hgain

/-- Exact positive-power conversion of the Sobolev gain, including infinite extended norms.
The real power integral is an actual integrability premise. -/
theorem positive_norm_power_gain
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (s : X → ℝ)
    (hs : ∀ x, 0 ≤ s x) {p q A : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hI : Integrable (fun x => s x ^ p) μ) {C : ℝ≥0∞}
    (hgain : (eLpNorm (fun x => s x ^ (p/2)) (ENNReal.ofReal q) ν) ^ (2 : ℕ) ≤
      C * ENNReal.ofReal (A * (∫ x, s x ^ p ∂μ))) :
    (eLpNorm s (ENNReal.ofReal ((q/2)*p)) ν) ^ p ≤
      C * ENNReal.ofReal A * (eLpNorm s (ENNReal.ofReal p) μ) ^ p := by
  have hf : (fun x => s x ^ (p/2)) = (fun x => ‖s x‖ ^ (p/2)) := by
    funext x
    rw [Real.norm_eq_abs,abs_of_nonneg (hs x)]
  have hnorm : (eLpNorm (fun x => s x ^ (p/2)) (ENNReal.ofReal q) ν) ^ (2 : ℕ) =
      (eLpNorm s (ENNReal.ofReal ((q/2)*p)) ν) ^ p := by
    rw [hf,eLpNorm_norm_rpow _ (by positivity : 0 < p/2),← ENNReal.rpow_mul_natCast]
    have he : ENNReal.ofReal q * ENNReal.ofReal (p/2) = ENNReal.ofReal ((q/2)*p) := by
      rw [← ENNReal.ofReal_mul hq]
      congr 1
      ring
    rw [he]
    congr 1
    ring
  rw [hnorm,ENNReal.ofReal_mul hA,← mul_assoc,
    ofReal_integral_rpow_eq_eLpNorm_rpow μ s hs hp hI] at hgain
  exact hgain

/-- Exact positive-power conversion at the essential endpoint, also for infinite norms. -/
theorem positive_power_eLpNorm_top_square
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : X → ℝ)
    (hs : ∀ x,0 ≤ s x) {p : ℝ} (hp : 0 < p) :
    (eLpNorm (fun x => s x^(p/2)) ∞ μ)^2 = (eLpNorm s ∞ μ)^p := by
  have hf : (fun x => s x^(p/2)) = fun x => ‖s x‖^(p/2) := by
    funext x
    rw [Real.norm_eq_abs,abs_of_nonneg (hs x)]
  rw [hf,eLpNorm_norm_rpow _ (half_pos hp),← ENNReal.rpow_mul_natCast,
    ENNReal.top_mul (ENNReal.ofReal_pos.mpr (half_pos hp)).ne']
  congr 1
  ring

/-- Exact inverse-power conversion at the essential endpoint. -/
theorem inverse_power_eLpNorm_top_square
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : X → ℝ)
    (hs : ∀ x,0 < s x) {p : ℝ} (hp : 0 < p) :
    (eLpNorm (fun x => s x^(-p/2)) ∞ μ)^2 = (eLpNorm (fun x => s x^(-1 : ℝ)) ∞ μ)^p := by
  simpa only [ENNReal.top_mul (ENNReal.ofReal_pos.mpr (half_pos hp)).ne'] using
    inverse_power_eLpNorm_square μ s hs hp ∞

end PowerNorms

section EssentialInfimum


/-- The inverse essential norm is the reciprocal of the ENN-valued essential infimum.
This needs only a.e. positivity; no pointwise infimum or regular representative is asserted. -/
theorem eLpNorm_inverse_eq_inv_essInf
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : X → ℝ}
    (hs : ∀ᵐ x ∂μ, 0 < s x) :
    eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ = (essInf (fun x => ENNReal.ofReal (s x)) μ)⁻¹ := by
  rw [eLpNorm_exponent_top,eLpNormEssSup_eq_essSup_enorm]
  have he : (fun x => ‖s x ^ (-1 : ℝ)‖ₑ) =ᵐ[μ] (fun x => (ENNReal.ofReal (s x))⁻¹) := by
    filter_upwards [hs] with x hx
    rw [Real.rpow_neg_one,Real.enorm_eq_ofReal (inv_pos.mpr hx).le,ENNReal.ofReal_inv_of_pos hx]
  rw [essSup_congr_ae he]
  have H := OrderIso.essInf_apply (fun x => ENNReal.ofReal (s x)) μ OrderIso.invENNReal
  exact H.symm

/-- A positive real function on a nonzero measure has a nonzero inverse essential norm. -/
private theorem eLpNorm_inverse_ne_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [NeZero μ] {s : X → ℝ}
    (hs : ∀ᵐ x ∂μ, 0 < s x) : eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ ≠ 0 := by
  intro hzero
  rw [eLpNorm_exponent_top,eLpNormEssSup_eq_zero_iff] at hzero
  obtain ⟨x,hpos,hz⟩ := (hs.and hzero).exists
  exact (Real.rpow_pos_of_pos hpos (-1 : ℝ)).ne' (by simpa only [Pi.zero_apply] using hz)

/-- A positive lower bound makes the inverse essential norm finite; logarithm measurability
supplies actual measurability of the inverse function. No finite-measure assumption is needed. -/
private theorem eLpNorm_inverse_ne_top_of_lower_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : X → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hs : ∀ᵐ x ∂μ, δ ≤ s x)
    (hm : AEStronglyMeasurable (fun x => Real.log (s x)) μ) :
    eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ ≠ ∞ := by
  have hme : AEStronglyMeasurable (fun x => Real.exp (-Real.log (s x))) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hm.neg
  have he : (fun x => Real.exp (-Real.log (s x))) =ᵐ[μ] (fun x => s x ^ (-1 : ℝ)) := by
    filter_upwards [hs] with x hx
    rw [Real.rpow_neg_one,Real.exp_neg,Real.exp_log (hδ.trans_le hx)]
  have hmi : AEStronglyMeasurable (fun x => s x ^ (-1 : ℝ)) μ := hme.congr he
  have hb : ∀ᵐ x ∂μ, ‖s x ^ (-1 : ℝ)‖ ≤ δ⁻¹ := by
    filter_upwards [hs] with x hx
    rw [Real.rpow_neg_one,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hδ.trans_le hx))]
    exact (inv_le_inv₀ (hδ.trans_le hx) hδ).2 hx
  exact (memLp_top_of_bound hmi (δ⁻¹) hb).2.ne

/-- Convert the inverse-norm product formulation into the essential-infimum formulation under
the actual positive shift assumptions. The original norm factor and constant may be extended values. -/
theorem le_mul_essInf_of_inverse_norm_product
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [NeZero μ] {s : X → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hs : ∀ᵐ x ∂μ, δ ≤ s x)
    (hm : AEStronglyMeasurable (fun x => Real.log (s x)) μ) {A C : ℝ≥0∞}
    (hprod : A * eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ ≤ C) :
    A ≤ C * essInf (fun x => ENNReal.ofReal (s x)) μ := by
  have hpos : ∀ᵐ x ∂μ, 0 < s x := hs.mono fun _ hx => hδ.trans_le hx
  have h0 := eLpNorm_inverse_ne_zero μ hpos
  have ht := eLpNorm_inverse_ne_top_of_lower_bound μ hδ hs hm
  have H := (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)).2 hprod
  rw [div_eq_mul_inv,eLpNorm_inverse_eq_inv_essInf μ hpos,inv_inv] at H
  exact H

/-- Remove every positive shift without changing the constant. Essential infimum, not pointwise infimum. -/
theorem unshifted_bound_of_shifted_inverse_norm_products
    {X : Type*} [MeasurableSpace X] (μ1 μ2 : Measure X) [NeZero μ1]
    (w : X → ℝ) (h1 : ∀ᵐ x ∂μ1, 0 ≤ w x) (h2 : ∀ᵐ x ∂μ2, 0 ≤ w x)
    {k : ℝ} (hk : 0 ≤ k) (A C : ℝ≥0∞) (hC : C ≠ ∞) (p : ℝ≥0∞)
    (hm : ∀ δ : ℝ, k < δ → AEStronglyMeasurable (fun x => Real.log (δ + max (w x) 0)) μ1)
    (hprod : ∀ δ : ℝ, k < δ →
      (A * eLpNorm (fun x => δ + max (w x) 0) p μ2) *
        eLpNorm (fun x => (δ + max (w x) 0) ^ (-1 : ℝ)) ∞ μ1 ≤ C) :
    A * eLpNorm w p μ2 ≤ C *
      (essInf (fun x => ENNReal.ofReal (w x)) μ1 + ENNReal.ofReal k) := by
  -- for every admissible shift: the inverse-norm conversion, norm monotonicity on μ2, essInf translation on μ1
  have hstep : ∀ δ : ℝ, k < δ →
      A * eLpNorm w p μ2 ≤ C * (ENNReal.ofReal δ + essInf (fun x => ENNReal.ofReal (w x)) μ1) := by
    intro δ hkδ
    have hδ : 0 < δ := hk.trans_lt hkδ
    have hlow : ∀ᵐ x ∂μ1, δ ≤ δ + max (w x) 0 :=
      ae_of_all _ fun x => le_add_of_nonneg_right (le_max_right _ _)
    have H := le_mul_essInf_of_inverse_norm_product μ1 hδ hlow (hm δ hkδ) (hprod δ hkδ)
    have hmono : eLpNorm w p μ2 ≤ eLpNorm (fun x => δ + max (w x) 0) p μ2 := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [h2] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx, max_eq_left hx,
        abs_of_pos (show 0 < δ + w x by linarith)]
      linarith
    have hess : essInf (fun x => ENNReal.ofReal (δ + max (w x) 0)) μ1 =
        ENNReal.ofReal δ + essInf (fun x => ENNReal.ofReal (w x)) μ1 := by
      have hae : (fun x => ENNReal.ofReal (δ + max (w x) 0)) =ᵐ[μ1]
          fun x => ENNReal.ofReal δ + ENNReal.ofReal (w x) := by
        filter_upwards [h1] with x hx
        rw [max_eq_left hx, ENNReal.ofReal_add hδ.le hx]
      rw [essInf_congr_ae hae]
      exact liminf_const_add (ae μ1) (fun x => ENNReal.ofReal (w x)) (ENNReal.ofReal δ)
        (by isBoundedDefault) (by isBoundedDefault)
    calc
      A * eLpNorm w p μ2 ≤ A * eLpNorm (fun x => δ + max (w x) 0) p μ2 := by gcongr
      _ ≤ C * essInf (fun x => ENNReal.ofReal (δ + max (w x) 0)) μ1 := H
      _ = _ := by rw [hess]
  -- δ ↓ k with the SAME finite C: `C * ·` is continuous at every limit because `C ≠ ∞`
  have hlim : Filter.Tendsto
      (fun δ : ℝ => C * (ENNReal.ofReal δ + essInf (fun x => ENNReal.ofReal (w x)) μ1))
      (nhdsWithin k (Set.Ioi k)) (nhds (C * (ENNReal.ofReal k + essInf (fun x => ENNReal.ofReal (w x)) μ1))) :=
    ENNReal.Tendsto.const_mul
      (((ENNReal.continuous_ofReal.tendsto k).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds) (Or.inr hC)
  rw [add_comm (essInf _ μ1)]
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => hstep δ hδ)

end EssentialInfimum

section MomentProduct


/-- Exact radius cancellation `R^{−N/p0} R^{−N/p0} ((c (a R)^N)²)^{1/p0} = (c a^N)^{2/p0}`, for every `R > 0`. -/
private theorem rpow_neg_mul_rpow_neg_mul_sq_rpow_eq {N p0 c a R : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hR : 0 < R) :
    R ^ (-N / p0) * R ^ (-N / p0) * ((c * (a * R) ^ N) ^ 2) ^ (1 / p0) = (c * a ^ N) ^ (2 / p0) := by
  have h6 : 0 ≤ a ^ N := Real.rpow_nonneg ha N
  have hRN : 0 ≤ R ^ N := Real.rpow_nonneg hR.le N
  have hc6 : 0 ≤ c * a ^ N := mul_nonneg hc h6
  rw [Real.mul_rpow ha hR.le]
  have e1 : (c * (a ^ N * R ^ N)) ^ 2 = (c * a ^ N) ^ 2 * (R ^ N) ^ 2 := by ring
  rw [e1, Real.mul_rpow (pow_nonneg hc6 2) (pow_nonneg hRN 2)]
  rw [← Real.rpow_natCast (c * a ^ N) 2, ← Real.rpow_natCast (R ^ N) 2, ← Real.rpow_mul hc6,
    ← Real.rpow_mul hRN, ← Real.rpow_mul hR.le]
  have e2 : R ^ (-N / p0) * R ^ (-N / p0) * ((c * a ^ N) ^ ((2 : ℕ) * (1 / p0) : ℝ) *
      R ^ (N * (((2 : ℕ) : ℝ) * (1 / p0)))) =
      (c * a ^ N) ^ ((2 : ℕ) * (1 / p0) : ℝ) * (R ^ (-N / p0) * R ^ (-N / p0) * R ^ (N * (((2 : ℕ) : ℝ) * (1 / p0)))) := by
    ring
  rw [e2, ← Real.rpow_add hR, ← Real.rpow_add hR]
  have e3 : -N / p0 + -N / p0 + N * (((2 : ℕ) : ℝ) * (1 / p0)) = 0 := by push_cast; ring
  have e4 : ((2 : ℕ) * (1 / p0) : ℝ) = 2 / p0 := by push_cast; ring
  rw [e3, Real.rpow_zero, mul_one, e4]

/-- The measure-level moment product before the radius cancellation: the moment product of `s^{±p0}` on `μ3`, the inverse
endpoint on `μ1` and `μ2 ≤ μ3` give `(R^{−N/p0} ‖s‖_{p0,μ2}) ‖s⁻¹‖_{∞,μ1} ≤ Cinv R^{−N/p0} R^{−N/p0} (A²)^{1/p0}`. -/
private theorem mul_eLpNorm_inv_top_le_of_moment_product_aux {X : Type*} [MeasurableSpace X]
    (μ1 μ2 μ3 : Measure X) (hμ : μ2 ≤ μ3)
    (s : X → ℝ) (hs : ∀ x, 0 < s x) {N p0 R Cinv A : ℝ} (hp0 : 0 < p0) (hR : 0 < R) (hCinv : 0 ≤ Cinv)
    (hpos : Integrable (fun x => s x ^ p0) μ3) (hneg : Integrable (fun x => s x ^ (-p0)) μ3)
    (hprod : (∫ x, s x ^ p0 ∂μ3) * (∫ x, s x ^ (-p0) ∂μ3) ≤ A ^ 2)
    (hinv : eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ1 ≤ ENNReal.ofReal Cinv * ((ENNReal.ofReal R) ^ (-N / p0) *
      eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0) μ3)) :
    ((ENNReal.ofReal R) ^ (-N / p0) * eLpNorm s (ENNReal.ofReal p0) μ2) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ1 ≤
      ENNReal.ofReal (Cinv * (R ^ (-N / p0) * R ^ (-N / p0) * (A ^ 2) ^ (1 / p0))) := by
  have hinvpow : (fun x => (s x ^ (-1 : ℝ)) ^ p0) = fun x => s x ^ (-p0) := by
    funext x
    rw [← Real.rpow_mul (hs x).le]
    congr 1
    ring
  have ha : eLpNorm s (ENNReal.ofReal p0) μ2 ≤ eLpNorm s (ENNReal.ofReal p0) μ3 := eLpNorm_mono_measure _ hμ
  have hI1 := ofReal_integral_rpow_eq_eLpNorm_rpow μ3 s (fun x => (hs x).le) hp0 hpos
  have hI2 := ofReal_integral_rpow_eq_eLpNorm_rpow μ3 (fun x => s x ^ (-1 : ℝ))
    (fun x => (Real.rpow_pos_of_pos (hs x) _).le) hp0 (by rw [hinvpow]; exact hneg)
  rw [hinvpow] at hI2
  have hX : (eLpNorm s (ENNReal.ofReal p0) μ3 * eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0) μ3) ^ p0 ≤
      ENNReal.ofReal (A ^ 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← hI1, ← hI2,
      ← ENNReal.ofReal_mul (integral_nonneg fun x => Real.rpow_nonneg (hs x).le _)]
    exact ENNReal.ofReal_le_ofReal hprod
  have hY : eLpNorm s (ENNReal.ofReal p0) μ3 * eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0) μ3 ≤
      (ENNReal.ofReal (A ^ 2)) ^ (1 / p0) := by
    have H := ENNReal.rpow_le_rpow hX (by positivity : (0 : ℝ) ≤ 1 / p0)
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at H
  calc
    _ ≤ ((ENNReal.ofReal R) ^ (-N / p0) * eLpNorm s (ENNReal.ofReal p0) μ3) *
          (ENNReal.ofReal Cinv * ((ENNReal.ofReal R) ^ (-N / p0) *
            eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0) μ3)) :=
      mul_le_mul' (mul_le_mul_of_nonneg_left ha zero_le) hinv
    _ = ENNReal.ofReal Cinv * (ENNReal.ofReal R) ^ (-N / p0) * (ENNReal.ofReal R) ^ (-N / p0) *
          (eLpNorm s (ENNReal.ofReal p0) μ3 * eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0) μ3) := by ring
    _ ≤ ENNReal.ofReal Cinv * (ENNReal.ofReal R) ^ (-N / p0) * (ENNReal.ofReal R) ^ (-N / p0) *
          (ENNReal.ofReal (A ^ 2)) ^ (1 / p0) := mul_le_mul_of_nonneg_left hY zero_le
    _ = _ := by
      rw [ENNReal.ofReal_mul hCinv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_rpow_of_pos hR, ← ENNReal.ofReal_rpow_of_nonneg (sq_nonneg A) (by positivity)]
      ring

/-- **Moment product → small-exponent product.** If `s > 0`, `s^{±p0}` are integrable on `μ3` with
`∫ s^{p0} ∫ s^{−p0} ≤ (c (a R)^N)²`, `μ2 ≤ μ3`, and `‖s⁻¹‖_{∞,μ1} ≤ Cinv R^{−N/p0} ‖s⁻¹‖_{p0,μ3}`, then
`(R^{−N/p0} ‖s‖_{p0,μ2}) ‖s⁻¹‖_{∞,μ1} ≤ Cinv (c a^N)^{2/p0}`, for every `R > 0`: the radius cancels exactly. The power
integrabilities are actual premises (no Bochner junk value) and every extended norm is handled before any real conversion.
This is the moment-to-product step of the weak Harnack inequality (Gilbarg–Trudinger 2001, proof of Theorem 8.18). -/
theorem mul_eLpNorm_inv_top_le_of_moment_product {X : Type*} [MeasurableSpace X]
    (μ1 μ2 μ3 : Measure X) (hμ : μ2 ≤ μ3)
    (s : X → ℝ) (hs : ∀ x, 0 < s x) {N p0 R Cinv c a : ℝ} (hp0 : 0 < p0) (hR : 0 < R) (hCinv : 0 ≤ Cinv)
    (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hpos : Integrable (fun x => s x ^ p0) μ3) (hneg : Integrable (fun x => s x ^ (-p0)) μ3)
    (hprod : (∫ x, s x ^ p0 ∂μ3) * (∫ x, s x ^ (-p0) ∂μ3) ≤ (c * (a * R) ^ N) ^ 2)
    (hinv : eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ1 ≤ ENNReal.ofReal Cinv * ((ENNReal.ofReal R) ^ (-N / p0) *
      eLpNorm (fun x => s x ^ (-1 : ℝ)) (ENNReal.ofReal p0) μ3)) :
    ((ENNReal.ofReal R) ^ (-N / p0) * eLpNorm s (ENNReal.ofReal p0) μ2) *
        eLpNorm (fun x => s x ^ (-1 : ℝ)) ∞ μ1 ≤
      ENNReal.ofReal (Cinv * (c * a ^ N) ^ (2 / p0)) := by
  have H := mul_eLpNorm_inv_top_le_of_moment_product_aux μ1 μ2 μ3 hμ s hs hp0 hR hCinv hpos hneg hprod hinv
  rwa [rpow_neg_mul_rpow_neg_mul_sq_rpow_eq hc ha hR] at H

end MomentProduct

end FunctionalInequalities.Analysis
