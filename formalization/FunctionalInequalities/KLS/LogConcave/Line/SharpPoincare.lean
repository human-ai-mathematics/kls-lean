module

public import FunctionalInequalities.KLS.LogConcave.Line.SharpHardy
public import FunctionalInequalities.KLS.LogConcave.Line.Poincare

/-!
# The sharp one-dimensional log-concave Poincaré bound `C_P^lit(ν) ≤ 4 Var_ν`

Source: Blueprint `thm:one-dimensional-logconcave-poincare` (constant `4`, following the
collaborator's constant-4 source audit, a locally kept record). Read
`LogConcave.smoothTest_holds_four_variance`, `LogConcave.localSlope_constant_le_four_variance` and
`LogConcave.localSlope_constant_le_four_evariance`.

For a log-concave probability law `ν` on the real line with nonempty interior support `Ω`, an
admissible test `f` is clipped to constants outside an interval `[a, b] ⊆ Ω` straddling a median.
The sharp Hardy module gives `Var(f_{ab}) ≤ 4 · Var_ν · ∫ f'² dν` for the clipped test; the tails
`∫_{x ≤ a} (f - f a)² dν` and `∫_{x ≥ b} (f - f b)² dν` are controlled by the half-line Hardy
bounds anchored at `a` and `b` (with the median constant) and vanish as `F a → 0`, `F b → 1`,
since `∫ f'² dν` is absolutely continuous with respect to `ν`. A `(1 + δ)`-split of the variance
then yields `Var f ≤ 4 · Var_ν · ∫ f'² dν`. The zero-dimensional (Dirac) case is handled as in the
constant-`12` module; the historical constant `12` becomes a corollary.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities

namespace Probability

/-- Absolute continuity of the integral of a nonnegative integrable function: small measure gives
small integral, with the threshold expressed as a real number below one half. -/
theorem exists_pos_forall_setIntegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x) {η : ℝ} (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / 2 ∧
      ∀ s : Set α, μ s ≤ ENNReal.ofReal t → ∫ x in s, g x ∂μ ≤ η := by
  have hlin : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg0)]
    exact ENNReal.ofReal_ne_top
  obtain ⟨δ, hδ, hδs⟩ := exists_pos_setLIntegral_lt_of_measure_lt hlin
    (ε := ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη).ne'
  obtain ⟨r, _, hr, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
  refine ⟨min r (1 / 4), by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun s hs ↦ ?_⟩
  have hlt : μ s < δ :=
    lt_of_le_of_lt hs (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hrδ)
  have := hδs s hlt
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable.restrict]
  exact ENNReal.toReal_le_of_le_ofReal hη.le this.le

/-- The elementary split `(u + v)² ≤ (1 + δ) u² + (1 + 1/δ) v²` for `δ > 0`. -/
theorem add_sq_le_split {δ : ℝ} (hδ : 0 < δ) (u v : ℝ) :
    (u + v) ^ 2 ≤ (1 + δ) * u ^ 2 + (1 + 1 / δ) * v ^ 2 := by
  have h : (1 + δ) * u ^ 2 + (1 + 1 / δ) * v ^ 2 - (u + v) ^ 2 = (δ * u - v) ^ 2 / δ := by
    field_simp
    ring
  have : 0 ≤ (δ * u - v) ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
  linarith

end Probability

namespace KLS

namespace LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ) (hμ : LogConcave μ)
  (hi : (interior (μ : Measure ℝ).support).Nonempty) {m : ℝ} (hm : cdf μ m = 1 / 2)
include d hμ hi hm

/-- The left tail of an admissible test can be made small: for every `η > 0` there is an interior
point `a ≤ m` with `∫_{x ≤ a} (f x - f a)² dμ ≤ η`. -/
theorem exists_setIntegral_Iic_sq_sub_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) {η : ℝ} (hη : 0 < η) :
    ∃ a ∈ interior (μ : Measure ℝ).support, a ≤ m ∧
      ∫ x in Iic a, (f x - f a) ^ 2 ∂(μ : Measure ℝ) ≤ η := by
  have hmΩ := median_mem hμ hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  set K := (1 / d.ρ m) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hf'2 : Integrable (fun s ↦ deriv f s ^ 2) (μ : Measure ℝ) :=
    hf.energy_integrable.congr (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  obtain ⟨t, ht0, ht1, hts⟩ :=
    Probability.exists_pos_forall_setIntegral_le hf'2 (fun x ↦ sq_nonneg _) (div_pos hη hKpos)
  obtain ⟨a, ha⟩ := Probability.Line.exists_cdf_eq μ d.withDensity_eq d.measurable d.nonneg ht0
    (by linarith)
  have haΩ : a ∈ interior (μ : Measure ℝ).support :=
    hμ.mem_interior_support_of_cdf hi (by rw [ha]; exact ht0) (by rw [ha]; linarith)
  have ham : a ≤ m := by
    rcases le_or_gt a m with h | h
    · exact h
    · have := Probability.Line.cdf_mono μ h.le
      rw [hm, ha] at this
      linarith
  refine ⟨a, haΩ, ham, ?_⟩
  have hmeas : (μ : Measure ℝ) (Iic a) ≤ ENNReal.ofReal t := by
    rw [← ha, cdf, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  calc ∫ x in Iic a, (f x - f a) ^ 2 ∂(μ : Measure ℝ)
      ≤ K * ∫ x in Iic a, deriv f x ^ 2 ∂(μ : Measure ℝ) :=
        d.setIntegral_Iic_sq_sub_le_of_le hμ hi hm hf haΩ ham
    _ ≤ K * (η / K) := mul_le_mul_of_nonneg_left (hts _ hmeas) hKpos.le
    _ = η := by field_simp

/-- The right tail of an admissible test can be made small: for every `η > 0` there is an
interior point `b ≥ m` with `∫_{x > b} (f x - f b)² dμ ≤ η`. -/
theorem exists_setIntegral_Ioi_sq_sub_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) {η : ℝ} (hη : 0 < η) :
    ∃ b ∈ interior (μ : Measure ℝ).support, m ≤ b ∧
      ∫ x in Ioi b, (f x - f b) ^ 2 ∂(μ : Measure ℝ) ≤ η := by
  have hmΩ := median_mem hμ hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  set K := (1 / d.ρ m) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hf'2 : Integrable (fun s ↦ deriv f s ^ 2) (μ : Measure ℝ) :=
    hf.energy_integrable.congr (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  obtain ⟨t, ht0, ht1, hts⟩ :=
    Probability.exists_pos_forall_setIntegral_le hf'2 (fun x ↦ sq_nonneg _) (div_pos hη hKpos)
  obtain ⟨b, hb⟩ := Probability.Line.exists_cdf_eq μ d.withDensity_eq d.measurable d.nonneg
    (t := 1 - t) (by linarith) (by linarith)
  have hbΩ : b ∈ interior (μ : Measure ℝ).support :=
    hμ.mem_interior_support_of_cdf hi (by rw [hb]; linarith) (by rw [hb]; linarith)
  have hmb : m ≤ b := by
    rcases le_or_gt m b with h | h
    · exact h
    · have := Probability.Line.cdf_mono μ h.le
      rw [hm, hb] at this
      linarith
  refine ⟨b, hbΩ, hmb, ?_⟩
  have hmeas : (μ : Measure ℝ) (Ioi b) ≤ ENNReal.ofReal t := by
    have h1 : (μ : Measure ℝ).real (Ioi b) = t := by
      rw [Probability.Line.measureReal_Ioi μ b, hb]
      ring
    rw [← h1, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  calc ∫ x in Ioi b, (f x - f b) ^ 2 ∂(μ : Measure ℝ)
      ≤ K * ∫ x in Ioi b, deriv f x ^ 2 ∂(μ : Measure ℝ) :=
        d.setIntegral_Ioi_sq_sub_le_of_le hμ hi hm hf hbΩ hmb
    _ ≤ K * (η / K) := mul_le_mul_of_nonneg_left (hts _ hmeas) hKpos.le
    _ = η := by field_simp

omit d hμ hi hm in
/-- The clipping error is controlled by the two tails:
`∫ (f - f_{ab})² dμ ≤ ∫_{x ≤ a} (f x - f a)² dμ + ∫_{x > b} (f x - f b)² dμ`. -/
theorem integral_sub_clip_sq_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) {a b : ℝ} (hab : a ≤ b) :
    ∫ x, (f x - clip a b f x) ^ 2 ∂(μ : Measure ℝ) ≤
      (∫ x in Iic a, (f x - f a) ^ 2 ∂(μ : Measure ℝ)) +
        ∫ x in Ioi b, (f x - f b) ^ 2 ∂(μ : Measure ℝ) := by
  have hfc : Continuous f := hf.smooth'.continuous
  obtain ⟨C, hC⟩ := clip.exists_bound hab hfc
  have hg2 : MemLp (clip a b f) 2 (μ : Measure ℝ) :=
    MemLp.of_bound (clip.continuous hfc).aestronglyMeasurable C (ae_of_all _ hC)
  have hint0 : Integrable (fun x ↦ (f x - clip a b f x) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub hg2).integrable_sq
  have hintA : Integrable (fun x ↦ (f x - f a) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub (memLp_const (f a))).integrable_sq
  have hintB : Integrable (fun x ↦ (f x - f b) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub (memLp_const (f b))).integrable_sq
  have hpt : ∀ x, (f x - clip a b f x) ^ 2 ≤
      (Iic a).indicator (fun x ↦ (f x - f a) ^ 2) x +
        (Ioi b).indicator (fun x ↦ (f x - f b) ^ 2) x := by
    intro x
    by_cases hxa : x ≤ a
    · rw [clip.of_le hab hxa, indicator_of_mem (mem_Iic.mpr hxa)]
      exact le_add_of_nonneg_right (indicator_nonneg (fun y _ ↦ sq_nonneg _) x)
    · by_cases hxb : b < x
      · rw [clip.of_ge hxb.le hab, indicator_of_mem (mem_Ioi.mpr hxb)]
        exact le_add_of_nonneg_left (indicator_nonneg (fun y _ ↦ sq_nonneg _) x)
      · rw [clip.of_mem ⟨(not_le.mp hxa).le, not_lt.mp hxb⟩, sub_self]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact add_nonneg (indicator_nonneg (fun y _ ↦ sq_nonneg _) x)
          (indicator_nonneg (fun y _ ↦ sq_nonneg _) x)
  calc ∫ x, (f x - clip a b f x) ^ 2 ∂(μ : Measure ℝ)
      ≤ ∫ x, ((Iic a).indicator (fun x ↦ (f x - f a) ^ 2) x +
          (Ioi b).indicator (fun x ↦ (f x - f b) ^ 2) x) ∂(μ : Measure ℝ) :=
        integral_mono hint0 ((hintA.indicator measurableSet_Iic).add
          (hintB.indicator measurableSet_Ioi)) hpt
    _ = _ := by
        rw [integral_add (hintA.indicator measurableSet_Iic) (hintB.indicator measurableSet_Ioi),
          integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi]

/-- The sharp smooth-test Poincaré inequality `Var f ≤ 4 · Var_μ · ∫ f'² dμ` for an admissible
test, obtained from the clipped bound by letting the clipping interval exhaust the support. -/
theorem variance_le_four_variance_mul {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) :
    variance f (μ : Measure ℝ) ≤
      4 * variance id (μ : Measure ℝ) * ∫ x, deriv f x ^ 2 ∂(μ : Measure ℝ) := by
  have hfc : Continuous f := hf.smooth'.continuous
  have hE : Integrable (fun x ↦ deriv f x ^ 2) (μ : Measure ℝ) :=
    hf.energy_integrable.congr (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  set K := 4 * variance id (μ : Measure ℝ) * ∫ x, deriv f x ^ 2 ∂(μ : Measure ℝ) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg (by norm_num) (variance_nonneg _ _))
      (integral_nonneg fun x ↦ sq_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ : ℝ := ε / (2 * (K + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set η : ℝ := ε / (4 * (1 + 1 / δ)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨a, haΩ, ham, hA⟩ := d.exists_setIntegral_Iic_sq_sub_le hμ hi hm hf hηpos
  obtain ⟨b, hbΩ, hmb, hB⟩ := d.exists_setIntegral_Ioi_sq_sub_le hμ hi hm hf hηpos
  have hab : a ≤ b := ham.trans hmb
  have hFa : cdf μ a ≤ 1 / 2 := cdf_le_half_of_le hm ham
  have hFb : 1 / 2 ≤ cdf μ b := half_le_cdf_of_le hm hmb
  set g := clip a b f with hg
  have hgc : Continuous g := clip.continuous hfc
  obtain ⟨C, hC⟩ := clip.exists_bound hab hfc
  have hg2 : MemLp g 2 (μ : Measure ℝ) :=
    MemLp.of_bound hgc.aestronglyMeasurable C (ae_of_all _ hC)
  set c := ∫ x, g x ∂(μ : Measure ℝ) with hc
  -- the clipped variance is bounded by `K`
  have hvarg : variance g (μ : Measure ℝ) ≤ K :=
    d.variance_clip_le hμ hi hab haΩ hbΩ hf.smooth' hFa hFb hE
  have hvarg_eq : variance g (μ : Measure ℝ) = ∫ x, (g x - c) ^ 2 ∂(μ : Measure ℝ) := by
    rw [variance_eq_integral hgc.measurable.aemeasurable]
  -- the clipping error is at most `2 η`
  have herr : ∫ x, (f x - g x) ^ 2 ∂(μ : Measure ℝ) ≤ 2 * η := by
    have := integral_sub_clip_sq_le hf hab
    linarith
  -- the `(1 + δ)`-split
  have hint1 : Integrable (fun x ↦ (g x - c) ^ 2) (μ : Measure ℝ) :=
    (hg2.sub (memLp_const c)).integrable_sq
  have hint2 : Integrable (fun x ↦ (f x - g x) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub hg2).integrable_sq
  have hsplit : ∫ x, (f x - c) ^ 2 ∂(μ : Measure ℝ) ≤
      (1 + δ) * ∫ x, (g x - c) ^ 2 ∂(μ : Measure ℝ) +
        (1 + 1 / δ) * ∫ x, (f x - g x) ^ 2 ∂(μ : Measure ℝ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hint1.const_mul _)
      (hint2.const_mul _)]
    refine integral_mono ((hf.memLp_two.sub (memLp_const c)).integrable_sq)
      ((hint1.const_mul _).add (hint2.const_mul _)) fun x ↦ ?_
    have := Probability.add_sq_le_split hδpos (g x - c) (f x - g x)
    have heq : f x - c = (g x - c) + (f x - g x) := by ring
    rw [heq]
    exact this
  -- assemble
  have hδK : δ * K ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hK0, hε.le]
  have hηδ : (1 + 1 / δ) * (2 * η) = ε / 2 := by
    rw [hη]
    field_simp
    ring
  have hvarg0 := variance_nonneg g (μ : Measure ℝ)
  have hδ1 : 0 ≤ 1 + 1 / δ := by positivity
  calc variance f (μ : Measure ℝ)
      ≤ ∫ x, (f x - c) ^ 2 ∂(μ : Measure ℝ) := hf.variance_le_integral_sq_sub c
    _ ≤ (1 + δ) * ∫ x, (g x - c) ^ 2 ∂(μ : Measure ℝ) +
        (1 + 1 / δ) * ∫ x, (f x - g x) ^ 2 ∂(μ : Measure ℝ) := hsplit
    _ ≤ (1 + δ) * K + (1 + 1 / δ) * (2 * η) := by
        rw [← hvarg_eq]
        exact add_le_add (mul_le_mul_of_nonneg_left hvarg (by positivity))
          (mul_le_mul_of_nonneg_left herr hδ1)
    _ ≤ K + ε := by nlinarith

end LineDensity

namespace LogConcave

variable {ν : ProbabilityMeasure ℝ}

/-- Smooth-test Poincaré inequality with the sharp constant `4 · Var` for a log-concave law on
the line whose support has nonempty interior. -/
theorem smoothTest_holds_four_variance (hν : LogConcave ν)
    (hi : (interior (ν : Measure ℝ).support).Nonempty) :
    Poincare.SmoothTest.Holds (ν : Measure ℝ) (4 * variance id (ν : Measure ℝ)) := by
  obtain ⟨d⟩ := hν.exists_lineDensity hi
  obtain ⟨m, hm⟩ := d.exists_median
  refine ⟨inferInstance, mul_nonneg (by norm_num) (variance_nonneg _ _), fun f hf ↦ ?_⟩
  have henergy : Poincare.SmoothTest.energy (ν : Measure ℝ) f =
      ∫ s, deriv f s ^ 2 ∂(ν : Measure ℝ) := by
    unfold Poincare.SmoothTest.energy
    exact integral_congr_ae (ae_of_all _ fun s ↦ LineDensity.norm_gradient_sq_eq_deriv_sq f s)
  rw [henergy]
  exact d.variance_le_four_variance_mul hν hi hm hf

/-- Blueprint `thm:one-dimensional-logconcave-poincare`: every log-concave law on the line has
literature Poincaré constant at most `4 · Var_ν(id)`, the zero-variance (Dirac) case included. -/
theorem localSlope_constant_le_four_variance (hν : LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤
      ENNReal.ofReal (4 * variance id (ν : Measure ℝ)) := by
  rcases hν.direction_eq_bot_or_interior_support_nonempty with hbot | hi
  · rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_direction_eq_bot ν hbot]
    exact bot_le
  · have h4 : 0 ≤ 4 * variance id (ν : Measure ℝ) :=
      mul_nonneg (by norm_num) (variance_nonneg _ _)
    rw [← hν.smoothTest_constant_eq_localSlope, ENNReal.ofReal_eq_coe_nnreal h4]
    exact Poincare.SmoothTest.constant_le (hν.smoothTest_holds_four_variance hi)

/-- The same bound in extended form, through the extended variance. -/
theorem localSlope_constant_le_four_evariance (hν : LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ 4 * evariance id (ν : Measure ℝ) := by
  refine hν.localSlope_constant_le_four_variance.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num), ofReal_variance hν.memLp_id_two]
  norm_num

/-- The historical constant `12` (Bobkov) as a corollary of the sharp bound. -/
theorem localSlope_constant_le_twelve_variance_of_four (hν : LogConcave ν) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (12 * variance id (ν : Measure ℝ)) :=
  hν.localSlope_constant_le_four_variance.trans
    (ENNReal.ofReal_le_ofReal (by nlinarith [variance_nonneg id (ν : Measure ℝ)]))

end LogConcave

end KLS

end FunctionalInequalities
