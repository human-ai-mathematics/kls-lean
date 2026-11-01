module

public import FunctionalInequalities.KLS.LogConcave.Line.Profile
public import FunctionalInequalities.KLS.LogConcave.Isotropic
public import FunctionalInequalities.KLS.LogConcave.Borel
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Grünbaum's lemma on the line

Guédon–Milman, *Interpolating thin-shell and sharp large-deviation estimates for isotropic
log-concave measures* (arXiv:1011.0943v3), Lemma 2.2 (Grünbaum): if a real random variable has a
log-concave density and barycenter at the origin, then `1/e ≤ P(X ≥ 0) ≤ 1 - 1/e`.

A law with a log-concave density is a log-concave law whose support has nonempty interior. The
tail `G(t) = μ(t, ∞)` is log-concave, so it lies below its tangent exponential at `0`:
`G(t) ≤ G(0) e^{-a t}` with `a > 0`. The layer-cake formula turns the barycenter condition into
`∫₀^∞ G = ∫_{-∞}^0 (1 - G)`, and comparing both sides with the exponential gives
`G(0) ≥ -log G(0) - 1 + G(0)`, i.e. `G(0) ≥ 1/e`. The reflected law gives `μ(-∞, 0) ≥ 1/e`.
-/

@[expose] public section

section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FunctionalInequalities.KLS.LogConcave

variable {μ : ProbabilityMeasure ℝ}

private lemma log_slope_anti {g : ℝ → ℝ}
    (hlc : ∀ a b θ : ℝ, 0 < θ → θ < 1 →
      g a ^ θ * g b ^ (1 - θ) ≤ g (θ * a + (1 - θ) * b))
    {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (hx : 0 < g x) (hy : 0 < g y) (hz : 0 < g z) :
    (Real.log (g y) - Real.log (g x)) / (y - x) ≥
      (Real.log (g z) - Real.log (g y)) / (z - y) := by
  let θ : ℝ := (z - y) / (z - x)
  have hxz : 0 < z - x := by linarith
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one hxz]
    linarith
  have hpoint : θ * x + (1 - θ) * z = y := by
    dsimp [θ]
    field_simp
    ring
  have hineq : g x ^ θ * g z ^ (1 - θ) ≤ g y := by
    simpa [hpoint] using hlc x z θ hθ hθ1
  have hlog :
      θ * Real.log (g x) + (1 - θ) * Real.log (g z) ≤
        Real.log (g y) := by
    have h₁ : 0 < g x ^ θ * g z ^ (1 - θ) := by positivity
    have h₂ : 0 < g y := hy
    have h₃ := Real.strictMonoOn_log.monotoneOn h₁ h₂ hineq
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hx, Real.log_rpow hz] at h₃
    simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h₃
  dsimp [θ] at hlog
  have hxy' : 0 < y - x := sub_pos.mpr hxy
  have hyz' : 0 < z - y := sub_pos.mpr hyz
  have hxz' : 0 < z - x := sub_pos.mpr (lt_trans hxy hyz)
  apply (div_le_div_iff₀ hyz' hxy').2
  field_simp [hxy'.ne', hyz'.ne', hxz'.ne'] at hlog
  nlinarith

private lemma slope_trans {A B C r s : ℝ}
    (hr : 0 < r) (hrs : r < s)
    (h : (C - B) / (s - r) ≤ (B - A) / r) :
    (C - A) / s ≤ (B - A) / r := by
  have hs : 0 < s := by linarith
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have h₁ : ((C - B) / (s - r)) * r ≤ B - A := by
    exact (le_div_iff₀ hr).mp h
  have h₂ :
      (((C - B) / (s - r)) * r) * (s - r) ≤
        (B - A) * (s - r) := by
    exact mul_le_mul_of_nonneg_right h₁ (le_of_lt hsr)
  have h₃ : r * (C - B) ≤ (B - A) * (s - r) := by
    field_simp [hsr.ne'] at h₂
    simpa [mul_comm, mul_left_comm, mul_assoc] using h₂
  apply (div_le_div_iff₀ hs hr).2
  nlinarith

/-- Tangent exponential of a log-concave tail: a nonincreasing `g ≥ 0` with
`g(θa + (1-θ)b) ≥ g(a)^θ g(b)^{1-θ}`, `g → 1` at `-∞`, `0 < g 0 < 1` and `g > 0` somewhere to
the right of `0` satisfies `g t ≤ g 0 · e^{-a t}` for some `a > 0` and every `t`. -/
theorem exists_le_mul_exp {g : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hanti : Antitone g)
    (hlc : ∀ a b θ : ℝ, 0 < θ → θ < 1 → g a ^ θ * g b ^ (1 - θ) ≤ g (θ * a + (1 - θ) * b))
    (hlim : Tendsto g atBot (𝓝 1)) (hpos : 0 < g 0) (hlt : g 0 < 1) (hs : ∃ s > 0, 0 < g s) :
    ∃ a > 0, ∀ t, g t ≤ g 0 * Real.exp (-(a * t)) := by
  rcases hs with ⟨s, hs, hspos⟩
  have hev : ∀ᶠ t in atBot, (1 + g 0) / 2 < g t := by
    apply (tendsto_order.1 hlim).1
    linarith
  rcases eventually_atBot.1 hev with ⟨b, hb⟩
  let u : ℝ := min b (-1)
  have hu : u < 0 := by
    dsimp [u]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hgu : 0 < g u := by
    have h := hb u (min_le_left _ _)
    linarith
  have hgu0 : g 0 < g u := by
    have h := hb u (min_le_left _ _)
    linarith
  let σ : ℝ → ℝ := fun t =>
    (Real.log (g t) - Real.log (g 0)) / t
  let A : Set ℝ := σ '' Set.Ioc 0 s
  have hA_nonempty : A.Nonempty := by
    refine ⟨σ s, ?_⟩
    exact ⟨s, ⟨hs, le_rfl⟩, rfl⟩
  have hA_bdd : BddAbove A := by
    refine ⟨(Real.log (g 0) - Real.log (g u)) / (0 - u), ?_⟩
    rintro _ ⟨t, ⟨ht, hts⟩, rfl⟩
    have hgt : 0 < g t := lt_of_lt_of_le hspos (hanti hts)
    have hsl := log_slope_anti hlc hu ht hgu hpos hgt
    dsimp [σ]
    simpa [sub_zero] using hsl
  let c : ℝ := sSup A
  have hc_mem : ∀ t, 0 < t → t ≤ s → σ t ≤ c := by
    intro t ht hts
    apply le_csSup hA_bdd
    exact ⟨t, ⟨ht, hts⟩, rfl⟩
  have hc_left : ∀ t, t < 0 → 0 < g t →
      c ≤ (Real.log (g 0) - Real.log (g t)) / (0 - t) := by
    intro t ht hgt
    apply csSup_le hA_nonempty
    rintro _ ⟨r, ⟨hr, hrs⟩, rfl⟩
    have hgr : 0 < g r := lt_of_lt_of_le hspos (hanti hrs)
    have hsl := log_slope_anti hlc ht hr hgt hpos hgr
    dsimp [σ]
    simpa [sub_zero] using hsl
  have hc_upper : ∀ t, 0 < t → 0 < g t → σ t ≤ c := by
    intro t ht hgt
    by_cases hts : t ≤ s
    · exact hc_mem t ht hts
    · have hst : s < t := lt_of_not_ge hts
      have hsl := log_slope_anti hlc hs hst hpos hspos hgt
      have htrans :
          (Real.log (g t) - Real.log (g 0)) / t ≤
            (Real.log (g s) - Real.log (g 0)) / s := by
        apply slope_trans hs hst
        simpa [sub_zero] using hsl
      exact htrans.trans (hc_mem s hs (le_refl s))
  have hc_neg : c < 0 := by
    by_contra h
    have hc0 : 0 ≤ c := le_of_not_gt h
    have hleft : ∀ t, t < 0 → g t ≤ g 0 := by
      intro t ht
      have hgt : 0 < g t := lt_of_lt_of_le hpos (hanti (le_of_lt ht))
      have hct := hc_left t ht hgt
      have hct' :
          c * (0 - t) ≤ Real.log (g 0) - Real.log (g t) := by
        exact (le_div_iff₀ (sub_pos.mpr ht)).mp hct
      have hlog : Real.log (g t) ≤ Real.log (g 0) := by
        have hnonpos : c * t ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_lt ht)
        nlinarith
      exact (Real.strictMonoOn_log.le_iff_le hgt hpos).mp hlog
    have hleftu := hleft u hu
    have hlimu := hb u (min_le_left _ _)
    linarith
  refine ⟨-c, neg_pos.mpr hc_neg, ?_⟩
  intro t
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases hzero : g t = 0
  · rw [hzero]
    exact mul_nonneg (le_of_lt hpos) (le_of_lt (Real.exp_pos _))
  have hgt : 0 < g t := lt_of_le_of_ne (hg0 t) (Ne.symm hzero)
  by_cases htpos : 0 < t
  · have hslope := hc_upper t htpos hgt
    have hmul :
        Real.log (g t) - Real.log (g 0) ≤ c * t := by
      exact (div_le_iff₀ htpos).mp hslope
    have hlog : Real.log (g t) ≤ Real.log (g 0) + c * t := by
      linarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hgt] at hexp
    calc
      g t ≤ Real.exp (Real.log (g 0) + c * t) := hexp
      _ = g 0 * Real.exp (c * t) := by
        rw [Real.exp_add, Real.exp_log hpos]
      _ = g 0 * Real.exp (-((-c) * t)) := by
        congr 1
        ring_nf
  · have htneg : t < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt htpos) (by
        intro h
        exact ht0 h)
    have hslope := hc_left t htneg hgt
    have hmul :
        c * (0 - t) ≤ Real.log (g 0) - Real.log (g t) := by
      exact (le_div_iff₀ (sub_pos.mpr htneg)).mp hslope
    have hlog : Real.log (g t) ≤ Real.log (g 0) + c * t := by
      nlinarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hgt] at hexp
    calc
      g t ≤ Real.exp (Real.log (g 0) + c * t) := hexp
      _ = g 0 * Real.exp (c * t) := by
        rw [Real.exp_add, Real.exp_log hpos]
      _ = g 0 * Real.exp (-((-c) * t)) := by
        congr 1
        ring_nf

section

variable {μ : ProbabilityMeasure ℝ}

/-- Upper half of the integral comparison: `∫₀^∞ g ≤ g 0 / a` under the tangent bound. -/
theorem integral_Ioi_le_div {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hint : IntegrableOn g (Ioi 0))
    (htan : ∀ t, g t ≤ g 0 * Real.exp (-(a * t))) :
    ∫ t in Ioi 0, g t ≤ g 0 / a := by
  have hmodel : IntegrableOn (fun t : ℝ => g 0 * Real.exp (-(a * t))) (Ioi 0) := by
    change Integrable (fun t : ℝ => g 0 * Real.exp (-(a * t)))
      (volume.restrict (Ioi 0))
    simpa [neg_mul] using
      ((integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).const_mul (g 0))
  have hle :
      ∫ t in Ioi 0, g t ≤
        ∫ t in Ioi 0, g 0 * Real.exp (-(a * t)) :=
    setIntegral_mono_on (hf := hint) (hg := hmodel) measurableSet_Ioi
      (fun t _ => htan t)
  have hexp :
      ∫ t in Ioi 0, Real.exp ((-a) * t) =
        -Real.exp ((-a) * 0) / (-a) :=
    integral_exp_mul_Ioi (a := -a) (by linarith) 0
  calc
    ∫ t in Ioi 0, g t ≤
        ∫ t in Ioi 0, g 0 * Real.exp (-(a * t)) := hle
    _ = g 0 * ∫ t in Ioi 0, Real.exp (-(a * t)) := by
      rw [integral_const_mul]
    _ = g 0 * ∫ t in Ioi 0, Real.exp ((-a) * t) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp [neg_mul]
    _ = g 0 * (-Real.exp ((-a) * 0) / (-a)) := by
      rw [hexp]
    _ = g 0 / a := by
      simp [div_eq_mul_inv]

end

theorem integral_one_sub_mul_exp {a : ℝ} (ha : 0 < a) (c u : ℝ) :
    ∫ t in u..0, (1 - c * Real.exp (-(a * t))) =
      -u - c * (Real.exp (-(a * u)) - 1) / a := by
  have hcont :
      Continuous (fun t : ℝ => c * Real.exp (-(a * t))) := by
    fun_prop
  have hci :
      IntervalIntegrable (fun t : ℝ => c * Real.exp (-(a * t))) volume u 0 := by
    exact hcont.intervalIntegrable u 0
  have hexp :
      ∫ t in u..0, Real.exp (-(a * t)) =
        (Real.exp (-(a * u)) - 1) / a := by
    have hna : -a ≠ 0 := by linarith
    have hcomp :
        ∫ t in u..0, Real.exp ((-a) * t) =
          (-a)⁻¹ • ∫ t in (-a) * u..(-a) * 0, Real.exp t := by
      exact intervalIntegral.integral_comp_mul_left
        (f := fun t : ℝ => Real.exp t) (c := -a) (a := u) (b := 0) hna
    have hexp' :
        ∫ t in (-a) * u..(-a) * 0, Real.exp t =
          Real.exp ((-a) * 0) - Real.exp ((-a) * u) := by
      rw [integral_exp]
    calc
      ∫ t in u..0, Real.exp (-(a * t)) =
          ∫ t in u..0, Real.exp ((-a) * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring_nf
      _ = (-a)⁻¹ • ∫ t in (-a) * u..(-a) * 0, Real.exp t := hcomp
      _ = (-a)⁻¹ •
          (Real.exp ((-a) * 0) - Real.exp ((-a) * u)) := by rw [hexp']
      _ = (Real.exp (-(a * u)) - 1) / a := by
        simp only [smul_eq_mul]
        rw [show (-a) * 0 = 0 by ring, Real.exp_zero]
        rw [show (-a) * u = -(a * u) by ring]
        field_simp [ne_of_gt ha]
        ring
  calc
    ∫ t in u..0, (1 - c * Real.exp (-(a * t))) =
        (∫ t in u..0, (1 : ℝ)) -
          ∫ t in u..0, c * Real.exp (-(a * t)) := by
      exact intervalIntegral.integral_sub intervalIntegrable_const hci
    _ = (∫ t in u..0, (1 : ℝ)) -
          c * ∫ t in u..0, Real.exp (-(a * t)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = -u - c * (Real.exp (-(a * u)) - 1) / a := by
      rw [intervalIntegral.integral_const, hexp]
      simp only [smul_eq_mul]
      ring_nf

theorem div_le_integral_Iio {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hg1 : ∀ t, g t ≤ 1)
    (hpos : 0 < g 0) (htan : ∀ t, g t ≤ g 0 * Real.exp (-(a * t)))
    (hint : IntegrableOn (fun t => 1 - g t) (Iio 0)) :
    (-(Real.log (g 0)) - 1 + g 0) / a ≤ ∫ t in Iio 0, (1 - g t) := by
  by_cases h : g 0 = 1
  · have hnonneg : 0 ≤ ∫ t in Iio 0, (1 - g t) := by
      apply integral_nonneg_of_ae
      filter_upwards [] with t
      exact sub_nonneg.mpr (hg1 t)
    simpa [h] using hnonneg
  · have hlt : g 0 < 1 := lt_of_le_of_ne (hg1 0) h
    have hlog : Real.log (g 0) < 0 := Real.log_neg hpos hlt
    let t₀ : ℝ := Real.log (g 0) / a
    have ht₀ : t₀ < 0 := by
      dsimp [t₀]
      exact div_neg_of_neg_of_pos hlog ha
    have hsub : Ioo t₀ 0 ⊆ Iio 0 := by
      intro t ht
      exact ht.2
    have hsub_ae : Ioo t₀ 0 ≤ᵐ[volume] Iio 0 := by
      filter_upwards [] with t ht
      exact hsub ht
    have hnonneg : 0 ≤ᵐ[volume.restrict (Iio 0)] (fun t => 1 - g t) := by
      filter_upwards [] with t
      exact sub_nonneg.mpr (hg1 t)
    have hset :
        (∫ t in Ioo t₀ 0, (1 - g t)) ≤
          ∫ t in Iio 0, (1 - g t) := by
      exact setIntegral_mono_set hint hnonneg hsub_ae
    have hcont :
        Continuous (fun t : ℝ => 1 - g 0 * Real.exp (-(a * t))) := by
      fun_prop
    have hmodelIoc :
        IntegrableOn (fun t : ℝ => 1 - g 0 * Real.exp (-(a * t))) (Ioc t₀ 0) :=
      hcont.integrableOn_Ioc
    have hmodelIoo :
        IntegrableOn (fun t : ℝ => 1 - g 0 * Real.exp (-(a * t))) (Ioo t₀ 0) :=
      hmodelIoc.mono_set (by
        intro t ht
        exact ⟨ht.1, le_of_lt ht.2⟩)
    have hpoint :
        ∀ t ∈ Ioo t₀ 0,
          1 - g 0 * Real.exp (-(a * t)) ≤ 1 - g t := by
      intro t ht
      linarith [htan t]
    have hcomp :
        (∫ t in Ioo t₀ 0, 1 - g 0 * Real.exp (-(a * t))) ≤
          ∫ t in Ioo t₀ 0, (1 - g t) := by
      exact setIntegral_mono_on (hf := hmodelIoo)
        (hg := hint.mono_set hsub) measurableSet_Ioo hpoint
    have hlower :
        ∫ t in Iio 0, (1 - g t) ≥
          ∫ t in t₀..0, (1 - g 0 * Real.exp (-(a * t))) := by
      calc
        ∫ t in Iio 0, (1 - g t) ≥ ∫ t in Ioo t₀ 0, (1 - g t) := hset
        _ ≥ ∫ t in Ioo t₀ 0, (1 - g 0 * Real.exp (-(a * t))) := hcomp
        _ = ∫ t in Ioc t₀ 0, (1 - g 0 * Real.exp (-(a * t))) := by
          rw [integral_Ioc_eq_integral_Ioo]
        _ = ∫ t in t₀..0, (1 - g 0 * Real.exp (-(a * t))) := by
          rw [intervalIntegral.integral_of_le (le_of_lt ht₀)]
    have hformula :
        ∫ t in t₀..0, (1 - g 0 * Real.exp (-(a * t))) =
          -t₀ - g 0 * (Real.exp (-(a * t₀)) - 1) / a := by
      exact integral_one_sub_mul_exp ha (g 0) t₀
    have hexp : Real.exp (-(a * t₀)) = (g 0)⁻¹ := by
      dsimp [t₀]
      have hcancel : a * (Real.log (g 0) / a) = Real.log (g 0) := by
        field_simp [ne_of_gt ha]
      rw [hcancel, Real.exp_neg, Real.exp_log hpos]
    have heq :
        -t₀ - g 0 * (Real.exp (-(a * t₀)) - 1) / a =
          (-(Real.log (g 0)) - 1 + g 0) / a := by
      rw [hexp]
      have hinv : g 0 * (g 0)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      have hmul : g 0 * ((g 0)⁻¹ - 1) = 1 - g 0 := by
        calc
          g 0 * ((g 0)⁻¹ - 1) = g 0 * (g 0)⁻¹ - g 0 * 1 := by rw [mul_sub]
          _ = 1 - g 0 := by rw [hinv, mul_one]
      rw [hmul]
      dsimp [t₀]
      field_simp [ne_of_gt ha]
      ring
    calc
      (-(Real.log (g 0)) - 1 + g 0) / a =
          -t₀ - g 0 * (Real.exp (-(a * t₀)) - 1) / a := heq.symm
      _ = ∫ t in t₀..0, (1 - g 0 * Real.exp (-(a * t))) := hformula.symm
      _ ≤ ∫ t in Iio 0, (1 - g t) := hlower

/-- The integral comparison: if `0 ≤ g ≤ 1`, `g t ≤ g 0 · e^{-a t}` with `a > 0` and
`∫₀^∞ g = ∫_{-∞}^0 (1 - g)`, then `g 0 ≥ 1/e`. -/
theorem exp_neg_one_le_of_integral_eq {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hg1 : ∀ t, g t ≤ 1) (hpos : 0 < g 0) (htan : ∀ t, g t ≤ g 0 * Real.exp (-(a * t)))
    (hint₁ : IntegrableOn g (Ioi 0)) (hint₂ : IntegrableOn (fun t => 1 - g t) (Iio 0))
    (heq : ∫ t in Ioi 0, g t = ∫ t in Iio 0, (1 - g t)) :
    Real.exp (-1) ≤ g 0 := by
  have h1 := integral_Ioi_le_div ha hint₁ htan
  have h2 := div_le_integral_Iio ha hg1 hpos htan hint₂
  rw [← heq] at h2
  have h3 :
      (-(Real.log (g 0)) - 1 + g 0) / a ≤ g 0 / a :=
    h2.trans h1
  have h4 :
      -(Real.log (g 0)) - 1 + g 0 ≤ g 0 := by
    exact (div_le_div_iff_of_pos_right ha).mp h3
  have hlog : -1 ≤ Real.log (g 0) := by
    linarith
  calc
    Real.exp (-1) ≤ Real.exp (Real.log (g 0)) :=
      Real.exp_le_exp.mpr hlog
    _ = g 0 := Real.exp_log hpos

theorem measureReal_Ioi_rpow_mul_le (hμ : LogConcave μ) (a b θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (μ : Measure ℝ).real (Ioi a) ^ θ * (μ : Measure ℝ).real (Ioi b) ^ (1 - θ) ≤
      (μ : Measure ℝ).real (Ioi (θ * a + (1 - θ) * b)) := by
  have hBorel :=
    (LogConcave.borel_iff μ).1 hμ (Ioi a) (Ioi b)
      measurableSet_Ioi measurableSet_Ioi θ hθ0 hθ1
  let C : Set ℝ :=
    {z | ∃ x ∈ Ioi a, ∃ y ∈ Ioi b, z = θ • x + (1 - θ) • y}
  have hsub :
      C ⊆ Ioi (θ * a + (1 - θ) * b) := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hxa : 0 < x - a := sub_pos.mpr hx
    have hyb : 0 < y - b := sub_pos.mpr hy
    have hθ' : 0 < 1 - θ := sub_pos.mpr hθ1
    have h₁ : 0 < θ * (x - a) := mul_pos hθ0 hxa
    have h₂ : 0 < (1 - θ) * (y - b) := mul_pos hθ' hyb
    have hlt :
        θ * a + (1 - θ) * b <
          θ * x + (1 - θ) * y := by
      nlinarith
    simpa [smul_eq_mul] using hlt
  have hE :
      (μ : Measure ℝ) (Ioi a) ^ θ *
          (μ : Measure ℝ) (Ioi b) ^ (1 - θ) ≤
        (μ : Measure ℝ) (Ioi (θ * a + (1 - θ) * b)) := by
    calc
      (μ : Measure ℝ) (Ioi a) ^ θ *
          (μ : Measure ℝ) (Ioi b) ^ (1 - θ) ≤
          innerMeasure (μ : Measure ℝ) C := by
        simpa [C] using hBorel
      _ ≤ (μ : Measure ℝ) C :=
        innerMeasure_le (μ : Measure ℝ) C
      _ ≤ (μ : Measure ℝ) (Ioi (θ * a + (1 - θ) * b)) :=
        measure_mono hsub
  have hA : (μ : Measure ℝ) (Ioi a) ≠ ∞ := measure_ne_top _ _
  have hB : (μ : Measure ℝ) (Ioi b) ≠ ∞ := measure_ne_top _ _
  have hR :
      (μ : Measure ℝ) (Ioi (θ * a + (1 - θ) * b)) ≠ ∞ :=
    measure_ne_top _ _
  have hto :=
    ENNReal.toReal_mono hR hE
  change
    ((μ : Measure ℝ) (Ioi a)).toReal ^ θ *
        ((μ : Measure ℝ) (Ioi b)).toReal ^ (1 - θ) ≤
      ((μ : Measure ℝ) (Ioi (θ * a + (1 - θ) * b))).toReal
  simpa [ENNReal.toReal_mul, ENNReal.toReal_rpow, hA, hB, hR] using hto

theorem integral_max_eq (hint : Integrable id (μ : Measure ℝ)) :
    ∫ x, max x 0 ∂(μ : Measure ℝ) = ∫ t in Ioi 0, (μ : Measure ℝ).real (Ioi t) := by
  have hpos : Integrable (fun x : ℝ => max x 0) (μ : Measure ℝ) := by
    simpa using hint.pos_part
  have hnonneg :
      0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => max x 0) :=
    ae_of_all _ (fun x => le_max_right x 0)
  have hlayer :=
    hpos.integral_eq_integral_meas_lt hnonneg
  have hset :
      ∀ t : ℝ, t ∈ Ioi 0 →
        {a : ℝ | t < max a 0} = Ioi t := by
    intro t ht
    change 0 < t at ht
    ext a
    constructor
    · intro ha
      change t < max a 0 at ha
      by_cases haa : 0 ≤ a
      · change t < a
        simpa [max_eq_left haa] using ha
      · have ha0 : a ≤ 0 := le_of_not_ge haa
        have hmax : max a 0 = 0 := max_eq_right ha0
        rw [hmax] at ha
        exfalso
        linarith
    · intro ha
      change t < a at ha
      exact lt_of_lt_of_le ha (le_max_left a 0)
  calc
    ∫ x, max x 0 ∂(μ : Measure ℝ) =
        ∫ t in Ioi 0, (μ : Measure ℝ).real {a : ℝ | t < max a 0} := hlayer
    _ = ∫ t in Ioi 0, (μ : Measure ℝ).real (Ioi t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change
        (μ : Measure ℝ).real {a : ℝ | t < max a 0} =
          (μ : Measure ℝ).real (Ioi t)
      exact congrArg (fun s : Set ℝ => (μ : Measure ℝ).real s) (hset t ht)

/-- Layer cake for the negative part: `∫ max(-x, 0) dμ = ∫₀^∞ μ(-∞, -s] ds`. -/
theorem integral_max_neg_eq (hint : Integrable id (μ : Measure ℝ)) :
    ∫ x, max (-x) 0 ∂(μ : Measure ℝ) = ∫ s in Ioi 0, (μ : Measure ℝ).real (Iic (-s)) := by
  have hpos : Integrable (fun x : ℝ => max (-x) 0) (μ : Measure ℝ) := by
    simpa using hint.neg.pos_part
  have hnonneg :
      0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => max (-x) 0) :=
    ae_of_all _ (fun x => le_max_right (-x) 0)
  have hlayer :=
    hpos.integral_eq_integral_meas_le hnonneg
  have hset :
      ∀ t : ℝ, t ∈ Ioi 0 →
        {a : ℝ | t ≤ max (-a) 0} = Iic (-t) := by
    intro t ht
    change 0 < t at ht
    ext a
    constructor
    · intro ha
      change t ≤ max (-a) 0 at ha
      have hta : t ≤ -a := by
        rcases (le_max_iff.mp ha) with h | h
        · exact h
        · linarith
      change a ≤ -t
      linarith
    · intro ha
      change a ≤ -t at ha
      change t ≤ max (-a) 0
      apply le_max_iff.mpr
      left
      linarith
  calc
    ∫ x, max (-x) 0 ∂(μ : Measure ℝ) =
        ∫ t in Ioi 0, (μ : Measure ℝ).real
          {a : ℝ | t ≤ max (-a) 0} := hlayer
    _ = ∫ t in Ioi 0, (μ : Measure ℝ).real (Iic (-t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change
        (μ : Measure ℝ).real {a : ℝ | t ≤ max (-a) 0} =
          (μ : Measure ℝ).real (Iic (-t))
      exact congrArg (fun s : Set ℝ => (μ : Measure ℝ).real s) (hset t ht)

/-- The tail `t ↦ μ(t, ∞)` is integrable on `(0, ∞)` for an integrable law. -/
theorem integrableOn_measureReal_Ioi (hint : Integrable id (μ : Measure ℝ)) :
    IntegrableOn (fun t => (μ : Measure ℝ).real (Ioi t)) (Ioi 0) := by
  let f : ℝ → ℝ≥0∞ := fun t => (μ : Measure ℝ) (Ioi t)
  have hf_anti : Antitone f := by
    intro a b hab
    dsimp [f]
    exact measure_mono (Ioi_subset_Ioi hab)
  have hf_ae :
      AEMeasurable f (volume.restrict (Ioi 0)) :=
    hf_anti.measurable.aemeasurable
  have hmax : Integrable (fun x : ℝ => max x 0) (μ : Measure ℝ) := by
    simpa using hint.pos_part
  have hmax_nonneg :
      0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => max x 0) :=
    ae_of_all _ (fun x => le_max_right x 0)
  have hmax_meas :
      AEMeasurable (fun x : ℝ => max x 0) (μ : Measure ℝ) :=
    (measurable_id.max measurable_const).aemeasurable
  have hlayer :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt
      (μ : Measure ℝ) hmax_nonneg hmax_meas
  have hset :
      ∀ t : ℝ, t ∈ Ioi 0 →
        {x : ℝ | t < max x 0} = Ioi t := by
    intro t ht
    change 0 < t at ht
    ext x
    constructor
    · intro hx
      change t < max x 0 at hx
      by_cases hxp : 0 ≤ x
      · change t < x
        simpa [max_eq_left hxp] using hx
      · have hx0 : x ≤ 0 := le_of_not_ge hxp
        have hmaxx : max x 0 = 0 := max_eq_right hx0
        rw [hmaxx] at hx
        exfalso
        linarith
    · intro hx
      change t < x at hx
      exact lt_of_lt_of_le hx (le_max_left x 0)
  have hEq :
      (∫⁻ t in Ioi 0, f t) =
        ∫⁻ t in Ioi 0, (μ : Measure ℝ) {x : ℝ | t < max x 0} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [f]
    exact congrArg (fun s : Set ℝ => (μ : Measure ℝ) s) (hset t ht).symm
  have hfinite :
      (∫⁻ x, ENNReal.ofReal (max x 0) ∂(μ : Measure ℝ)) < ∞ := by
    refine (lintegral_mono ?_).trans_lt hmax.2
    intro x
    exact Real.ofReal_le_enorm _
  have htail :
      (∫⁻ t in Ioi 0, f t) < ∞ := by
    calc
      (∫⁻ t in Ioi 0, f t) =
          ∫⁻ t in Ioi 0, (μ : Measure ℝ) {x : ℝ | t < max x 0} := hEq
      _ = ∫⁻ x, ENNReal.ofReal (max x 0) ∂(μ : Measure ℝ) :=
        hlayer.symm
      _ < ∞ := hfinite
  have htoReal :
      Integrable (fun t : ℝ => (f t).toReal)
        (volume.restrict (Ioi 0)) :=
    integrable_toReal_of_lintegral_ne_top
      (f := f) hf_ae htail.ne
  change
    Integrable
      (fun t : ℝ => ((μ : Measure ℝ) (Ioi t)).toReal)
      (volume.restrict (Ioi 0))
  simpa [f] using htoReal

theorem integrableOn_measureReal_Iic_neg (hint : Integrable id (μ : Measure ℝ)) :
    IntegrableOn (fun s => (μ : Measure ℝ).real (Iic (-s))) (Ioi 0) := by
  let f : ℝ → ℝ≥0∞ := fun s => (μ : Measure ℝ) (Iic (-s))
  have hf_anti : Antitone f := by
    intro a b hab
    dsimp [f]
    apply measure_mono
    intro x hx
    change x ≤ -b at hx
    change x ≤ -a
    linarith
  have hf_ae :
      AEMeasurable f (volume.restrict (Ioi 0)) :=
    hf_anti.measurable.aemeasurable
  have hmax : Integrable (fun x : ℝ => max (-x) 0) (μ : Measure ℝ) := by
    simpa using hint.neg.pos_part
  have hmax_nonneg :
      0 ≤ᵐ[(μ : Measure ℝ)] (fun x : ℝ => max (-x) 0) :=
    ae_of_all _ (fun x => le_max_right (-x) 0)
  have hmax_meas :
      AEMeasurable (fun x : ℝ => max (-x) 0) (μ : Measure ℝ) :=
    (measurable_id.neg.max measurable_const).aemeasurable
  have hlayer :=
    MeasureTheory.lintegral_eq_lintegral_meas_le
      (μ : Measure ℝ) hmax_nonneg hmax_meas
  have hset :
      ∀ t : ℝ, t ∈ Ioi 0 →
        {x : ℝ | t ≤ max (-x) 0} = Iic (-t) := by
    intro t ht
    change 0 < t at ht
    ext x
    constructor
    · intro hx
      change t ≤ max (-x) 0 at hx
      have htx : t ≤ -x := by
        rcases (le_max_iff.mp hx) with h | h
        · exact h
        · linarith
      change x ≤ -t
      linarith
    · intro hx
      change x ≤ -t at hx
      change t ≤ max (-x) 0
      apply le_max_iff.mpr
      left
      linarith
  have hEq :
      (∫⁻ t in Ioi 0, f t) =
        ∫⁻ t in Ioi 0, (μ : Measure ℝ)
          {x : ℝ | t ≤ max (-x) 0} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp [f]
    exact congrArg (fun s : Set ℝ => (μ : Measure ℝ) s) (hset t ht).symm
  have hfinite :
      (∫⁻ x, ENNReal.ofReal (max (-x) 0) ∂(μ : Measure ℝ)) < ∞ := by
    refine (lintegral_mono ?_).trans_lt hmax.2
    intro x
    exact Real.ofReal_le_enorm _
  have htail :
      (∫⁻ t in Ioi 0, f t) < ∞ := by
    calc
      (∫⁻ t in Ioi 0, f t) =
          ∫⁻ t in Ioi 0, (μ : Measure ℝ)
            {x : ℝ | t ≤ max (-x) 0} := hEq
      _ = ∫⁻ x, ENNReal.ofReal (max (-x) 0) ∂(μ : Measure ℝ) :=
        hlayer.symm
      _ < ∞ := hfinite
  have htoReal :
      Integrable (fun t : ℝ => (f t).toReal)
        (volume.restrict (Ioi 0)) :=
    integrable_toReal_of_lintegral_ne_top
      (f := f) hf_ae htail.ne
  change
    Integrable
      (fun s : ℝ => ((μ : Measure ℝ) (Iic (-s))).toReal)
      (volume.restrict (Ioi 0))
  simpa [f] using htoReal

/-- Reflection to the negative half-line: `1 - μ(t, ∞)` on `(-∞, 0)` is the reflection of
`s ↦ μ(-∞, -s]`, in integrability and integral. -/
theorem integrableOn_one_sub_measureReal_Ioi_and_eq (hint : Integrable id (μ : Measure ℝ)) :
    IntegrableOn (fun t => 1 - (μ : Measure ℝ).real (Ioi t)) (Iio 0) ∧
      ∫ t in Iio 0, (1 - (μ : Measure ℝ).real (Ioi t)) =
        ∫ s in Ioi 0, (μ : Measure ℝ).real (Iic (-s)) := by
  let h : ℝ → ℝ := fun s => (μ : Measure ℝ).real (Iic (-s))

  have hcomp (t : ℝ) :
      1 - (μ : Measure ℝ).real (Ioi t) =
        (μ : Measure ℝ).real (Iic t) := by
    have hc :=
      measureReal_compl (μ := (μ : Measure ℝ)) (s := Ioi t) measurableSet_Ioi
    simpa [compl_Ioi] using hc.symm

  have hpoint (t : ℝ) :
      1 - (μ : Measure ℝ).real (Ioi t) = h (-t) := by
    rw [hcomp]
    simp [h]

  have hbase :
      IntegrableOn h (Ioi 0) :=
    integrableOn_measureReal_Iic_neg hint

  have hreflect :
      IntegrableOn (fun t : ℝ => h (-t)) (Iio 0) := by
    have h' := hbase.comp_neg
    simpa [h, Set.neg_Ioi] using h'

  have hintneg :
      IntegrableOn
        (fun t : ℝ => 1 - (μ : Measure ℝ).real (Ioi t)) (Iio 0) := by
    apply hreflect.congr
    filter_upwards [] with t
    exact (hpoint t).symm

  have htrans :
      (∫ x in Ioi 0, h (-(-x))) =
        ∫ x in Iic 0, h (-x) := by
    simp

  have hiic :
      (∫ x in Iic 0, h (-x)) =
        ∫ x in Iio 0, h (-x) := by
    rw [integral_Iic_eq_integral_Iio]

  refine ⟨hintneg, ?_⟩
  calc
    ∫ t in Iio 0, (1 - (μ : Measure ℝ).real (Ioi t)) =
        ∫ t in Iio 0, h (-t) := by
          apply setIntegral_congr_fun measurableSet_Iio
          intro t ht
          exact hpoint t
    _ = ∫ t in Iic 0, h (-t) := hiic.symm
    _ = ∫ t in Ioi 0, h t := by
          simp
    _ = ∫ s in Ioi 0, (μ : Measure ℝ).real (Iic (-s)) := by
          rfl

/-- Layer cake at the barycenter: for an integrable law with mean `0`, the tail `G` satisfies
`G ∈ L¹(0, ∞)`, `1 - G ∈ L¹(-∞, 0)` and `∫₀^∞ G = ∫_{-∞}^0 (1 - G)`. -/
theorem integral_Ioi_measureReal_Ioi_eq (hint : Integrable id (μ : Measure ℝ))
    (hmean : ∫ x, x ∂(μ : Measure ℝ) = 0) :
    IntegrableOn (fun t => (μ : Measure ℝ).real (Ioi t)) (Ioi 0) ∧
      IntegrableOn (fun t => 1 - (μ : Measure ℝ).real (Ioi t)) (Iio 0) ∧
      ∫ t in Ioi 0, (μ : Measure ℝ).real (Ioi t) =
        ∫ t in Iio 0, (1 - (μ : Measure ℝ).real (Ioi t)) := by
  have hneg :=
    integrableOn_one_sub_measureReal_Ioi_and_eq hint
  refine ⟨integrableOn_measureReal_Ioi hint, hneg.1, ?_⟩
  have hmax : Integrable (fun x : ℝ => max x 0) (μ : Measure ℝ) := by
    simpa using hint.pos_part
  have hmaxneg : Integrable (fun x : ℝ => max (-x) 0) (μ : Measure ℝ) := by
    simpa using hint.neg.pos_part
  have hfun : ∀ x : ℝ, x = max x 0 - max (-x) 0 := by
    intro x
    by_cases hx : 0 ≤ x
    · have hnx : -x ≤ 0 := by linarith
      rw [max_eq_left hx, max_eq_right hnx]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have hnx : 0 ≤ -x := by linarith
      rw [max_eq_right hx', max_eq_left hnx]
      ring
  have hrewrite :
      (∫ x, x ∂(μ : Measure ℝ)) =
        ∫ x, (max x 0 - max (-x) 0) ∂(μ : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact hfun x
  have hsub :
      (∫ x, (max x 0 - max (-x) 0) ∂(μ : Measure ℝ)) =
        (∫ x, max x 0 ∂(μ : Measure ℝ)) -
          ∫ x, max (-x) 0 ∂(μ : Measure ℝ) := by
    exact integral_sub hmax hmaxneg
  have hbalance :
      (∫ x, max x 0 ∂(μ : Measure ℝ)) =
        ∫ x, max (-x) 0 ∂(μ : Measure ℝ) := by
    linarith [hmean, hrewrite, hsub]
  calc
    ∫ t in Ioi 0, (μ : Measure ℝ).real (Ioi t) =
        ∫ x, max x 0 ∂(μ : Measure ℝ) :=
      (integral_max_eq hint).symm
    _ = ∫ x, max (-x) 0 ∂(μ : Measure ℝ) := hbalance
    _ = ∫ t in Ioi 0, (μ : Measure ℝ).real (Iic (-t)) :=
      integral_max_neg_eq hint
    _ = ∫ t in Iio 0, (1 - (μ : Measure ℝ).real (Ioi t)) :=
      hneg.2.symm

/-- One side of Grünbaum's lemma: a log-concave law with barycenter `0` and `μ(0, ∞) > 0` has
`μ(0, ∞) ≥ 1/e`. -/
theorem exp_neg_one_le_measureReal_Ioi (hμ : LogConcave μ) (hmean : ∫ x, x ∂(μ : Measure ℝ) = 0)
    (hpos : 0 < (μ : Measure ℝ).real (Ioi 0)) :
    Real.exp (-1) ≤ (μ : Measure ℝ).real (Ioi 0) := by
  let g : ℝ → ℝ := fun t => (μ : Measure ℝ).real (Ioi t)

  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    dsimp [g]
    exact measureReal_nonneg

  have hg1 : ∀ t, g t ≤ 1 := by
    intro t
    dsimp [g]
    exact measureReal_le_one

  have hanti : Antitone g := by
    intro a b hab
    dsimp [g]
    exact measureReal_mono (Ioi_subset_Ioi hab)

  have hlc :
      ∀ a b θ : ℝ, 0 < θ → θ < 1 →
        g a ^ θ * g b ^ (1 - θ) ≤ g (θ * a + (1 - θ) * b) := by
    intro a b θ hθ0 hθ1
    dsimp [g]
    exact measureReal_Ioi_rpow_mul_le hμ a b θ hθ0 hθ1

  have hmono_neg :
      Monotone (fun n : ℕ => Ioi (-(n : ℝ))) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hmn
    linarith

  have hunion_neg :
      (⋃ n : ℕ, Ioi (-(n : ℝ))) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      apply mem_iUnion.2
      refine ⟨n, ?_⟩
      change -(n : ℝ) < x
      linarith

  have hmeasure_neg :
      Tendsto
        (fun n : ℕ => (μ : Measure ℝ) (Ioi (-(n : ℝ))))
        atTop
        (𝓝 ((μ : Measure ℝ) Set.univ)) := by
    have h :=
      tendsto_measure_iUnion_atTop
        (μ := (μ : Measure ℝ))
        hmono_neg
    rw [hunion_neg] at h
    simpa [Function.comp_def] using h

  have hseq_real :
      Tendsto
        (fun n : ℕ => g (-(n : ℝ)))
        atTop
        (𝓝 1) := by
    have hto :
        Tendsto
          (fun n : ℕ => ((μ : Measure ℝ) (Ioi (-(n : ℝ)))).toReal)
          atTop
          (𝓝 (((μ : Measure ℝ) Set.univ).toReal)) :=
      (ENNReal.continuousAt_toReal
        (measure_ne_top (μ := (μ : Measure ℝ)) Set.univ)).tendsto.comp hmeasure_neg
    have huniv : ((μ : Measure ℝ) Set.univ).toReal = 1 := by
      rw [measure_univ]
      simp
    rw [huniv] at hto
    change
      Tendsto
        (fun n : ℕ => ((μ : Measure ℝ) (Ioi (-(n : ℝ)))).toReal)
        atTop
        (𝓝 1)
    exact hto

  have hlim : Tendsto g atBot (𝓝 1) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      have hev :
          ∀ᶠ n : ℕ in atTop, a < g (-(n : ℝ)) :=
        hseq_real.eventually (eventually_gt_nhds ha)
      obtain ⟨n, hn⟩ := eventually_atTop.1 hev
      refine eventually_atBot.2 ⟨-(n : ℝ), ?_⟩
      intro t ht
      have hle : t ≤ -(n : ℝ) := ht
      have hmono : g (-(n : ℝ)) ≤ g t := hanti hle
      exact lt_of_lt_of_le (hn n le_rfl) hmono
    · intro b hb
      filter_upwards [] with t
      exact lt_of_le_of_lt (hg1 t) hb

  have hmono_pos :
      Monotone (fun n : ℕ => Ioi (1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply Ioi_subset_Ioi
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hmn
    have hden : 0 < (m : ℝ) + 1 := by positivity
    apply one_div_le_one_div_of_le hden
    linarith

  have hunion_pos :
      (⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1))) = Ioi 0 := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨n, hn⟩
      change 1 / ((n : ℝ) + 1) < x at hn
      have hzero : 0 < x := by
        have hleft : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact hzero
    · intro hx
      change 0 < x at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
      apply mem_iUnion.2
      refine ⟨n, ?_⟩
      change 1 / ((n : ℝ) + 1) < x
      have hnx : 1 < (n : ℝ) * x := by
        exact (div_lt_iff₀ hx).mp hn
      have hden : 0 < (n : ℝ) + 1 := by positivity
      apply (div_lt_iff₀ hden).2
      nlinarith

  have hmeasure_pos :
      Tendsto
        (fun n : ℕ => (μ : Measure ℝ) (Ioi (1 / ((n : ℝ) + 1))))
        atTop
        (𝓝 ((μ : Measure ℝ) (Ioi 0))) := by
    have h :=
      tendsto_measure_iUnion_atTop
        (μ := (μ : Measure ℝ))
        hmono_pos
    rw [hunion_pos] at h
    simpa [Function.comp_def] using h

  have hseq_pos :
      Tendsto
        (fun n : ℕ => g (1 / ((n : ℝ) + 1)))
        atTop
        (𝓝 (g 0)) := by
    have hto :
        Tendsto
          (fun n : ℕ =>
            ((μ : Measure ℝ) (Ioi (1 / ((n : ℝ) + 1)))).toReal)
          atTop
          (𝓝 (((μ : Measure ℝ) (Ioi 0)).toReal)) :=
      (ENNReal.continuousAt_toReal
        (measure_ne_top (μ := (μ : Measure ℝ)) (Ioi 0))).tendsto.comp hmeasure_pos
    change
      Tendsto
        (fun n : ℕ =>
          ((μ : Measure ℝ) (Ioi (1 / ((n : ℝ) + 1)))).toReal)
        atTop
        (𝓝 ((μ : Measure ℝ).real (Ioi 0)))
    exact hto

  have hs : ∃ s > 0, 0 < g s := by
    have hev :
        ∀ᶠ n : ℕ in atTop, 0 < g (1 / ((n : ℝ) + 1)) :=
      hseq_pos.eventually (eventually_gt_nhds hpos)
    obtain ⟨n, hn⟩ := eventually_atTop.1 hev
    refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
    exact hn n le_rfl

  by_cases hzero : g 0 = 1
  · change Real.exp (-1) ≤ g 0
    rw [hzero]
    calc
      Real.exp (-1) ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        norm_num
      _ = 1 := Real.exp_zero
  · have hlt : g 0 < 1 :=
      lt_of_le_of_ne (hg1 0) hzero
    obtain ⟨a, ha, htan⟩ :=
      exists_le_mul_exp hg0 hanti hlc hlim hpos hlt hs
    obtain ⟨hint₁, hint₂, heq⟩ :=
      integral_Ioi_measureReal_Ioi_eq hμ.integrable_id hmean
    exact
      exp_neg_one_le_of_integral_eq ha hg1 hpos htan
        hint₁ hint₂ heq

/-- If the barycenter `0` lies in the interior of the support, both half-lines `(0, ∞)` and
`(-∞, 0)` have positive mass. -/
theorem measureReal_Ioi_pos_and_Iio_pos (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) (hmean : ∫ x, x ∂(μ : Measure ℝ) = 0) :
    0 < (μ : Measure ℝ).real (Ioi 0) ∧ 0 < (μ : Measure ℝ).real (Iio 0) := by
  have hzero : (0 : ℝ) ∈ interior (μ : Measure ℝ).support := by
    have hmem := hμ.mean_mem_interior_support hi
    have hmean' : (∫ x, id x ∂(μ : Measure ℝ)) = 0 := by
      simpa [id] using hmean
    rw [hmean'] at hmem
    exact hmem

  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior 0 hzero

  have hεhalf_pos : 0 < ε / 2 := by
    linarith

  have hεhalf_mem :
      ε / 2 ∈ interior (μ : Measure ℝ).support := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hεhalf_pos]
    linarith

  have hnegεhalf_mem :
      -ε / 2 ∈ interior (μ : Measure ℝ).support := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg]
    · linarith
    · linarith

  have hεhalf_support : ε / 2 ∈ (μ : Measure ℝ).support :=
    interior_subset hεhalf_mem

  have hnegεhalf_support : -ε / 2 ∈ (μ : Measure ℝ).support :=
    interior_subset hnegεhalf_mem

  have hIoi : 0 < (μ : Measure ℝ) (Ioi 0) := by
    have h :=
      (Measure.mem_support_iff_forall
        (μ := (μ : Measure ℝ)) (x := ε / 2)).mp hεhalf_support
    exact h (Ioi 0) (Ioi_mem_nhds (by linarith))

  have hIio : 0 < (μ : Measure ℝ) (Iio 0) := by
    have h :=
      (Measure.mem_support_iff_forall
        (μ := (μ : Measure ℝ)) (x := -ε / 2)).mp hnegεhalf_support
    exact h (Iio 0) (Iio_mem_nhds (by linarith))

  constructor
  · change 0 < ((μ : Measure ℝ) (Ioi 0)).toReal
    exact ENNReal.toReal_pos (ne_of_gt hIoi) (measure_ne_top _ _)
  · change 0 < ((μ : Measure ℝ) (Iio 0)).toReal
    exact ENNReal.toReal_pos (ne_of_gt hIio) (measure_ne_top _ _)

theorem reflect_logConcave (hμ : LogConcave μ) (hmean : ∫ x, x ∂(μ : Measure ℝ) = 0) :
    LogConcave (Probability.mapContinuousLinearEquiv μ (ContinuousLinearEquiv.neg ℝ)) ∧
      ∫ x,
            x ∂(Probability.mapContinuousLinearEquiv μ (ContinuousLinearEquiv.neg ℝ) :
              Measure ℝ) =
          0 ∧
        (Probability.mapContinuousLinearEquiv μ (ContinuousLinearEquiv.neg ℝ) : Measure ℝ).real
            (Ioi 0) =
          (μ : Measure ℝ).real (Iio 0) := by
  let T : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ
  let ν : ProbabilityMeasure ℝ := Probability.mapContinuousLinearEquiv μ T
  have hν : LogConcave ν := by exact hμ.mapContinuousLinearEquiv T
  have hcoe : (ν : Measure ℝ) = (μ : Measure ℝ).map T := by rfl
  have hν_integrable : Integrable id (ν : Measure ℝ) := hν.integrable_id
  have hν_integrable' : Integrable id ((μ : Measure ℝ).map T) := by
    rw [← hcoe]
    exact hν_integrable
  have hmap : ∫ x, id x ∂((μ : Measure ℝ).map T) = ∫ x, id (T x) ∂(μ : Measure ℝ) := by
    rw [integral_map T.continuous.aemeasurable]
    exact hν_integrable'.aestronglyMeasurable
  have hνmean : ∫ x, x ∂(ν : Measure ℝ) = 0 := by
    calc
      ∫ x, x ∂(ν : Measure ℝ) = ∫ x, id x ∂((μ : Measure ℝ).map T) := by
        rw [hcoe]
        rfl
      _ = ∫ x, id (T x) ∂(μ : Measure ℝ) := hmap
      _ = ∫ x, -x ∂(μ : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change T x = -x
        rfl
      _ = -(∫ x, x ∂(μ : Measure ℝ)) := by rw [integral_neg]
      _ = 0 := by rw [hmean, neg_zero]
  have hmass : (ν : Measure ℝ) (Ioi 0) = (μ : Measure ℝ) (Iio 0) := by
    rw [hcoe, Measure.map_apply T.continuous.measurable measurableSet_Ioi]
    have hpre : T ⁻¹' Ioi 0 = Iio 0 := by
      ext x
      change 0 < T x ↔ x < 0
      change 0 < -x ↔ x < 0
      constructor <;> intro hx <;> linarith
    rw [hpre]
  have hreal : (ν : Measure ℝ).real (Ioi 0) = (μ : Measure ℝ).real (Iio 0) := by
    change ((ν : Measure ℝ) (Ioi 0)).toReal = ((μ : Measure ℝ) (Iio 0)).toReal
    exact congrArg ENNReal.toReal hmass
  refine ⟨?_, ?_, ?_⟩
  · simpa [ν, T] using hν
  · simpa [ν, T] using hνmean
  · simpa [ν, T] using hreal

/-- Guédon–Milman (2011), Lemma 2.2 (Grünbaum): a real random variable with a log-concave density
and barycenter at the origin satisfies `1/e ≤ P(X ≥ 0) ≤ 1 - 1/e`. -/
theorem exp_neg_one_le_measureReal_Ici (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) (hmean : ∫ x, x ∂(μ : Measure ℝ) = 0) :
    Real.exp (-1) ≤ (μ : Measure ℝ).real (Ici 0) ∧
      (μ : Measure ℝ).real (Ici 0) ≤ 1 - Real.exp (-1) := by
  obtain ⟨hp, hn⟩ := measureReal_Ioi_pos_and_Iio_pos hμ hi hmean

  have hlow :
      Real.exp (-1) ≤ (μ : Measure ℝ).real (Ici 0) := by
    exact
      (exp_neg_one_le_measureReal_Ioi hμ hmean hp).trans
        (measureReal_mono Ioi_subset_Ici_self)

  obtain ⟨hν, hνmean, hνI⟩ := reflect_logConcave hμ hmean

  have hνpos :
      0 < (Probability.mapContinuousLinearEquiv μ (ContinuousLinearEquiv.neg ℝ) :
        Measure ℝ).real (Ioi 0) := by
    rw [hνI]
    exact hn

  have hu :
      Real.exp (-1) ≤
        (Probability.mapContinuousLinearEquiv μ (ContinuousLinearEquiv.neg ℝ) :
          Measure ℝ).real (Ioi 0) :=
    exp_neg_one_le_measureReal_Ioi hν hνmean hνpos

  rw [hνI] at hu

  have hcomp :
      (μ : Measure ℝ).real (Ici 0) =
        1 - (μ : Measure ℝ).real (Iio 0) := by
    have hc :=
      measureReal_compl (μ := (μ : Measure ℝ)) (s := Iio 0) measurableSet_Iio
    simpa [compl_Iio] using hc

  constructor
  · exact hlow
  · rw [hcomp]
    linarith

end FunctionalInequalities.KLS.LogConcave
