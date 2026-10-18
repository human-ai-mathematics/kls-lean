import FunctionalInequalities.Probability.Line.Cdf
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Probability.Moments.Variance

/-!
# Affine quantile-density profiles on the unit interval

Source: Blueprint `thm:one-dimensional-logconcave-poincare` (sharp form with constant `4`),
supporting calculus; the argument follows Section 4 of the collaborator's constant-4 source audit (a locally kept record). Read `affineWeight`,
`affineQuantile`, `hasDerivAt_affineQuantile` and `one_div_le_variance_affineQuantile`.

For `a, b > 0` the affine weight `w(u) = a² (1 - u) + b² u` is positive on `[0, 1]` and the quantile
function of the law with quantile density `w`, anchored at `p`, is `q(u) = ∫_p^u 1 / w`. Its variance
under the uniform law on `[0, 1]` is at least `1 / (a + b)⁴`: for `a = b` it is `1 / (12 a⁴)`, and
for `a ≠ b` it equals `(1 - a² b² (log b² - log a²)² / (b² - a²)²) / (b² - a²)²`, bounded below by the
elementary inequality `a b (log b - log a)² ≤ (b - a)²`, which is `t ≤ sinh t`.

Nothing here concerns a probability law other than the uniform law on `[0, 1]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology intervalIntegral

namespace FunctionalInequalities.Probability.Line

/-- The uniform probability law on the unit interval. -/
abbrev unitUniform : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitUniform :=
  ⟨by simp [unitUniform, Real.volume_Icc]⟩

/-- The affine weight `a² (1 - u) + b² u`. -/
def affineWeight (a b u : ℝ) : ℝ := a ^ 2 * (1 - u) + b ^ 2 * u

/-- The quantile function of the affine profile, anchored at `p`. -/
def affineQuantile (a b p u : ℝ) : ℝ := ∫ t in p..u, (affineWeight a b t)⁻¹

variable {a b : ℝ}

theorem affineWeight_pos (ha : 0 < a) (hb : 0 < b) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < affineWeight a b u := by
  unfold affineWeight
  rcases hu with ⟨h0, h1⟩
  have ha2 : 0 < a ^ 2 := by positivity
  have hb2 : 0 < b ^ 2 := by positivity
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; nlinarith
  · nlinarith [mul_pos ha2 (sub_pos.mpr h), mul_nonneg hb2.le h0]

theorem continuous_affineWeight : Continuous (affineWeight a b) := by
  unfold affineWeight; fun_prop

theorem hasDerivAt_affineWeight (u : ℝ) :
    HasDerivAt (affineWeight a b) (b ^ 2 - a ^ 2) u := by
  have h1 : HasDerivAt (fun u : ℝ ↦ a ^ 2 * (1 - u)) (a ^ 2 * (0 - 1)) u :=
    ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id' u)).const_mul (a ^ 2)
  have h2 : HasDerivAt (fun u : ℝ ↦ b ^ 2 * u) (b ^ 2 * 1) u := (hasDerivAt_id' u).const_mul (b ^ 2)
  exact (h1.add h2).congr_deriv (by ring)

theorem continuousOn_inv_affineWeight (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun t ↦ (affineWeight a b t)⁻¹) (Icc 0 1) :=
  continuous_affineWeight.continuousOn.inv₀ fun _ ht ↦ (affineWeight_pos ha hb ht).ne'

theorem intervalIntegrable_inv_affineWeight (ha : 0 < a) (hb : 0 < b) {p u : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t ↦ (affineWeight a b t)⁻¹) volume p u :=
  ((continuousOn_inv_affineWeight ha hb).mono (uIcc_subset_Icc hp hu)).intervalIntegrable

/-- The quantile function is differentiable in the open unit interval with derivative `1 / w`. -/
theorem hasDerivAt_affineQuantile (ha : 0 < a) (hb : 0 < b) {p u : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (affineQuantile a b p) (affineWeight a b u)⁻¹ u := by
  have hcont := (continuousOn_inv_affineWeight ha hb).mono Ioo_subset_Icc_self
  exact integral_hasDerivAt_right (intervalIntegrable_inv_affineWeight ha hb hp (Ioo_subset_Icc_self hu))
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo u hu)
    (hcont.continuousAt (isOpen_Ioo.mem_nhds hu))

/-- Closed form of the quantile function for `a ≠ b`. -/
theorem affineQuantile_eq (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 ≠ b ^ 2) {p u : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    affineQuantile a b p u =
      (Real.log (affineWeight a b u) - Real.log (affineWeight a b p)) / (b ^ 2 - a ^ 2) := by
  have hβ : b ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hderiv : ∀ t ∈ uIcc p u, HasDerivAt (fun t ↦ Real.log (affineWeight a b t) / (b ^ 2 - a ^ 2))
      (affineWeight a b t)⁻¹ t := by
    intro t ht
    have hpos := affineWeight_pos ha hb (uIcc_subset_Icc hp hu ht)
    have h := ((hasDerivAt_affineWeight t).log hpos.ne').div_const (b ^ 2 - a ^ 2)
    refine h.congr_deriv ?_
    rw [div_right_comm, div_self hβ, one_div]
  unfold affineQuantile
  rw [integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_inv_affineWeight ha hb hp hu)]
  ring

/-- Closed form of the quantile function for `a = b`. -/
theorem affineQuantile_self (a p u : ℝ) :
    affineQuantile a a p u = (u - p) / a ^ 2 := by
  have hw : ∀ t, affineWeight a a t = a ^ 2 := fun t ↦ by unfold affineWeight; ring
  unfold affineQuantile
  simp_rw [hw]
  rw [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

section Moments

theorem integral_log_affineWeight (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 ≠ b ^ 2) :
    ∫ u in (0 : ℝ)..1, Real.log (affineWeight a b u) =
      (b ^ 2 * Real.log (b ^ 2) - a ^ 2 * Real.log (a ^ 2)) / (b ^ 2 - a ^ 2) - 1 := by
  have hβ : b ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t ↦ (affineWeight a b t * Real.log (affineWeight a b t) - affineWeight a b t) /
        (b ^ 2 - a ^ 2)) (Real.log (affineWeight a b t)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hpos := affineWeight_pos ha hb ht
    have hw0 : affineWeight a b t ≠ 0 := hpos.ne'
    have hw := hasDerivAt_affineWeight (a := a) (b := b) t
    have h := ((hw.mul (hw.log hw0)).sub hw).div_const (b ^ 2 - a ^ 2)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun t ↦ Real.log (affineWeight a b t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Real.continuousOn_log.comp continuous_affineWeight.continuousOn
      fun t ht ↦ (affineWeight_pos ha hb ht).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : affineWeight a b 0 = a ^ 2 := by unfold affineWeight; ring
  have h1 : affineWeight a b 1 = b ^ 2 := by unfold affineWeight; ring
  rw [h0, h1]
  field_simp
  ring

theorem integral_log_sq_affineWeight (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 ≠ b ^ 2) :
    ∫ u in (0 : ℝ)..1, Real.log (affineWeight a b u) ^ 2 =
      (b ^ 2 * Real.log (b ^ 2) ^ 2 - a ^ 2 * Real.log (a ^ 2) ^ 2) / (b ^ 2 - a ^ 2) -
        2 * ((b ^ 2 * Real.log (b ^ 2) - a ^ 2 * Real.log (a ^ 2)) / (b ^ 2 - a ^ 2)) + 2 := by
  have hβ : b ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t ↦ affineWeight a b t * (Real.log (affineWeight a b t) ^ 2 -
        2 * Real.log (affineWeight a b t) + 2) / (b ^ 2 - a ^ 2))
      (Real.log (affineWeight a b t) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hpos := affineWeight_pos ha hb ht
    have hw0 : affineWeight a b t ≠ 0 := hpos.ne'
    have hw := hasDerivAt_affineWeight (a := a) (b := b) t
    have hL := hw.log hw0
    have h := (hw.mul (((hL.pow 2).sub (hL.const_mul 2)).add_const 2)).div_const (b ^ 2 - a ^ 2)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
    · simp only [Pi.sub_apply, Pi.pow_apply]
      field_simp
      ring
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  have hint : IntervalIntegrable (fun t ↦ Real.log (affineWeight a b t) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (Real.continuousOn_log.comp continuous_affineWeight.continuousOn
      fun t ht ↦ (affineWeight_pos ha hb ht).ne').pow 2
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : affineWeight a b 0 = a ^ 2 := by unfold affineWeight; ring
  have h1 : affineWeight a b 1 = b ^ 2 := by unfold affineWeight; ring
  rw [h0, h1]
  field_simp
  ring

/-- The variance of the uniform law on the unit interval is `1/12`. -/
theorem variance_id_unitUniform : variance (fun u : ℝ ↦ u) unitUniform = 1 / 12 := by
  have hmem : MemLp (fun u : ℝ ↦ u) 2 unitUniform :=
    MemLp.of_bound (continuous_id.aestronglyMeasurable) 1 (by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact ae_of_all _ fun u hu ↦ by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hu.1, hu.2])
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, unitUniform]
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one, integral_pow,
    integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one, integral_id]
  norm_num

/-- The variance of the affine quantile function for `a ≠ b`. -/
theorem variance_affineQuantile (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 ≠ b ^ 2) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    variance (affineQuantile a b p) unitUniform =
      (1 - a ^ 2 * b ^ 2 * (Real.log (b ^ 2) - Real.log (a ^ 2)) ^ 2 / (b ^ 2 - a ^ 2) ^ 2) /
        (b ^ 2 - a ^ 2) ^ 2 := by
  have hβ : b ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set L : ℝ → ℝ := fun u ↦ Real.log (affineWeight a b u) with hL
  have hLcont : ContinuousOn L (Icc 0 1) :=
    Real.continuousOn_log.comp continuous_affineWeight.continuousOn
      fun t ht ↦ (affineWeight_pos ha hb ht).ne'
  have hLmeas : AEStronglyMeasurable L unitUniform := hLcont.aestronglyMeasurable measurableSet_Icc
  have hLmem : MemLp L 2 unitUniform := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hLcont
    refine MemLp.of_bound hLmeas C ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun u hu ↦ hC u hu
  -- the quantile function agrees almost everywhere with the closed form
  have hae : affineQuantile a b p =ᵐ[unitUniform] fun u ↦ (L u - L p) * (b ^ 2 - a ^ 2)⁻¹ := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun u hu ↦ by
      rw [affineQuantile_eq ha hb hab hp hu, div_eq_mul_inv]
  rw [variance_congr hae, variance_mul_const, variance_sub_const hLmeas, variance_eq_sub hLmem]
  have h1 : ∫ u, L u ∂unitUniform = ∫ u in (0 : ℝ)..1, Real.log (affineWeight a b u) := by
    simp only [unitUniform]
    rw [integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one]
  have h2 : ∫ u, (L ^ 2) u ∂unitUniform = ∫ u in (0 : ℝ)..1, Real.log (affineWeight a b u) ^ 2 := by
    simp only [unitUniform, Pi.pow_apply]
    rw [integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one]
  rw [h1, h2, integral_log_affineWeight ha hb hab, integral_log_sq_affineWeight ha hb hab]
  field_simp
  ring

end Moments

section Inequality

/-- The elementary inequality `a b (log b - log a)² ≤ (b - a)²` for positive `a, b`; it is
`t ≤ sinh t` for `t = (log b - log a) / 2`. -/
theorem mul_mul_log_sub_sq_le (ha : 0 < a) (hb : 0 < b) :
    a * b * (Real.log b - Real.log a) ^ 2 ≤ (b - a) ^ 2 := by
  wlog hab : a ≤ b generalizing a b
  · have := this hb ha (le_of_not_ge hab)
    have e1 : (Real.log a - Real.log b) ^ 2 = (Real.log b - Real.log a) ^ 2 := by ring
    have e2 : (a - b) ^ 2 = (b - a) ^ 2 := by ring
    rw [e1, e2, mul_comm b a] at this
    exact this
  set s : ℝ := (Real.log b - Real.log a) / 2 with hs
  have hs0 : 0 ≤ s := by
    have := Real.log_le_log ha hab
    rw [hs]; linarith
  have hb' : b = a * Real.exp (2 * s) := by
    have : Real.exp (2 * s) = b / a := by
      rw [hs, show 2 * ((Real.log b - Real.log a) / 2) = Real.log b - Real.log a by ring,
        Real.exp_sub, Real.exp_log hb, Real.exp_log ha]
    rw [this]
    field_simp
  have hsinh : s ≤ Real.sinh s := Real.self_le_sinh_iff.mpr hs0
  have hsq : s ^ 2 ≤ Real.sinh s ^ 2 := pow_le_pow_left₀ hs0 hsinh 2
  have hexp : Real.exp (2 * s) - 1 = 2 * Real.exp s * Real.sinh s := by
    have he : Real.exp s ≠ 0 := Real.exp_ne_zero s
    rw [Real.sinh_eq, Real.exp_neg, show 2 * s = s + s by ring, Real.exp_add]
    field_simp
  have hlog : Real.log b - Real.log a = 2 * s := by rw [hs]; ring
  rw [hlog, hb']
  have hpos : 0 < a ^ 2 * Real.exp (2 * s) := by positivity
  have h2s : Real.exp (2 * s) = Real.exp s ^ 2 := by rw [show 2 * s = s + s by ring, Real.exp_add, sq]
  calc a * (a * Real.exp (2 * s)) * (2 * s) ^ 2 = 4 * (a ^ 2 * Real.exp (2 * s)) * s ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 * Real.exp (2 * s)) * Real.sinh s ^ 2 := by gcongr
    _ = (a * Real.exp (2 * s) - a) ^ 2 := by
        rw [show a * Real.exp (2 * s) - a = a * (Real.exp (2 * s) - 1) by ring, hexp, h2s]
        ring

/-- The variance of the affine quantile function is at least `1 / (a + b)⁴`. -/
theorem one_div_le_variance_affineQuantile (ha : 0 < a) (hb : 0 < b) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    1 / (a + b) ^ 4 ≤ variance (affineQuantile a b p) unitUniform := by
  by_cases hab : a = b
  · subst hab
    have hae : affineQuantile a a p =ᵐ[unitUniform] fun u ↦ (u - p) * (a ^ 2)⁻¹ :=
      ae_of_all _ fun u ↦ by rw [affineQuantile_self, div_eq_mul_inv]
    rw [variance_congr hae, variance_mul_const,
      variance_sub_const (X := fun u : ℝ ↦ u) continuous_id'.aestronglyMeasurable,
      variance_id_unitUniform]
    have h : (0 : ℝ) < (a ^ 2) ^ 2 := by positivity
    calc 1 / (a + a) ^ 4 = 1 / (16 * (a ^ 2) ^ 2) := by ring
      _ ≤ 1 / (12 * (a ^ 2) ^ 2) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = 1 / 12 * ((a ^ 2)⁻¹) ^ 2 := by rw [inv_pow, ← one_div, one_div_mul_one_div]
  · have hab2 : a ^ 2 ≠ b ^ 2 := fun h ↦ hab ((pow_left_inj₀ ha.le hb.le two_ne_zero).mp h)
    rw [variance_affineQuantile ha hb hab2 hp]
    have hβ : b ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab2)
    have hβ2 : 0 < (b ^ 2 - a ^ 2) ^ 2 := by positivity
    have hkey := mul_mul_log_sub_sq_le ha hb
    have hlog : Real.log (b ^ 2) - Real.log (a ^ 2) = 2 * (Real.log b - Real.log a) := by
      rw [Real.log_pow, Real.log_pow]; push_cast; ring
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hβeq : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    have hS : 0 < a + b := by positivity
    rw [hlog, div_le_div_iff₀ (by positivity) hβ2, one_mul]
    -- `(b² − a²)² ≤ (a+b)⁴ · (1 − a²b²·4(log b − log a)²/(b²−a²)²)`
    have hmain : a ^ 2 * b ^ 2 * (2 * (Real.log b - Real.log a)) ^ 2 / (b ^ 2 - a ^ 2) ^ 2 ≤
        4 * a * b / (a + b) ^ 2 := by
      rw [div_le_div_iff₀ hβ2 (by positivity), hβeq]
      have : a ^ 2 * b ^ 2 * (2 * (Real.log b - Real.log a)) ^ 2 * (a + b) ^ 2 =
          4 * (a * b * (Real.log b - Real.log a) ^ 2) * (a * b * (a + b) ^ 2) := by ring
      rw [this]
      have h2 : 4 * (a * b * (Real.log b - Real.log a) ^ 2) * (a * b * (a + b) ^ 2) ≤
          4 * (b - a) ^ 2 * (a * b * (a + b) ^ 2) := by
        have := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ a * b * (a + b) ^ 2)
        nlinarith [this]
      calc _ ≤ 4 * (b - a) ^ 2 * (a * b * (a + b) ^ 2) := h2
        _ = 4 * a * b * ((b - a) * (b + a)) ^ 2 := by ring
    have hfinal : (b ^ 2 - a ^ 2) ^ 2 ≤ (a + b) ^ 4 * (1 - 4 * a * b / (a + b) ^ 2) := by
      have : (a + b) ^ 4 * (1 - 4 * a * b / (a + b) ^ 2) = (a + b) ^ 2 * ((a + b) ^ 2 - 4 * a * b) := by
        field_simp
      rw [this, hβeq]
      have : (a + b) ^ 2 - 4 * a * b = (b - a) ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (a + b), sq_nonneg (b - a)]
    calc (b ^ 2 - a ^ 2) ^ 2 ≤ (a + b) ^ 4 * (1 - 4 * a * b / (a + b) ^ 2) := hfinal
      _ = (1 - 4 * a * b / (a + b) ^ 2) * (a + b) ^ 4 := mul_comm _ _
      _ ≤ (1 - a ^ 2 * b ^ 2 * (2 * (Real.log b - Real.log a)) ^ 2 / (b ^ 2 - a ^ 2) ^ 2) *
          (a + b) ^ 4 := by
          gcongr

end Inequality

end FunctionalInequalities.Probability.Line
