module

public import FunctionalInequalities.KLS.LogConcave.Line.Hazard
public import FunctionalInequalities.Poincare.Gaussian.Hardy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# A Hardy inequality for log-concave laws on the line

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, analytic core (compare Bobkov 1999,
Section 4, whose Cheeger route is replaced here by an integration-by-parts Hardy argument). Read
`Probability.Line.integral_sq_mul_le_of_le_integral_abs`, the one-sided interval bounds
`LineDensity.integral_sq_sub_mul_le_right` and `LineDensity.integral_sq_sub_mul_le_left`, their
half-line versions `LineDensity.setIntegral_Ioi_sq_sub_le` and
`LineDensity.setIntegral_Iic_sq_sub_le`, and the conclusion `LineDensity.smoothTest_holds`.

For a log-concave law `μ` with Borell density `ρ`, median `m` and `c = ρ m > 0`, the median
bounds `2 c (1 - F) ≤ ρ` on the right and `2 c F ≤ ρ` on the left of `m` turn an integration by
parts against `1 - F` (respectively `F`) into
`∫ (f - f m)² dμ ≤ (1 / c)² ∫ (f')² dμ` for every smooth admissible test `f`. Hence the smooth-test
Poincaré inequality holds with constant `(1 / c)²`.

Only the smooth-test inequality is asserted here; the comparison with the variance is in the
variance module and the final constant `12 · Var` is assembled afterwards.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities.Probability.Line

/-- Hardy step on an interval: if `∫ g² ρ ≤ ∫ 2 |g| |g'| W` and `2 W ≤ t ρ`, then
`∫ g² ρ ≤ t² ∫ g'² ρ`. -/
theorem integral_sq_mul_le_of_le_integral_abs {a b t : ℝ} (hab : a ≤ b)
    {g g' ρ W : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hρ : ContinuousOn ρ (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hρ0 : ∀ s ∈ Icc a b, 0 ≤ ρ s) (hWρ : ∀ s ∈ Icc a b, 2 * W s ≤ t * ρ s)
    (h : ∫ s in a..b, g s ^ 2 * ρ s ≤ ∫ s in a..b, 2 * |g s| * |g' s| * W s) :
    ∫ s in a..b, g s ^ 2 * ρ s ≤ t ^ 2 * ∫ s in a..b, g' s ^ 2 * ρ s := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint1 : IntervalIntegrable (fun s ↦ g s ^ 2 * ρ s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (hg.pow 2).mul hρ
  have hint2 : IntervalIntegrable (fun s ↦ g' s ^ 2 * ρ s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (hg'.pow 2).mul hρ
  have hint3 : IntervalIntegrable (fun s ↦ 2 * |g s| * |g' s| * W s) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact ((continuousOn_const.mul hg.abs).mul hg'.abs).mul hW
  have hpt : ∀ s ∈ Icc a b, 2 * |g s| * |g' s| * W s ≤
      g s ^ 2 * ρ s / 2 + t ^ 2 * (g' s ^ 2 * ρ s) / 2 := by
    intro s hs
    have hA := abs_nonneg (g s)
    have hB := abs_nonneg (g' s)
    have h1 := mul_le_mul_of_nonneg_left (hWρ s hs) (mul_nonneg hA hB)
    have h2 := mul_nonneg (hρ0 s hs) (sq_nonneg (|g s| - t * |g' s|))
    rw [← sq_abs (g s), ← sq_abs (g' s)]
    nlinarith
  have hmono := intervalIntegral.integral_mono_on hab hint3
    ((hint1.div_const 2).add ((hint2.const_mul (t ^ 2)).div_const 2)) hpt
  rw [intervalIntegral.integral_add (hint1.div_const 2) ((hint2.const_mul (t ^ 2)).div_const 2),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul] at hmono
  linarith

end FunctionalInequalities.Probability.Line

namespace FunctionalInequalities.KLS.LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

/-- Set integrals against the law are Lebesgue integrals weighted by the density. -/
theorem setIntegral_eq_integral_mul (g : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ : Measure ℝ) = ∫ x in s, g x * d.ρ x := by
  rw [d.withDensity_eq, setIntegral_withDensity_eq_setIntegral_toReal_smul
    d.measurable.ennreal_ofReal (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top) g hs]
  refine setIntegral_congr_fun hs fun x _ ↦ ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (d.nonneg x), mul_comm]

/-- Pointwise: the squared gradient energy density on `ℝ` is the squared derivative. -/
theorem norm_gradient_sq_eq_deriv_sq (f : ℝ → ℝ) (x : ℝ) :
    ‖gradient f x‖ ^ 2 = deriv f x ^ 2 := by
  rw [gradient_eq_deriv', Real.norm_eq_abs, sq_abs]

section Interval

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
  {m : ℝ} (hm : cdf μ m = 1 / 2)
include hμ hi hm

/-- Right of any point `p ≥ m` of the interior: `∫_p^x (f - f p)² ρ ≤ (1 / ρ m)² ∫_p^x (f')² ρ`
for `x ≥ p` in the interior of the support; the constant still comes from the median. -/
theorem integral_sq_sub_mul_le_right_of_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {p : ℝ}
    (hpΩ : p ∈ interior (μ : Measure ℝ).support) (hmp : m ≤ p) {x : ℝ}
    (hx : x ∈ interior (μ : Measure ℝ).support) (hpx : p ≤ x) :
    ∫ s in p..x, (f s - f p) ^ 2 * d.ρ s ≤
      (1 / d.ρ m) ^ 2 * ∫ s in p..x, deriv f s ^ 2 * d.ρ s := by
  have hmΩ := median_mem hμ hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  have hc' : d.ρ m ≠ 0 := hc.ne'
  have hIcc : Icc p x ⊆ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out hpΩ hx
  have huIcc : uIcc p x = Icc p x := uIcc_of_le hpx
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfd : ∀ s, HasDerivAt f (deriv f s) s := fun s ↦
    (hf.differentiable one_ne_zero s).hasDerivAt
  set W : ℝ → ℝ := fun s ↦ (μ : Measure ℝ).real (Ioi s) with hW
  have hWeq : W = fun s ↦ 1 - cdf μ s := funext fun s ↦ Probability.Line.measureReal_Ioi μ s
  have hWc : Continuous W := by
    rw [hWeq]
    exact continuous_const.sub d.continuous_cdf
  have hWd : ∀ s ∈ interior (μ : Measure ℝ).support, HasDerivAt W (-d.ρ s) s := by
    intro s hs
    rw [hWeq]
    simpa using (d.hasDerivAt_cdf hs).const_sub 1
  have hW0 : ∀ s, 0 ≤ W s := fun s ↦ measureReal_nonneg
  have hρc : ContinuousOn d.ρ (Icc p x) := d.continuousOn.mono hIcc
  have hu : ∀ s ∈ uIcc p x, HasDerivAt (fun s ↦ (f s - f p) ^ 2)
      (deriv f s * (f s - f p) + (f s - f p) * deriv f s) s := by
    intro s _
    have h := (hfd s).sub_const (f p)
    have h2 := h.mul h
    simp only [pow_two]
    exact h2
  have hv : ∀ s ∈ uIcc p x, HasDerivAt W (-d.ρ s) s := fun s hs ↦ hWd s (hIcc (huIcc ▸ hs))
  have hu' : IntervalIntegrable
      (fun s ↦ deriv f s * (f s - f p) + (f s - f p) * deriv f s) volume p x :=
    ((hf'c.mul (hfc.sub continuous_const)).add
      ((hfc.sub continuous_const).mul hf'c)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s ↦ -d.ρ s) volume p x := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hρc.neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  beta_reduce at hibp
  have hzero : (f p - f p) ^ 2 * W p = 0 := by simp
  have hneg : ∫ s in p..x, (f s - f p) ^ 2 * -d.ρ s = -∫ s in p..x, (f s - f p) ^ 2 * d.ρ s := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext s
    ring
  have hle : ∫ s in p..x, (f s - f p) ^ 2 * d.ρ s ≤
      ∫ s in p..x, 2 * |f s - f p| * |deriv f s| * W s := by
    have h1 : ∫ s in p..x, (deriv f s * (f s - f p) + (f s - f p) * deriv f s) * W s ≤
        ∫ s in p..x, 2 * |f s - f p| * |deriv f s| * W s := by
      refine intervalIntegral.integral_mono_on hpx
        ((((hf'c.mul (hfc.sub continuous_const)).add
          ((hfc.sub continuous_const).mul hf'c)).mul hWc).intervalIntegrable _ _)
        ((((continuous_const.mul (hfc.sub continuous_const).abs).mul hf'c.abs).mul
          hWc).intervalIntegrable _ _) fun s _ ↦ ?_
      have habs := le_abs_self ((f s - f p) * deriv f s)
      rw [abs_mul] at habs
      have : deriv f s * (f s - f p) + (f s - f p) * deriv f s ≤
          2 * |f s - f p| * |deriv f s| := by linarith
      exact mul_le_mul_of_nonneg_right this (hW0 s)
    have h2 : 0 ≤ (f x - f p) ^ 2 * W x := mul_nonneg (sq_nonneg _) (hW0 x)
    linarith
  refine Probability.Line.integral_sq_mul_le_of_le_integral_abs hpx
    (hfc.sub continuous_const).continuousOn hf'c.continuousOn hρc hWc.continuousOn
    (fun s _ ↦ d.nonneg s) (fun s hs ↦ ?_) hle
  have h := d.two_mul_measureReal_Ioi_le hμ hi hm (hmp.trans hs.1)
  calc 2 * W s = (1 / d.ρ m) * (2 * d.ρ m * W s) := by
        field_simp
    _ ≤ (1 / d.ρ m) * d.ρ s := mul_le_mul_of_nonneg_left h (by positivity)

/-- Right of the median: `∫_m^x (f - f m)² ρ ≤ (1 / ρ m)² ∫_m^x (f')² ρ` for `x` in the interior
of the support. -/
theorem integral_sq_sub_mul_le_right {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {x : ℝ}
    (hx : x ∈ interior (μ : Measure ℝ).support) (hmx : m ≤ x) :
    ∫ s in m..x, (f s - f m) ^ 2 * d.ρ s ≤
      (1 / d.ρ m) ^ 2 * ∫ s in m..x, deriv f s ^ 2 * d.ρ s :=
  d.integral_sq_sub_mul_le_right_of_le hμ hi hm hf (median_mem hμ hi hm) le_rfl hx hmx

/-- Left of any point `p ≤ m` of the interior: `∫_x^p (f - f p)² ρ ≤ (1 / ρ m)² ∫_x^p (f')² ρ`
for `x ≤ p` in the interior of the support; the constant still comes from the median. -/
theorem integral_sq_sub_mul_le_left_of_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {p : ℝ}
    (hpΩ : p ∈ interior (μ : Measure ℝ).support) (hpm : p ≤ m) {x : ℝ}
    (hx : x ∈ interior (μ : Measure ℝ).support) (hxp : x ≤ p) :
    ∫ s in x..p, (f s - f p) ^ 2 * d.ρ s ≤
      (1 / d.ρ m) ^ 2 * ∫ s in x..p, deriv f s ^ 2 * d.ρ s := by
  have hmΩ := median_mem hμ hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  have hc' : d.ρ m ≠ 0 := hc.ne'
  have hIcc : Icc x p ⊆ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out hx hpΩ
  have huIcc : uIcc x p = Icc x p := uIcc_of_le hxp
  have hfc : Continuous f := hf.continuous
  have hf'c : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfd : ∀ s, HasDerivAt f (deriv f s) s := fun s ↦
    (hf.differentiable one_ne_zero s).hasDerivAt
  have hFc : Continuous (cdf μ) := d.continuous_cdf
  have hF0 : ∀ s, 0 ≤ cdf μ s := fun s ↦ Probability.Line.cdf_nonneg μ s
  have hρc : ContinuousOn d.ρ (Icc x p) := d.continuousOn.mono hIcc
  have hu : ∀ s ∈ uIcc x p, HasDerivAt (fun s ↦ (f s - f p) ^ 2)
      (deriv f s * (f s - f p) + (f s - f p) * deriv f s) s := by
    intro s _
    have h := (hfd s).sub_const (f p)
    have h2 := h.mul h
    simp only [pow_two]
    exact h2
  have hv : ∀ s ∈ uIcc x p, HasDerivAt (cdf μ) (d.ρ s) s := fun s hs ↦
    d.hasDerivAt_cdf (hIcc (huIcc ▸ hs))
  have hu' : IntervalIntegrable
      (fun s ↦ deriv f s * (f s - f p) + (f s - f p) * deriv f s) volume x p :=
    ((hf'c.mul (hfc.sub continuous_const)).add
      ((hfc.sub continuous_const).mul hf'c)).intervalIntegrable _ _
  have hv' : IntervalIntegrable d.ρ volume x p := d.integrable.intervalIntegrable
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  beta_reduce at hibp
  have hzero : (f p - f p) ^ 2 * cdf μ p = 0 := by simp
  have hle : ∫ s in x..p, (f s - f p) ^ 2 * d.ρ s ≤
      ∫ s in x..p, 2 * |f s - f p| * |deriv f s| * cdf μ s := by
    have h1 : ∫ s in x..p, -((deriv f s * (f s - f p) + (f s - f p) * deriv f s) * cdf μ s) ≤
        ∫ s in x..p, 2 * |f s - f p| * |deriv f s| * cdf μ s := by
      refine intervalIntegral.integral_mono_on hxp
        ((((hf'c.mul (hfc.sub continuous_const)).add
          ((hfc.sub continuous_const).mul hf'c)).mul hFc).neg.intervalIntegrable _ _)
        ((((continuous_const.mul (hfc.sub continuous_const).abs).mul hf'c.abs).mul
          hFc).intervalIntegrable _ _) fun s _ ↦ ?_
      have habs := neg_abs_le ((f s - f p) * deriv f s)
      rw [abs_mul] at habs
      have : -(deriv f s * (f s - f p) + (f s - f p) * deriv f s) ≤
          2 * |f s - f p| * |deriv f s| := by linarith
      rw [← neg_mul]
      exact mul_le_mul_of_nonneg_right this (hF0 s)
    rw [intervalIntegral.integral_neg] at h1
    have h2 : 0 ≤ (f x - f p) ^ 2 * cdf μ x := mul_nonneg (sq_nonneg _) (hF0 x)
    linarith
  refine Probability.Line.integral_sq_mul_le_of_le_integral_abs hxp
    (hfc.sub continuous_const).continuousOn hf'c.continuousOn hρc hFc.continuousOn
    (fun s _ ↦ d.nonneg s) (fun s hs ↦ ?_) hle
  have h := d.two_mul_cdf_le hμ hi hm (hs.2.trans hpm)
  calc 2 * cdf μ s = (1 / d.ρ m) * (2 * d.ρ m * cdf μ s) := by
        field_simp
    _ ≤ (1 / d.ρ m) * d.ρ s := mul_le_mul_of_nonneg_left h (by positivity)

/-- Left of the median: `∫_x^m (f - f m)² ρ ≤ (1 / ρ m)² ∫_x^m (f')² ρ` for `x` in the interior
of the support. -/
theorem integral_sq_sub_mul_le_left {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {x : ℝ}
    (hx : x ∈ interior (μ : Measure ℝ).support) (hxm : x ≤ m) :
    ∫ s in x..m, (f s - f m) ^ 2 * d.ρ s ≤
      (1 / d.ρ m) ^ 2 * ∫ s in x..m, deriv f s ^ 2 * d.ρ s :=
  d.integral_sq_sub_mul_le_left_of_le hμ hi hm hf (median_mem hμ hi hm) le_rfl hx hxm

end Interval

section HalfLine

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
  {m : ℝ} (hm : cdf μ m = 1 / 2)
include hμ hi hm

omit hμ hi hm in
/-- A set integral of a nonnegative integrable function, read through the auxiliary density
measure. -/
theorem withDensity_apply_eq_ofReal {g : ℝ → ℝ} (hg : Integrable g (μ : Measure ℝ))
    (hg0 : ∀ x, 0 ≤ g x) {S : Set ℝ} (hS : MeasurableSet S) :
    ((μ : Measure ℝ).withDensity fun x ↦ ENNReal.ofReal (g x)) S =
      ENNReal.ofReal (∫ x in S, g x ∂(μ : Measure ℝ)) := by
  rw [withDensity_apply _ hS,
    ofReal_integral_eq_lintegral_ofReal hg.integrableOn (ae_of_all _ fun x ↦ hg0 x)]

omit hm in
/-- The auxiliary density measure gives no mass off the interior of the support. -/
theorem withDensity_compl_interior_support (g : ℝ → ENNReal) :
    ((μ : Measure ℝ).withDensity g) (interior (μ : Measure ℝ).support)ᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ (hμ.measure_compl_interior_support hi)

/-- Right half-line Hardy bound for admissible tests, anchored at any interior point `p ≥ m`
with the median constant. -/
theorem setIntegral_Ioi_sq_sub_le_of_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) {p : ℝ}
    (hpΩ : p ∈ interior (μ : Measure ℝ).support) (hmp : m ≤ p) :
    ∫ s in Ioi p, (f s - f p) ^ 2 ∂(μ : Measure ℝ) ≤
      (1 / d.ρ m) ^ 2 * ∫ s in Ioi p, deriv f s ^ 2 ∂(μ : Measure ℝ) := by
  classical
  have hf1 : ContDiff ℝ 1 f := hf.smooth'.of_le (by exact_mod_cast le_top)
  have hg2 : Integrable (fun s ↦ (f s - f p) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub (memLp_const (f p))).integrable_sq
  have hf'2 : Integrable (fun s ↦ deriv f s ^ 2) (μ : Measure ℝ) :=
    hf.energy_integrable.congr (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  set K := (1 / d.ρ m) ^ 2 * ∫ s in Ioi p, deriv f s ^ 2 ∂(μ : Measure ℝ) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun s ↦ sq_nonneg _)
  have hstep :
    ∀ q : ℝ,
      q ∈ interior (μ : Measure ℝ).support →
        p < q → ∫ s in Ioc p q, (f s - f p) ^ 2 ∂(μ : Measure ℝ) ≤ K := by
    intro q hq hpq
    rw [d.setIntegral_eq_integral_mul _ measurableSet_Ioc, ←
      intervalIntegral.integral_of_le hpq.le]
    refine (d.integral_sq_sub_mul_le_right_of_le hμ hi hm hf1 hpΩ hmp hq hpq.le).trans ?_
    rw [hK]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [intervalIntegral.integral_of_le hpq.le, ←
      d.setIntegral_eq_integral_mul _ measurableSet_Ioc]
    exact
      setIntegral_mono_set hf'2.integrableOn (ae_of_all _ fun s ↦ sq_nonneg _)
        (ae_of_all _ Ioc_subset_Ioi_self)
  set ν : Measure ℝ := (μ : Measure ℝ).withDensity fun s ↦ ENNReal.ofReal ((f s - f p) ^ 2) with
    hν
  have hνS :
    ∀ S : Set ℝ,
      MeasurableSet S → ν S = ENNReal.ofReal (∫ s in S, (f s - f p) ^ 2 ∂(μ : Measure ℝ)) :=
    fun S hS ↦ withDensity_apply_eq_ofReal hg2 (fun s ↦ sq_nonneg _) hS
  set S : ℚ → Set ℝ := fun q ↦
    if (q : ℝ) ∈ interior (μ : Measure ℝ).support ∧ p < q then Ioc p q else ∅ with hS
  have hSle : ∀ q, ν (S q) ≤ ENNReal.ofReal K := by
    intro q
    by_cases hq : (q : ℝ) ∈ interior (μ : Measure ℝ).support ∧ p < q
    · simp only [hS, ite_eq_left hq]
      rw [hνS _ measurableSet_Ioc]
      exact ENNReal.ofReal_le_ofReal (hstep q hq.1 hq.2)
    · simp [hS, ite_eq_right hq]
  have hdir : Directed (· ⊆ ·) S := by
    intro i j
    by_cases hi' : (i : ℝ) ∈ interior (μ : Measure ℝ).support ∧ p < i
    · by_cases hj' : (j : ℝ) ∈ interior (μ : Measure ℝ).support ∧ p < j
      · have hmax :
          ((max i j : ℚ) : ℝ) ∈ interior (μ : Measure ℝ).support ∧ p < ((max i j : ℚ) : ℝ) := by
          rcases le_total i j with h | h
          · rw [max_eq_right h]
            exact hj'
          · rw [max_eq_left h]
            exact hi'
        refine ⟨max i j, ?_, ?_⟩
        · simp only [hS, ite_eq_left hi', ite_eq_left hmax]
          exact Ioc_subset_Ioc_right (by exact_mod_cast le_max_left i j)
        · simp only [hS, ite_eq_left hj', ite_eq_left hmax]
          exact Ioc_subset_Ioc_right (by exact_mod_cast le_max_right i j)
      · exact ⟨i, subset_rfl, by simp [hS, ite_eq_right hj']⟩
    · exact ⟨j, by simp [hS, ite_eq_right hi'], subset_rfl⟩
  have hcover : Ioi p ∩ interior (μ : Measure ℝ).support ⊆ ⋃ q, S q := by
    rintro y ⟨hyp, hyΩ⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hyΩ
    obtain ⟨q, hyq, hqε⟩ := exists_rat_btwn (show y < y + ε by linarith)
    have hqΩ : (q : ℝ) ∈ interior (μ : Measure ℝ).support := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hpy : p < y := hyp
    refine mem_iUnion.mpr ⟨q, ?_⟩
    have hSq : S q = Ioc p q := by
      simp only [hS]
      exact ite_eq_left (And.intro hqΩ (hpy.trans hyq))
    rw [hSq]
    exact ⟨hpy, hyq.le⟩
  have hν_le : ν (Ioi p) ≤ ENNReal.ofReal K := by
    calc
      ν (Ioi p) ≤ ν ((⋃ q, S q) ∪ (interior (μ : Measure ℝ).support)ᶜ) := by
        apply measure_mono
        intro y hy
        by_cases hyΩ : y ∈ interior (μ : Measure ℝ).support
        · exact Or.inl (hcover (mem_inter hy hyΩ))
        · exact Or.inr hyΩ
      _ ≤ ν (⋃ q, S q) + ν (interior (μ : Measure ℝ).support)ᶜ := measure_union_le _ _
      _ = ⨆ q, ν (S q) := by
        rw [withDensity_compl_interior_support hμ hi _, add_zero, hdir.measure_iUnion]
      _ ≤ ENNReal.ofReal K := iSup_le hSle
  rw [hνS _ measurableSet_Ioi] at hν_le
  exact (ENNReal.ofReal_le_ofReal_iff hK0).mp hν_le

/-- Right half-line Hardy bound for admissible tests. -/
theorem setIntegral_Ioi_sq_sub_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) :
    ∫ s in Ioi m, (f s - f m) ^ 2 ∂(μ : Measure ℝ) ≤
      (1 / d.ρ m) ^ 2 * ∫ s in Ioi m, deriv f s ^ 2 ∂(μ : Measure ℝ) :=
  d.setIntegral_Ioi_sq_sub_le_of_le hμ hi hm hf (median_mem hμ hi hm) le_rfl

/-- Left half-line Hardy bound for admissible tests, anchored at any interior point `p ≤ m`
with the median constant. -/
theorem setIntegral_Iic_sq_sub_le_of_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) {p : ℝ}
    (hpΩ : p ∈ interior (μ : Measure ℝ).support) (hpm : p ≤ m) :
    ∫ s in Iic p, (f s - f p) ^ 2 ∂(μ : Measure ℝ) ≤
      (1 / d.ρ m) ^ 2 * ∫ s in Iic p, deriv f s ^ 2 ∂(μ : Measure ℝ) := by
  classical
  have hf1 : ContDiff ℝ 1 f := hf.smooth'.of_le (by exact_mod_cast le_top)
  have hg2 : Integrable (fun s ↦ (f s - f p) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub (memLp_const (f p))).integrable_sq
  have hf'2 : Integrable (fun s ↦ deriv f s ^ 2) (μ : Measure ℝ) :=
    hf.energy_integrable.congr (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  set K := (1 / d.ρ m) ^ 2 * ∫ s in Iic p, deriv f s ^ 2 ∂(μ : Measure ℝ) with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun s ↦ sq_nonneg _)
  have hstep :
    ∀ q : ℝ,
      q ∈ interior (μ : Measure ℝ).support →
        q < p → ∫ s in Ioc q p, (f s - f p) ^ 2 ∂(μ : Measure ℝ) ≤ K := by
    intro q hq hqp
    rw [d.setIntegral_eq_integral_mul _ measurableSet_Ioc, ←
      intervalIntegral.integral_of_le hqp.le]
    refine (d.integral_sq_sub_mul_le_left_of_le hμ hi hm hf1 hpΩ hpm hq hqp.le).trans ?_
    rw [hK]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [intervalIntegral.integral_of_le hqp.le, ←
      d.setIntegral_eq_integral_mul _ measurableSet_Ioc]
    exact
      setIntegral_mono_set hf'2.integrableOn (ae_of_all _ fun s ↦ sq_nonneg _)
        (ae_of_all _ fun s hs ↦ hs.2)
  set ν : Measure ℝ := (μ : Measure ℝ).withDensity fun s ↦ ENNReal.ofReal ((f s - f p) ^ 2) with
    hν
  have hνS :
    ∀ S : Set ℝ,
      MeasurableSet S → ν S = ENNReal.ofReal (∫ s in S, (f s - f p) ^ 2 ∂(μ : Measure ℝ)) :=
    fun S hS ↦ withDensity_apply_eq_ofReal hg2 (fun s ↦ sq_nonneg _) hS
  set S : ℚ → Set ℝ := fun q ↦
    if (q : ℝ) ∈ interior (μ : Measure ℝ).support ∧ (q : ℝ) < p then Ioc q p else ∅ with hS
  have hSle : ∀ q, ν (S q) ≤ ENNReal.ofReal K := by
    intro q
    by_cases hq : (q : ℝ) ∈ interior (μ : Measure ℝ).support ∧ (q : ℝ) < p
    · simp only [hS, ite_eq_left hq]
      rw [hνS _ measurableSet_Ioc]
      exact ENNReal.ofReal_le_ofReal (hstep q hq.1 hq.2)
    · simp [hS, ite_eq_right hq]
  have hdir : Directed (· ⊆ ·) S := by
    intro i j
    by_cases hi' : (i : ℝ) ∈ interior (μ : Measure ℝ).support ∧ (i : ℝ) < p
    · by_cases hj' : (j : ℝ) ∈ interior (μ : Measure ℝ).support ∧ (j : ℝ) < p
      · have hmin :
          ((min i j : ℚ) : ℝ) ∈ interior (μ : Measure ℝ).support ∧ ((min i j : ℚ) : ℝ) < p := by
          rcases le_total i j with h | h
          · rw [min_eq_left h]
            exact hi'
          · rw [min_eq_right h]
            exact hj'
        refine ⟨min i j, ?_, ?_⟩
        · simp only [hS, ite_eq_left hi', ite_eq_left hmin]
          exact Ioc_subset_Ioc_left (by exact_mod_cast min_le_left i j)
        · simp only [hS, ite_eq_left hj', ite_eq_left hmin]
          exact Ioc_subset_Ioc_left (by exact_mod_cast min_le_right i j)
      · exact ⟨i, subset_rfl, by simp [hS, ite_eq_right hj']⟩
    · exact ⟨j, by simp [hS, ite_eq_right hi'], subset_rfl⟩
  have hcover : Iic p ∩ interior (μ : Measure ℝ).support ⊆ ⋃ q, S q := by
    rintro y ⟨hyp, hyΩ⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hyΩ
    obtain ⟨q, hqy, hyq⟩ := exists_rat_btwn (show y - ε < y by linarith)
    have hqΩ : (q : ℝ) ∈ interior (μ : Measure ℝ).support := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hyp' : y ≤ p := hyp
    refine mem_iUnion.mpr ⟨q, ?_⟩
    have hSq : S q = Ioc (q : ℝ) p := by
      simp only [hS]
      exact ite_eq_left (And.intro hqΩ (hyq.trans_le hyp'))
    rw [hSq]
    exact ⟨hyq, hyp'⟩
  have hν_le : ν (Iic p) ≤ ENNReal.ofReal K := by
    calc
      ν (Iic p) ≤ ν ((⋃ q, S q) ∪ (interior (μ : Measure ℝ).support)ᶜ) := by
        apply measure_mono
        intro y hy
        by_cases hyΩ : y ∈ interior (μ : Measure ℝ).support
        · exact Or.inl (hcover (mem_inter hy hyΩ))
        · exact Or.inr hyΩ
      _ ≤ ν (⋃ q, S q) + ν (interior (μ : Measure ℝ).support)ᶜ := measure_union_le _ _
      _ = ⨆ q, ν (S q) := by
        rw [withDensity_compl_interior_support hμ hi _, add_zero, hdir.measure_iUnion]
      _ ≤ ENNReal.ofReal K := iSup_le hSle
  rw [hνS _ measurableSet_Iic] at hν_le
  exact (ENNReal.ofReal_le_ofReal_iff hK0).mp hν_le

/-- Left half-line Hardy bound for admissible tests. -/
theorem setIntegral_Iic_sq_sub_le {f : ℝ → ℝ}
    (hf : Poincare.SmoothTest.Admissible (μ : Measure ℝ) f) :
    ∫ s in Iic m, (f s - f m) ^ 2 ∂(μ : Measure ℝ) ≤
      (1 / d.ρ m) ^ 2 * ∫ s in Iic m, deriv f s ^ 2 ∂(μ : Measure ℝ) :=
  d.setIntegral_Iic_sq_sub_le_of_le hμ hi hm hf (median_mem hμ hi hm) le_rfl

/-- The smooth-test Poincaré inequality with constant `(1 / ρ m)²` at a median `m`. -/
theorem smoothTest_holds : Poincare.SmoothTest.Holds (μ : Measure ℝ) ((1 / d.ρ m) ^ 2) := by
  refine ⟨inferInstance, by positivity, fun f hf ↦ ?_⟩
  have hg2 : Integrable (fun s ↦ (f s - f m) ^ 2) (μ : Measure ℝ) :=
    (hf.memLp_two.sub (memLp_const (f m))).integrable_sq
  have hf'2 : Integrable (fun s ↦ deriv f s ^ 2) (μ : Measure ℝ) :=
    hf.energy_integrable.congr (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  have henergy :
    Poincare.SmoothTest.energy (μ : Measure ℝ) f = ∫ s, deriv f s ^ 2 ∂(μ : Measure ℝ) := by
    unfold Poincare.SmoothTest.energy
    exact integral_congr_ae (ae_of_all _ fun s ↦ norm_gradient_sq_eq_deriv_sq f s)
  calc
    ProbabilityTheory.variance f (μ : Measure ℝ) ≤ ∫ s, (f s - f m) ^ 2 ∂(μ : Measure ℝ) :=
      hf.variance_le_integral_sq_sub (f m)
    _ =
        ∫ s in Ioi m, (f s - f m) ^ 2 ∂(μ : Measure ℝ) +
          ∫ s in Iic m, (f s - f m) ^ 2 ∂(μ : Measure ℝ) := by
      rw [← compl_Ioi, integral_add_compl measurableSet_Ioi hg2]
    _ ≤
        (1 / d.ρ m) ^ 2 * ∫ s in Ioi m, deriv f s ^ 2 ∂(μ : Measure ℝ) +
          (1 / d.ρ m) ^ 2 * ∫ s in Iic m, deriv f s ^ 2 ∂(μ : Measure ℝ) :=
      add_le_add (d.setIntegral_Ioi_sq_sub_le hμ hi hm hf)
        (d.setIntegral_Iic_sq_sub_le hμ hi hm hf)
    _ = (1 / d.ρ m) ^ 2 * Poincare.SmoothTest.energy (μ : Measure ℝ) f := by
      rw [← mul_add, ← compl_Ioi, integral_add_compl measurableSet_Ioi hf'2, henergy]

end HalfLine

end FunctionalInequalities.KLS.LineDensity
