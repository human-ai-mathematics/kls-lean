import FunctionalInequalities.KLS.LogConcave.Line.Hazard
import FunctionalInequalities.KLS.LogConcave.Translation

/-!
# The variance of a log-concave law on the line dominates `1 / (12 ρ(m)²)`

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, variance step (compare Bobkov 1999,
Proposition 4.1: `ρ(m)² · Var ≥ 1/12` for log-concave laws with median `m`). Read
`LineDensity.quadratic_bound_le_sub` and `LineDensity.one_div_le_variance`.

With `F` the distribution function, `c = ρ m > 0` at a median `m`, and `k` a supporting slope of
`log ρ` at `m`, the supporting-line bound `ρ ≤ c + k (F - 1/2)` gives the pointwise comparison
`φ(F x) ≤ x - m` for `x ≥ m` and `φ(F x) ≥ x - m` for `x ≤ m`, where
`φ(u) = (u - 1/2) / c - k (u - 1/2)² / (2 c²)`. Since `F(X)` is uniform on `[0, 1]`,
`∫ (x - m)(F x - 1/2) dμ ≥ ∫₀¹ φ(u)(u - 1/2) du = 1 / (12 c)`. The elementary inequality
`a b ≤ c a² / 2 + b² / (2 c)` with `∫ (F - 1/2)² dμ = 1/12` then yields `Var μ ≥ 1 / (12 c²)`.

The bound is sharp for uniform laws. No Poincaré inequality is asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities.KLS.LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

/-- The elementary derivative bound behind the comparison function: if `0 ≤ r ≤ c + k δ`, then
`r (c - k δ) ≤ c²`. -/
theorem mul_sub_le_sq {c k r δ : ℝ} (hr : 0 ≤ r) (hrL : r ≤ c + k * δ) :
    r * (c - k * δ) ≤ c ^ 2 := by
  rcases le_or_gt (c - k * δ) 0 with h | h
  · nlinarith [mul_nonpos_iff.mpr (Or.inl ⟨hr, h⟩)]
  · nlinarith [mul_le_mul_of_nonneg_right hrL h.le, sq_nonneg (k * δ)]

section Comparison

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
  {m : ℝ} (hm : cdf μ m = 1 / 2) {k : ℝ}
  (hk : ∀ s ∈ interior (μ : Measure ℝ).support, d.ρ s ≤ d.ρ m * Real.exp (k * (s - m)))
include hμ hi hm hk

omit hμ hi hm hk in
/-- The derivative of the comparison function `φ(F x) - (x - m)` on the interior of the
support. -/
theorem hasDerivAt_comparison {s : ℝ} (hs : s ∈ interior (μ : Measure ℝ).support) :
    HasDerivAt (fun x ↦ (cdf μ x - 1 / 2) / d.ρ m -
        k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2)) - (x - m))
      (d.ρ s / d.ρ m - k / (2 * d.ρ m ^ 2) *
        (d.ρ s * (cdf μ s - 1 / 2) + (cdf μ s - 1 / 2) * d.ρ s) - 1) s := by
  have h1 : HasDerivAt (fun x ↦ cdf μ x - 1 / 2) (d.ρ s) s := (d.hasDerivAt_cdf hs).sub_const _
  have h2 := h1.div_const (d.ρ m)
  have h3 := (h1.mul h1).const_mul (k / (2 * d.ρ m ^ 2))
  have h4 := (h2.sub h3).sub ((hasDerivAt_id s).sub_const m)
  exact h4

/-- The derivative of the comparison function is nonpositive on the interior of the support. -/
theorem comparison_deriv_nonpos {s : ℝ} (hs : s ∈ interior (μ : Measure ℝ).support) :
    d.ρ s / d.ρ m - k / (2 * d.ρ m ^ 2) *
      (d.ρ s * (cdf μ s - 1 / 2) + (cdf μ s - 1 / 2) * d.ρ s) - 1 ≤ 0 := by
  have hc : 0 < d.ρ m := d.pos (median_mem hμ hi hm)
  have hc' : d.ρ m ≠ 0 := hc.ne'
  have hL := d.le_add_mul_cdf_sub hμ hi hm hk hs
  have hkey := mul_sub_le_sq (d.nonneg s) hL
  have heq : d.ρ s / d.ρ m - k / (2 * d.ρ m ^ 2) *
      (d.ρ s * (cdf μ s - 1 / 2) + (cdf μ s - 1 / 2) * d.ρ s) - 1 =
      (d.ρ s * (d.ρ m - k * (cdf μ s - 1 / 2)) - d.ρ m ^ 2) / d.ρ m ^ 2 := by
    field_simp
    ring
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)

omit hμ hi hm hk in
/-- Continuity of the comparison derivative on subintervals of the interior of the support. -/
theorem continuousOn_comparison_deriv {a b : ℝ} (hab : Icc a b ⊆ interior (μ : Measure ℝ).support) :
    ContinuousOn (fun s ↦ d.ρ s / d.ρ m - k / (2 * d.ρ m ^ 2) *
      (d.ρ s * (cdf μ s - 1 / 2) + (cdf μ s - 1 / 2) * d.ρ s) - 1) (Icc a b) := by
  have hρ : ContinuousOn d.ρ (Icc a b) := d.continuousOn.mono hab
  have hF : ContinuousOn (fun s ↦ cdf μ s - 1 / 2) (Icc a b) :=
    (d.continuous_cdf.sub continuous_const).continuousOn
  exact ((hρ.div_const _).sub (continuousOn_const.mul ((hρ.mul hF).add (hF.mul hρ)))).sub
    continuousOn_const

/-- Pointwise comparison: `φ(F x) (F x - 1/2) ≤ (x - m) (F x - 1/2)` on the interior of the
support. -/
theorem quadratic_bound_le_sub {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    ((cdf μ x - 1 / 2) / d.ρ m -
        k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2))) * (cdf μ x - 1 / 2) ≤
      (x - m) * (cdf μ x - 1 / 2) := by
  have hmΩ := median_mem hμ hi hm
  set Ψ : ℝ → ℝ := fun x ↦ (cdf μ x - 1 / 2) / d.ρ m -
    k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2)) - (x - m) with hΨ
  set Ψ' : ℝ → ℝ := fun s ↦ d.ρ s / d.ρ m - k / (2 * d.ρ m ^ 2) *
    (d.ρ s * (cdf μ s - 1 / 2) + (cdf μ s - 1 / 2) * d.ρ s) - 1 with hΨ'
  have hΨm : Ψ m = 0 := by
    simp [hΨ, hm]
  rcases le_total m x with hmx | hxm
  · have hIcc : Icc m x ⊆ interior (μ : Measure ℝ).support :=
      hμ.convex_interior_support.ordConnected.out hmΩ hx
    have hftc : ∫ s in m..x, Ψ' s = Ψ x - Ψ m := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦ ?_) ?_
      · exact d.hasDerivAt_comparison (hIcc ((uIcc_of_le hmx) ▸ hs))
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hmx]
        exact d.continuousOn_comparison_deriv hIcc
    have hneg : ∫ s in m..x, Ψ' s ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) hmx fun s hs ↦
        neg_nonneg.mpr (d.comparison_deriv_nonpos hμ hi hm hk (hIcc hs))
      rw [intervalIntegral.integral_neg] at this
      linarith
    have hΨx : Ψ x ≤ 0 := by linarith
    have hφ : (cdf μ x - 1 / 2) / d.ρ m -
        k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2)) ≤ x - m := by
      have : Ψ x = (cdf μ x - 1 / 2) / d.ρ m -
          k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2)) - (x - m) := rfl
      linarith
    exact mul_le_mul_of_nonneg_right hφ (by linarith [half_le_cdf_of_le hm hmx])
  · have hIcc : Icc x m ⊆ interior (μ : Measure ℝ).support :=
      hμ.convex_interior_support.ordConnected.out hx hmΩ
    have hftc : ∫ s in x..m, Ψ' s = Ψ m - Ψ x := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦ ?_) ?_
      · exact d.hasDerivAt_comparison (hIcc ((uIcc_of_le hxm) ▸ hs))
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hxm]
        exact d.continuousOn_comparison_deriv hIcc
    have hneg : ∫ s in x..m, Ψ' s ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) hxm fun s hs ↦
        neg_nonneg.mpr (d.comparison_deriv_nonpos hμ hi hm hk (hIcc hs))
      rw [intervalIntegral.integral_neg] at this
      linarith
    have hΨx : 0 ≤ Ψ x := by linarith
    have hφ : x - m ≤ (cdf μ x - 1 / 2) / d.ρ m -
        k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2)) := by
      have : Ψ x = (cdf μ x - 1 / 2) / d.ρ m -
          k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2)) - (x - m) := rfl
      linarith
    exact mul_le_mul_of_nonpos_right hφ (by linarith [cdf_le_half_of_le hm hxm])

/-- The centered covariance of the coordinate with its distribution function is at least
`1 / (12 ρ(m))`. -/
theorem one_div_le_integral_mul :
    1 / (12 * d.ρ m) ≤ ∫ x, (x - m) * (cdf μ x - 1 / 2) ∂(μ : Measure ℝ) := by
  have hc : 0 < d.ρ m := d.pos (median_mem hμ hi hm)
  have hc' : d.ρ m ≠ 0 := hc.ne'
  have hint : ∀ p : ℝ → ℝ, Continuous p → Integrable (fun x ↦ p (cdf μ x)) (μ : Measure ℝ) :=
    fun p hp ↦ Probability.Line.integrable_comp_cdf μ d.withDensity_eq d.measurable d.nonneg hp
  have hsq := Probability.Line.integral_cdf_sub_half_sq μ d.withDensity_eq d.measurable d.nonneg
  have hcube := Probability.Line.integral_cdf_sub_half_cube μ d.withDensity_eq d.measurable d.nonneg
  have hlhs : ∫ x, ((cdf μ x - 1 / 2) / d.ρ m -
      k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2))) * (cdf μ x - 1 / 2)
        ∂(μ : Measure ℝ) = 1 / (12 * d.ρ m) := by
    have heq : ∀ x, ((cdf μ x - 1 / 2) / d.ρ m -
        k / (2 * d.ρ m ^ 2) * ((cdf μ x - 1 / 2) * (cdf μ x - 1 / 2))) * (cdf μ x - 1 / 2) =
        (1 / d.ρ m) * (cdf μ x - 1 / 2) ^ 2 - (k / (2 * d.ρ m ^ 2)) * (cdf μ x - 1 / 2) ^ 3 := by
      intro x
      ring
    simp_rw [heq]
    rw [integral_sub ((hint (fun u ↦ (1 / d.ρ m) * (u - 1 / 2) ^ 2) (by fun_prop)))
      ((hint (fun u ↦ (k / (2 * d.ρ m ^ 2)) * (u - 1 / 2) ^ 3) (by fun_prop))),
      integral_const_mul, integral_const_mul, hsq, hcube]
    rw [mul_zero, sub_zero, one_div_mul_one_div, mul_comm]
  rw [← hlhs]
  refine integral_mono_ae (hint (fun u ↦ ((u - 1 / 2) / d.ρ m -
      k / (2 * d.ρ m ^ 2) * ((u - 1 / 2) * (u - 1 / 2))) * (u - 1 / 2)) (by fun_prop)) ?_ ?_
  · have hid : Integrable (fun x : ℝ ↦ x - m) (μ : Measure ℝ) :=
      hμ.integrable_id.sub (integrable_const m)
    have hFb : ∀ x, ‖cdf μ x - 1 / 2‖ ≤ 1 / 2 := fun x ↦ by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Probability.Line.cdf_nonneg μ x, Probability.Line.cdf_le_one μ x]
    have hb := hid.bdd_mul (c := 1 / 2)
      (d.continuous_cdf.sub continuous_const).aestronglyMeasurable (ae_of_all _ hFb)
    exact hb.congr (ae_of_all _ fun x ↦ mul_comm _ _)
  · have h0 : (μ : Measure ℝ) (interior (μ : Measure ℝ).support)ᶜ = 0 :=
      hμ.measure_compl_interior_support hi
    rw [EventuallyLE]
    filter_upwards [(ae_iff.mpr h0 : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ interior (μ : Measure ℝ).support)]
      with x hx
    exact d.quadratic_bound_le_sub hμ hi hm hk hx

/-- Bobkov's variance bound: `1 / (12 ρ(m)²) ≤ Var μ` at a median `m`. -/
theorem one_div_le_variance : 1 / (12 * d.ρ m ^ 2) ≤ variance id (μ : Measure ℝ) := by
  have hc : 0 < d.ρ m := d.pos (median_mem hμ hi hm)
  have hc' : d.ρ m ≠ 0 := hc.ne'
  have hint : ∀ p : ℝ → ℝ, Continuous p → Integrable (fun x ↦ p (cdf μ x)) (μ : Measure ℝ) :=
    fun p hp ↦ Probability.Line.integrable_comp_cdf μ d.withDensity_eq d.measurable d.nonneg hp
  have hsq := Probability.Line.integral_cdf_sub_half_sq μ d.withDensity_eq d.measurable d.nonneg
  have hF := Probability.Line.integral_cdf μ d.withDensity_eq d.measurable d.nonneg
  have hcov := d.one_div_le_integral_mul hμ hi hm hk
  set E : ℝ := ∫ x, id x ∂(μ : Measure ℝ) with hE
  have hid : Integrable id (μ : Measure ℝ) := hμ.integrable_id
  have hidE : Integrable (fun x : ℝ ↦ x - E) (μ : Measure ℝ) := hid.sub (integrable_const E)
  have hidm : Integrable (fun x : ℝ ↦ x - m) (μ : Measure ℝ) := hid.sub (integrable_const m)
  have hFb : ∀ x, ‖cdf μ x - 1 / 2‖ ≤ 1 / 2 := fun x ↦ by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Probability.Line.cdf_nonneg μ x, Probability.Line.cdf_le_one μ x]
  have hFmeas : AEStronglyMeasurable (fun x ↦ cdf μ x - 1 / 2) (μ : Measure ℝ) :=
    (d.continuous_cdf.sub continuous_const).aestronglyMeasurable
  have hprodE : Integrable (fun x ↦ (x - E) * (cdf μ x - 1 / 2)) (μ : Measure ℝ) :=
    (hidE.bdd_mul hFmeas (ae_of_all _ hFb)).congr (ae_of_all _ fun x ↦ mul_comm _ _)
  have hprodm : Integrable (fun x ↦ (x - m) * (cdf μ x - 1 / 2)) (μ : Measure ℝ) :=
    (hidm.bdd_mul hFmeas (ae_of_all _ hFb)).congr (ae_of_all _ fun x ↦ mul_comm _ _)
  have hFint : Integrable (fun x ↦ cdf μ x - 1 / 2) (μ : Measure ℝ) :=
    hint (fun u ↦ u - 1 / 2) (by fun_prop)
  -- centering does not change the covariance
  have hFint' : Integrable (cdf μ) (μ : Measure ℝ) := hint (fun u ↦ u) continuous_id
  have hFzero : ∫ x, (cdf μ x - 1 / 2) ∂(μ : Measure ℝ) = 0 := by
    rw [integral_sub hFint' (integrable_const _), integral_const]
    simp [hF]
  have hcenter : ∫ x, (x - E) * (cdf μ x - 1 / 2) ∂(μ : Measure ℝ) =
      ∫ x, (x - m) * (cdf μ x - 1 / 2) ∂(μ : Measure ℝ) := by
    have heq : ∀ x, (x - E) * (cdf μ x - 1 / 2) =
        (x - m) * (cdf μ x - 1 / 2) + (m - E) * (cdf μ x - 1 / 2) := fun x ↦ by ring
    simp_rw [heq]
    rw [integral_add hprodm (hFint.const_mul _), integral_const_mul, hFzero, mul_zero, add_zero]
  -- the elementary inequality `a b ≤ c a² / 2 + b² / (2 c)`
  have hsq2 : Integrable (fun x ↦ (x - E) ^ 2) (μ : Measure ℝ) :=
    (hμ.memLp_id_two.sub (memLp_const E)).integrable_sq
  have hF2 : Integrable (fun x ↦ (cdf μ x - 1 / 2) ^ 2) (μ : Measure ℝ) :=
    hint (fun u ↦ (u - 1 / 2) ^ 2) (by fun_prop)
  have hpt : ∀ x, (x - E) * (cdf μ x - 1 / 2) ≤
      d.ρ m / 2 * (x - E) ^ 2 + 1 / (2 * d.ρ m) * (cdf μ x - 1 / 2) ^ 2 := by
    intro x
    have h1 : 0 ≤ (d.ρ m * (x - E) - (cdf μ x - 1 / 2)) ^ 2 := sq_nonneg _
    have h2 : d.ρ m / 2 * (x - E) ^ 2 + 1 / (2 * d.ρ m) * (cdf μ x - 1 / 2) ^ 2 -
        (x - E) * (cdf μ x - 1 / 2) =
        (d.ρ m * (x - E) - (cdf μ x - 1 / 2)) ^ 2 / (2 * d.ρ m) := by
      field_simp
      ring
    have h3 : 0 ≤ (d.ρ m * (x - E) - (cdf μ x - 1 / 2)) ^ 2 / (2 * d.ρ m) :=
      div_nonneg h1 (by positivity)
    linarith
  have hsum : Integrable (fun x ↦ d.ρ m / 2 * (x - E) ^ 2 + 1 / (2 * d.ρ m) * (cdf μ x - 1 / 2) ^ 2)
      (μ : Measure ℝ) := (hsq2.const_mul _).add (hF2.const_mul _)
  have hmono := integral_mono hprodE hsum hpt
  rw [integral_add (hsq2.const_mul _) (hF2.const_mul _), integral_const_mul, integral_const_mul,
    hsq, hcenter] at hmono
  have hvar : variance id (μ : Measure ℝ) = ∫ x, (x - E) ^ 2 ∂(μ : Measure ℝ) := by
    rw [variance_eq_integral aemeasurable_id]
    rfl
  rw [hvar]
  set V := ∫ x, (x - E) ^ 2 ∂(μ : Measure ℝ) with hV
  have hV0 : 0 ≤ V := integral_nonneg fun x ↦ sq_nonneg _
  have hchain : 1 / (12 * d.ρ m) ≤ d.ρ m / 2 * V + 1 / (2 * d.ρ m) * (1 / 12) := hcov.trans hmono
  rw [div_le_iff₀ (by positivity)]
  have e1 : 24 * d.ρ m * (1 / (12 * d.ρ m)) = 2 := by
    field_simp
    ring
  have e2 : 24 * d.ρ m * (d.ρ m / 2 * V + 1 / (2 * d.ρ m) * (1 / 12)) =
      12 * d.ρ m ^ 2 * V + 1 := by
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left hchain (by positivity : (0 : ℝ) ≤ 24 * d.ρ m)
  rw [e1, e2] at this
  linarith

end Comparison

end FunctionalInequalities.KLS.LineDensity
