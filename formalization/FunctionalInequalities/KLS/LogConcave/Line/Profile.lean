import FunctionalInequalities.KLS.LogConcave.Line.Hazard
import FunctionalInequalities.KLS.LogConcave.Translation
import FunctionalInequalities.Probability.Line.AffineProfile

/-!
# The quantile-density profile of a log-concave law dominates `F (1 - F) / σ`

Source: Blueprint `thm:one-dimensional-logconcave-poincare` (sharp form with constant `4`); the
argument follows Section 5 of the collaborator's constant-4 source audit (a locally kept record). Read
`LogConcave.mean_mem_interior_support`, `LineDensity.variance_ge_of_affine_bound` and
`LineDensity.cdf_mul_one_sub_cdf_le_sd_mul`.

For a log-concave law `μ` on the line with Borell density `ρ`, distribution function `F` and
standard deviation `σ`, every point `x` of the interior `Ω` of the support satisfies
`F x (1 - F x) ≤ σ · ρ x`. The supporting exponential of `ρ` at `x` gives an affine majorant
`ρ ≤ A (1 - F) + B F` with `A, B ≥ 0`; comparing the law with the affine quantile model through the
`1`-Lipschitz map `Ψ = q ∘ F` (whose law is the uniform law pushed through `q`) gives
`σ² ≥ 1 / (√A + √B)⁴`, and `A (1 - F x) + B F x ≥ (√A + √B)² F x (1 - F x)` closes the estimate.

Nothing here is a Poincaré inequality; the bound feeds the sharp Hardy module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf affineWeight affineQuantile unitUniform)

namespace FunctionalInequalities.KLS

namespace LogConcave

variable {μ : ProbabilityMeasure ℝ}

/-- The mean of a log-concave law with interior support lies in the interior of the support. -/
theorem mean_mem_interior_support (hμ : LogConcave μ)
    (hi : (interior (μ : Measure ℝ).support).Nonempty) :
    (∫ x, id x ∂(μ : Measure ℝ)) ∈ interior (μ : Measure ℝ).support := by
  obtain ⟨d⟩ := hμ.exists_lineDensity hi
  set E := ∫ x, id x ∂(μ : Measure ℝ) with hE
  have hid : Integrable (fun x : ℝ ↦ x) (μ : Measure ℝ) := hμ.integrable_id
  have hsingle : (μ : Measure ℝ) {E} = 0 :=
    Probability.Line.measure_singleton_eq_zero μ d.withDensity_eq E
  have hEint : ∫ x, x ∂(μ : Measure ℝ) = E := rfl
  apply hμ.mem_interior_support_of_cdf hi
  · by_contra h0
    push Not at h0
    have hle : cdf μ E = 0 := le_antisymm h0 (Probability.Line.cdf_nonneg μ E)
    have hzero : (μ : Measure ℝ) (Iic E) = 0 := by
      unfold cdf at hle
      rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at hle
    have hae : ∀ᵐ x ∂(μ : Measure ℝ), E < x := by
      have hset : {a : ℝ | ¬ E < a} = Iic E := by ext; simp
      rw [ae_iff, hset]
      exact hzero
    have hint : Integrable (fun x : ℝ ↦ x - E) (μ : Measure ℝ) := hid.sub (integrable_const E)
    have hpos : 0 < ∫ x, (x - E) ∂(μ : Measure ℝ) := by
      rw [integral_pos_iff_support_of_nonneg_ae (hae.mono fun x hx ↦ (sub_pos.mpr hx).le) hint]
      have hs : Function.support (fun x : ℝ ↦ x - E) = {E}ᶜ := by
        ext x
        simp [sub_eq_zero]
      rw [hs, measure_compl (measurableSet_singleton E) (measure_ne_top _ _), hsingle]
      simp
    rw [integral_sub hid (integrable_const E), hEint, integral_const] at hpos
    simp at hpos
  · by_contra h1
    push Not at h1
    have hone : cdf μ E = 1 := le_antisymm (Probability.Line.cdf_le_one μ E) h1
    have hzero : (μ : Measure ℝ) (Ioi E) = 0 := by
      have h := Probability.Line.measureReal_Ioi μ E
      rw [hone, sub_self, measureReal_def, ENNReal.toReal_eq_zero_iff,
        or_iff_left (measure_ne_top _ _)] at h
      exact h
    have hae : ∀ᵐ x ∂(μ : Measure ℝ), x ≤ E := by
      have hset : {a : ℝ | ¬ a ≤ E} = Ioi E := by ext; simp
      rw [ae_iff, hset]
      exact hzero
    have hint : Integrable (fun x : ℝ ↦ E - x) (μ : Measure ℝ) := (integrable_const E).sub hid
    have hzero_int : ∫ x, (E - x) ∂(μ : Measure ℝ) = 0 := by
      rw [integral_sub (integrable_const E) hid, hEint, integral_const]
      simp
    have heq := (integral_eq_zero_iff_of_nonneg_ae (hae.mono fun x hx ↦ sub_nonneg.mpr hx) hint).mp
      hzero_int
    have hae' : ∀ᵐ x ∂(μ : Measure ℝ), x = E := by
      filter_upwards [heq] with x hx
      have : E - x = 0 := hx
      linarith
    have hcompl : (μ : Measure ℝ) {E}ᶜ = 0 := by
      have hset : {a : ℝ | ¬ a = E} = {E}ᶜ := by ext; simp
      rw [ae_iff, hset] at hae'
      exact hae'
    have := measure_compl (μ := (μ : Measure ℝ)) (measurableSet_singleton E) (measure_ne_top _ _)
    rw [hcompl, hsingle, measure_univ] at this
    simp at this

end LogConcave

end KLS

namespace Probability.Line

/-- An affine function positive on the open unit interval has nonnegative endpoint values. -/
theorem nonneg_of_affine_pos {A B : ℝ} (h : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < A * (1 - t) + B * t) :
    0 ≤ A ∧ 0 ≤ B := by
  constructor
  · by_contra hA
    push Not at hA
    rcases le_or_gt B 0 with hB | hB
    · have := h (1 / 2) ⟨by norm_num, by norm_num⟩
      linarith
    · set t : ℝ := -A / (2 * (B - A)) with ht
      have hBA : 0 < B - A := by linarith
      have ht0 : 0 < t := by rw [ht]; apply div_pos <;> linarith
      have ht1 : t < 1 := by
        rw [ht, div_lt_one (by positivity)]
        linarith
      have := h t ⟨ht0, ht1⟩
      have hval : A * (1 - t) + B * t = A / 2 := by
        rw [ht]
        field_simp
        ring
      linarith
  · by_contra hB
    push Not at hB
    rcases le_or_gt A 0 with hA | hA
    · have := h (1 / 2) ⟨by norm_num, by norm_num⟩
      linarith
    · set t : ℝ := (A - B / 2) / (A - B) with ht
      have hAB : 0 < A - B := by linarith
      have ht0 : 0 < t := by rw [ht]; apply div_pos <;> linarith
      have ht1 : t < 1 := by
        rw [ht, div_lt_one hAB]
        linarith
      have := h t ⟨ht0, ht1⟩
      have hval : A * (1 - t) + B * t = B / 2 := by
        rw [ht]
        field_simp
        ring
      linarith

end Probability.Line

namespace KLS.LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ) (hμ : LogConcave μ)
  (hi : (interior (μ : Measure ℝ).support).Nonempty)
include hμ hi

omit hi in
/-- The affine majorant in terms of the distribution function induced by a supporting exponential
at `x₀`. -/
theorem le_affine_of_supergradient {x₀ k : ℝ} (hx₀ : x₀ ∈ interior (μ : Measure ℝ).support)
    (hk : ∀ s ∈ interior (μ : Measure ℝ).support, d.ρ s ≤ d.ρ x₀ * Real.exp (k * (s - x₀)))
    {y : ℝ} (hy : y ∈ interior (μ : Measure ℝ).support) :
    d.ρ y ≤ (d.ρ x₀ - k * cdf μ x₀) * (1 - cdf μ y) + (d.ρ x₀ + k * (1 - cdf μ x₀)) * cdf μ y := by
  have h := d.le_add_mul_cdf_sub_of_mem hμ hx₀ hk hy
  have : (d.ρ x₀ - k * cdf μ x₀) * (1 - cdf μ y) + (d.ρ x₀ + k * (1 - cdf μ x₀)) * cdf μ y =
      d.ρ x₀ + k * (cdf μ y - cdf μ x₀) := by ring
  linarith

/-- An affine majorant of the density in terms of the distribution function is positive on the
open unit interval. -/
theorem affine_pos_of_bound {A B : ℝ}
    (hbound : ∀ y ∈ interior (μ : Measure ℝ).support, d.ρ y ≤ A * (1 - cdf μ y) + B * cdf μ y)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < A * (1 - t) + B * t := by
  obtain ⟨y, hy⟩ := Probability.Line.exists_cdf_eq μ d.withDensity_eq d.measurable d.nonneg ht.1 ht.2
  have hyΩ : y ∈ interior (μ : Measure ℝ).support :=
    hμ.mem_interior_support_of_cdf hi (hy ▸ ht.1) (hy ▸ ht.2)
  have := hbound y hyΩ
  rw [hy] at this
  exact (d.pos hyΩ).trans_le this

/-- Variance lower bound from an affine majorant: if `ρ ≤ A (1 - F) + B F` on the interior of the
support with `A, B ≥ 0`, then `Var μ ≥ 1 / (√A + √B)⁴`. -/
theorem variance_ge_of_affine_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ y ∈ interior (μ : Measure ℝ).support, d.ρ y ≤ A * (1 - cdf μ y) + B * cdf μ y) :
    1 / (Real.sqrt A + Real.sqrt B) ^ 4 ≤ variance id (μ : Measure ℝ) := by
  set Ω := interior (μ : Measure ℝ).support with hΩ
  have hΩo : IsOpen Ω := isOpen_interior
  have hae : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ω := ae_iff.mpr (hμ.measure_compl_interior_support hi)
  set E := ∫ x, id x ∂(μ : Measure ℝ) with hE
  have hEΩ : E ∈ Ω := hμ.mean_mem_interior_support hi
  have hFmeas : Measurable (cdf μ) := (Probability.Line.cdf_mono μ).measurable
  have hmap := Probability.Line.map_cdf_eq_uniform μ d.withDensity_eq d.measurable d.nonneg
  have hidsq : Integrable (fun x : ℝ ↦ (id x - E) ^ 2) (μ : Measure ℝ) := by
    have := (hμ.memLp_id_two.sub (memLp_const E)).integrable_sq
    exact this.congr (ae_of_all _ fun x ↦ rfl)
  -- the estimate for each perturbation `ε > 0`
  have hε : ∀ ε : ℝ, 0 < ε →
      1 / (Real.sqrt (A + ε) + Real.sqrt (B + ε)) ^ 4 ≤ variance id (μ : Measure ℝ) := by
    intro ε hε
    set a := Real.sqrt (A + ε) with ha_def
    set b := Real.sqrt (B + ε) with hb_def
    have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
    have ha2 : a ^ 2 = A + ε := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = B + ε := Real.sq_sqrt (by linarith)
    set p : ℝ := cdf μ E with hp_def
    have hp : p ∈ Icc (0 : ℝ) 1 := ⟨Probability.Line.cdf_nonneg μ E, Probability.Line.cdf_le_one μ E⟩
    set q : ℝ → ℝ := affineQuantile a b p with hq
    set Ψ : ℝ → ℝ := fun y ↦ q (cdf μ y) with hΨ
    -- the weight dominates the density on `Ω`
    have hw : ∀ y ∈ Ω, d.ρ y < affineWeight a b (cdf μ y) := by
      intro y hy
      have h1 := hbound y hy
      have hF0 := Probability.Line.cdf_nonneg μ y
      have hF1 := Probability.Line.cdf_le_one μ y
      unfold affineWeight
      rw [ha2, hb2]
      nlinarith
    have hwpos : ∀ y ∈ Ω, 0 < affineWeight a b (cdf μ y) := fun y hy ↦ (d.pos hy).trans (hw y hy)
    have hFΩ : ∀ y ∈ Ω, cdf μ y ∈ Ioo (0 : ℝ) 1 := fun y hy ↦
      ⟨Probability.Line.cdf_pos_of_mem_interior_support μ hy,
        Probability.Line.cdf_lt_one_of_mem_interior_support μ hy⟩
    -- derivative of `Ψ` on `Ω`
    have hΨderiv : ∀ y ∈ Ω, HasDerivAt Ψ ((affineWeight a b (cdf μ y))⁻¹ * d.ρ y) y := by
      intro y hy
      exact (Probability.Line.hasDerivAt_affineQuantile ha hb hp (hFΩ y hy)).comp y (d.hasDerivAt_cdf hy)
    have hderiv_bounds : ∀ y ∈ Ω, 0 ≤ (affineWeight a b (cdf μ y))⁻¹ * d.ρ y ∧
        (affineWeight a b (cdf μ y))⁻¹ * d.ρ y ≤ 1 := by
      intro y hy
      have hwy := hwpos y hy
      constructor
      · exact mul_nonneg (inv_nonneg.mpr hwy.le) (d.nonneg y)
      · rw [inv_mul_le_iff₀ hwy, mul_one]
        exact (hw y hy).le
    have hderiv_cont : ContinuousOn (fun y ↦ (affineWeight a b (cdf μ y))⁻¹ * d.ρ y) Ω := by
      refine ContinuousOn.mul ?_ d.continuousOn
      refine ContinuousOn.inv₀ ?_ fun y hy ↦ (hwpos y hy).ne'
      exact (Probability.Line.continuous_affineWeight.comp d.continuous_cdf).continuousOn
    -- `Ψ` is `1`-Lipschitz on `Ω`
    have hlip : ∀ y ∈ Ω, ∀ z ∈ Ω, y ≤ z → 0 ≤ Ψ z - Ψ y ∧ Ψ z - Ψ y ≤ z - y := by
      intro y hy z hz hyz
      have hIcc : Icc y z ⊆ Ω := hμ.convex_interior_support.ordConnected.out hy hz
      have huIcc : uIcc y z = Icc y z := uIcc_of_le hyz
      have hftc : ∫ t in y..z, (affineWeight a b (cdf μ t))⁻¹ * d.ρ t = Ψ z - Ψ y := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hΨderiv t (hIcc (huIcc ▸ ht))) ?_
        apply ContinuousOn.intervalIntegrable
        rw [huIcc]
        exact hderiv_cont.mono hIcc
      have hint : IntervalIntegrable (fun t ↦ (affineWeight a b (cdf μ t))⁻¹ * d.ρ t) volume y z := by
        apply ContinuousOn.intervalIntegrable
        rw [huIcc]
        exact hderiv_cont.mono hIcc
      rw [← hftc]
      constructor
      · exact intervalIntegral.integral_nonneg hyz fun t ht ↦ (hderiv_bounds t (hIcc ht)).1
      · have := intervalIntegral.integral_mono_on hyz hint (intervalIntegrable_const (c := (1 : ℝ)))
          fun t ht ↦ (hderiv_bounds t (hIcc ht)).2
        rwa [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
    -- `Ψ` is continuous
    have hqcont : ContinuousOn q (Icc 0 1) := by
      have := intervalIntegral.continuousOn_primitive_interval'
        (Probability.Line.intervalIntegrable_inv_affineWeight ha hb (left_mem_Icc.mpr zero_le_one)
          (right_mem_Icc.mpr zero_le_one)) (a := p) (by rw [uIcc_of_le zero_le_one]; exact hp)
      rwa [uIcc_of_le zero_le_one] at this
    have hΨcont : Continuous Ψ :=
      hqcont.comp_continuous d.continuous_cdf fun y ↦
        ⟨Probability.Line.cdf_nonneg μ y, Probability.Line.cdf_le_one μ y⟩
    -- variance comparison
    have hvarΨ : variance Ψ (μ : Measure ℝ) ≤ variance id (μ : Measure ℝ) := by
      have hΨmeas : AEStronglyMeasurable Ψ (μ : Measure ℝ) := hΨcont.aestronglyMeasurable
      have hpt : ∀ x ∈ Ω, (Ψ x - Ψ E) ^ 2 ≤ (id x - E) ^ 2 := by
        intro x hx
        rw [sq_le_sq]
        rcases le_total x E with hxE | hEx
        · obtain ⟨h1, h2⟩ := hlip x hx E hEΩ hxE
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by simpa using hxE)]
          simpa using h2
        · obtain ⟨h1, h2⟩ := hlip E hEΩ x hx hEx
          rw [abs_of_nonneg h1, abs_of_nonneg (by simpa using hEx)]
          simpa using h2
      have hint1 : Integrable (fun x ↦ (Ψ x - Ψ E) ^ 2) (μ : Measure ℝ) := by
        refine hidsq.mono' ((hΨmeas.sub aestronglyMeasurable_const).pow 2) ?_
        filter_upwards [hae] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hpt x hx
      calc variance Ψ (μ : Measure ℝ) = variance (fun x ↦ Ψ x - Ψ E) (μ : Measure ℝ) :=
            (variance_sub_const hΨmeas (Ψ E)).symm
        _ ≤ ∫ x, (Ψ x - Ψ E) ^ 2 ∂(μ : Measure ℝ) := by
            have := variance_le_expectation_sq (μ := (μ : Measure ℝ)) (X := fun x ↦ Ψ x - Ψ E)
              (hΨmeas.sub aestronglyMeasurable_const)
            simpa [Pi.pow_apply] using this
        _ ≤ ∫ x, (id x - E) ^ 2 ∂(μ : Measure ℝ) := by
            refine integral_mono_ae hint1 hidsq ?_
            filter_upwards [hae] with x hx
            exact hpt x hx
        _ = variance id (μ : Measure ℝ) := (variance_eq_integral aemeasurable_id).symm
    -- the law of `Ψ` is the uniform law pushed through `q`
    have hvar_eq : variance Ψ (μ : Measure ℝ) = variance q unitUniform := by
      have hqmeas : AEMeasurable q ((μ : Measure ℝ).map (cdf μ)) := by
        rw [hmap]
        exact (hqcont.aestronglyMeasurable measurableSet_Icc).aemeasurable
      have := variance_map (X := q) (Y := cdf μ) (μ := (μ : Measure ℝ)) hqmeas hFmeas.aemeasurable
      rw [hmap] at this
      rw [this]
      rfl
    calc 1 / (a + b) ^ 4 ≤ variance q unitUniform :=
          Probability.Line.one_div_le_variance_affineQuantile ha hb hp
      _ = variance Ψ (μ : Measure ℝ) := hvar_eq.symm
      _ ≤ variance id (μ : Measure ℝ) := hvarΨ
  -- pass to the limit `ε → 0`
  by_cases hS : Real.sqrt A + Real.sqrt B = 0
  · rw [hS]
    simp only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), div_zero]
    exact variance_nonneg _ _
  · have hcont : ContinuousAt (fun ε : ℝ ↦ 1 / (Real.sqrt (A + ε) + Real.sqrt (B + ε)) ^ 4) 0 := by
      have h1 : Continuous fun ε : ℝ ↦ (Real.sqrt (A + ε) + Real.sqrt (B + ε)) ^ 4 :=
        ((Real.continuous_sqrt.comp (continuous_const.add continuous_id)).add
          (Real.continuous_sqrt.comp (continuous_const.add continuous_id))).pow 4
      refine continuousAt_const.div h1.continuousAt ?_
      simpa using pow_ne_zero 4 hS
    have htend : Tendsto (fun ε : ℝ ↦ 1 / (Real.sqrt (A + ε) + Real.sqrt (B + ε)) ^ 4) (𝓝[>] 0)
        (𝓝 (1 / (Real.sqrt A + Real.sqrt B) ^ 4)) := by
      have := hcont.tendsto
      simp only [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε' hε' ↦ hε ε' hε')

/-- Profile bound: on the interior of the support, `F (1 - F) ≤ σ · ρ` with `σ` the standard
deviation. -/
theorem cdf_mul_one_sub_cdf_le_sd_mul {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    cdf μ x * (1 - cdf μ x) ≤ Real.sqrt (variance id (μ : Measure ℝ)) * d.ρ x := by
  obtain ⟨k, hk⟩ := d.exists_supergradient hμ hx
  set A : ℝ := d.ρ x - k * cdf μ x with hA_def
  set B : ℝ := d.ρ x + k * (1 - cdf μ x) with hB_def
  have hbound : ∀ y ∈ interior (μ : Measure ℝ).support,
      d.ρ y ≤ A * (1 - cdf μ y) + B * cdf μ y := fun y hy ↦
    d.le_affine_of_supergradient hμ hx hk hy
  obtain ⟨hA, hB⟩ := Probability.Line.nonneg_of_affine_pos fun t ht ↦
    d.affine_pos_of_bound hμ hi hbound ht
  have hvar := d.variance_ge_of_affine_bound hμ hi hA hB hbound
  set F := cdf μ x with hF_def
  have hρx : 0 < d.ρ x := d.pos hx
  have hρeq : A * (1 - F) + B * F = d.ρ x := by rw [hA_def, hB_def]; ring
  set sA := Real.sqrt A with hsA
  set sB := Real.sqrt B with hsB
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt hA
  have hsB2 : sB ^ 2 = B := Real.sq_sqrt hB
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg A
  have hsB0 : 0 ≤ sB := Real.sqrt_nonneg B
  have hS : 0 < sA + sB := by
    rcases eq_or_lt_of_le (add_nonneg hsA0 hsB0) with h | h
    · exfalso
      have h1 : sA = 0 := by linarith
      have h2 : sB = 0 := by linarith
      have hA0 : A = 0 := by rw [← hsA2, h1]; ring
      have hB0 : B = 0 := by rw [← hsB2, h2]; ring
      have : A * (1 - F) + B * F = 0 := by rw [hA0, hB0]; ring
      linarith
    · exact h
  have hF0 := Probability.Line.cdf_nonneg μ x
  have hF1 := Probability.Line.cdf_le_one μ x
  -- `A (1 - F) + B F ≥ (√A + √B)² F (1 - F)`
  have hAM : (sA + sB) ^ 2 * (F * (1 - F)) ≤ A * (1 - F) + B * F := by
    have := sq_nonneg (sA * (1 - F) - sB * F)
    nlinarith [hsA2, hsB2]
  have hvarpos : 0 < variance id (μ : Measure ℝ) :=
    lt_of_lt_of_le (by positivity) hvar
  set σ := Real.sqrt (variance id (μ : Measure ℝ)) with hσ
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hvarpos
  -- `1 / (sA + sB)² ≤ σ`
  have hσS : 1 / (sA + sB) ^ 2 ≤ σ := by
    have h1 : Real.sqrt (1 / (sA + sB) ^ 4) ≤ σ := Real.sqrt_le_sqrt hvar
    have h2 : Real.sqrt (1 / (sA + sB) ^ 4) = 1 / (sA + sB) ^ 2 := by
      rw [one_div, Real.sqrt_inv, show (sA + sB) ^ 4 = ((sA + sB) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity), one_div]
    rwa [h2] at h1
  have hS2 : 1 ≤ (sA + sB) ^ 2 * σ := by
    rw [div_le_iff₀ (by positivity)] at hσS
    linarith
  calc F * (1 - F) ≤ F * (1 - F) * ((sA + sB) ^ 2 * σ) := by
        have : 0 ≤ F * (1 - F) := mul_nonneg hF0 (by linarith)
        nlinarith
    _ = σ * ((sA + sB) ^ 2 * (F * (1 - F))) := by ring
    _ ≤ σ * (A * (1 - F) + B * F) := by gcongr
    _ = σ * d.ρ x := by rw [hρeq]

end KLS.LineDensity

end FunctionalInequalities
