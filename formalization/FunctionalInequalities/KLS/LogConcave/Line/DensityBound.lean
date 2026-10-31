module

public import FunctionalInequalities.KLS.LogConcave.Line.Buser

/-!
# The density at a point of balanced mass

Guédon–Milman, *Interpolating thin-shell and sharp large-deviation estimates for isotropic
log-concave measures* (arXiv:1011.0943v3), Lemma A.2: if `μ = f(x) dx` is a log-concave probability
measure on `ℝ` and `ε ≤ ∫_0^∞ f ≤ 1 - ε` for some `ε > 0`, then `f(0) ≥ ε ‖f‖_∞`.

Here `f` is the Borell representative `d.ρ` of a `LineDensity`, which is continuous on the interior
of the support, and `‖f‖_∞` is the essential supremum `eLpNorm d.ρ ⊤ volume`. The proof is the
paper's: the hazard-rate monotonicity `ρ x · G 0 ≤ ρ 0 · G x` for `x ≤ 0` and
`ρ x · F 0 ≤ ρ 0 · F x` for `x ≥ 0` bounds `ρ x` by `ρ 0 / ε` on the interior of the support,
and `ρ` vanishes almost everywhere off it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities.KLS.LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

include d

/-- A point whose right tail has mass strictly between `0` and `1` lies in the interior of the
support. -/
theorem mem_interior_support_of_measureReal_Ioi {x : ℝ} (h0 : 0 < (μ : Measure ℝ).real (Ioi x))
    (h1 : (μ : Measure ℝ).real (Ioi x) < 1) :
    x ∈ interior (μ : Measure ℝ).support := by
  have htail : (μ : Measure ℝ).real (Ioi x) = 1 - cdf μ x :=
    FunctionalInequalities.Probability.Line.measureReal_Ioi μ x
  have hcdf0 : 0 < cdf μ x := by
    linarith [h1, htail]
  have hcdf1 : cdf μ x < 1 := by
    linarith [h0, htail]
  exact
    LogConcave.mem_interior_support_of_cdf
      d.logConcave d.interior_support_nonempty hcdf0 hcdf1

/-- The pointwise bound on the interior of the support: if both `F 0 = μ(-∞, 0]` and
`G 0 = μ(0, ∞)` are at least `ε`, then `ε ρ x ≤ ρ 0`. -/
theorem mul_le_of_mem_interior_support {ε x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support)
    (hF : ε ≤ cdf μ 0) (hG : ε ≤ (μ : Measure ℝ).real (Ioi 0)) :
    ε * d.ρ x ≤ d.ρ 0 := by
  have htail_le : ∀ z : ℝ, (μ : Measure ℝ).real (Ioi z) ≤ 1 := by
    intro z
    rw [FunctionalInequalities.Probability.Line.measureReal_Ioi μ z]
    have hz := FunctionalInequalities.Probability.Line.cdf_nonneg (μ := μ) z
    linarith

  have hcdf_le : ∀ z : ℝ, cdf μ z ≤ 1 := by
    intro z
    exact FunctionalInequalities.Probability.Line.cdf_le_one (μ := μ) z

  rcases le_total x 0 with hxo | hox
  · have hhaz :
        d.ρ x * (μ : Measure ℝ).real (Ioi 0) ≤
          d.ρ 0 * (μ : Measure ℝ).real (Ioi x) :=
      d.mul_measureReal_Ioi_le d.logConcave d.interior_support_nonempty hx hxo
    have hbound :
        d.ρ 0 * (μ : Measure ℝ).real (Ioi x) ≤ d.ρ 0 := by
      have h :=
        mul_le_mul_of_nonneg_left (htail_le x) (d.nonneg 0)
      simpa using h
    calc
      ε * d.ρ x ≤ (μ : Measure ℝ).real (Ioi 0) * d.ρ x :=
        mul_le_mul_of_nonneg_right hG (d.nonneg x)
      _ = d.ρ x * (μ : Measure ℝ).real (Ioi 0) := by
        rw [mul_comm]
      _ ≤ d.ρ 0 := le_trans hhaz hbound
  · have hhaz : d.ρ x * cdf μ 0 ≤ d.ρ 0 * cdf μ x :=
      d.mul_cdf_le d.logConcave d.interior_support_nonempty hx hox
    have hbound : d.ρ 0 * cdf μ x ≤ d.ρ 0 := by
      have h :=
        mul_le_mul_of_nonneg_left (hcdf_le x) (d.nonneg 0)
      simpa using h
    calc
      ε * d.ρ x ≤ cdf μ 0 * d.ρ x :=
        mul_le_mul_of_nonneg_right hF (d.nonneg x)
      _ = d.ρ x * cdf μ 0 := by
        rw [mul_comm]
      _ ≤ d.ρ 0 := le_trans hhaz hbound

/-- The almost-everywhere form of Lemma A.2. -/
theorem ae_mul_le {ε : ℝ} (hε : 0 < ε) (h0 : ε ≤ (μ : Measure ℝ).real (Ioi 0))
    (h1 : (μ : Measure ℝ).real (Ioi 0) ≤ 1 - ε) :
    ∀ᵐ x, ε * d.ρ x ≤ d.ρ 0 := by
  have htail :
      (μ : Measure ℝ).real (Ioi 0) = 1 - cdf μ 0 :=
    FunctionalInequalities.Probability.Line.measureReal_Ioi μ 0
  have hF : ε ≤ cdf μ 0 := by
    linarith [h1, htail]
  have htail_pos : 0 < (μ : Measure ℝ).real (Ioi 0) :=
    lt_of_lt_of_le hε h0
  have htail_lt : (μ : Measure ℝ).real (Ioi 0) < 1 := by
    linarith [h1, hε]
  have hzero :
      (0 : ℝ) ∈ interior (μ : Measure ℝ).support :=
    d.mem_interior_support_of_measureReal_Ioi htail_pos htail_lt
  filter_upwards [
    d.ae_eq_zero_of_not_mem_interior_support
      d.logConcave d.interior_support_nonempty
  ] with x hx
  by_cases hxin : x ∈ interior (μ : Measure ℝ).support
  · exact d.mul_le_of_mem_interior_support hxin hF h0
  · have hxzero : d.ρ x = 0 := hx hxin
    simpa [hxzero] using d.nonneg 0

/-- Guédon–Milman (2011), Lemma A.2: if `ε ≤ ∫_0^∞ ρ ≤ 1 - ε` for some `ε > 0`, then
`ρ(0) ≥ ε ‖ρ‖_∞`. -/
theorem ofReal_mul_eLpNorm_top_le {ε : ℝ} (hε : 0 < ε) (h0 : ε ≤ ∫ x in Ioi 0, d.ρ x)
    (h1 : ∫ x in Ioi 0, d.ρ x ≤ 1 - ε) :
    ENNReal.ofReal ε * eLpNorm d.ρ ⊤ volume ≤ ENNReal.ofReal (d.ρ 0) := by
  have hmeasure :
      (μ : Measure ℝ).real (Ioi 0) = ∫ x in Ioi 0, d.ρ x :=
    d.measureReal_eq_setIntegral measurableSet_Ioi

  have h0' : ε ≤ (μ : Measure ℝ).real (Ioi 0) := by
    calc
      ε ≤ ∫ x in Ioi 0, d.ρ x := h0
      _ = (μ : Measure ℝ).real (Ioi 0) := hmeasure.symm

  have h1' : (μ : Measure ℝ).real (Ioi 0) ≤ 1 - ε := by
    calc
      (μ : Measure ℝ).real (Ioi 0) = ∫ x in Ioi 0, d.ρ x := hmeasure
      _ ≤ 1 - ε := h1

  have hae :
      ∀ᵐ x ∂(volume : Measure ℝ), ‖d.ρ x‖ ≤ d.ρ 0 / ε := by
    filter_upwards [d.ae_mul_le hε h0' h1'] with x hx
    calc
      ‖d.ρ x‖ = d.ρ x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (d.nonneg x)]
      _ ≤ d.ρ 0 / ε := by
        apply (le_div_iff₀ hε).2
        simpa [mul_comm] using hx

  have hess :
      eLpNormEssSup d.ρ volume ≤ ENNReal.ofReal (d.ρ 0 / ε) :=
    MeasureTheory.eLpNormEssSup_le_of_ae_bound hae

  have hep :
      eLpNorm d.ρ ⊤ volume ≤ ENNReal.ofReal (d.ρ 0 / ε) := by
    rw [MeasureTheory.eLpNorm_exponent_top d.measurable.aestronglyMeasurable]
    exact hess

  calc
    ENNReal.ofReal ε * eLpNorm d.ρ ⊤ volume ≤
        ENNReal.ofReal ε * ENNReal.ofReal (d.ρ 0 / ε) :=
      mul_le_mul_of_nonneg_left hep (by exact bot_le)
    _ = ENNReal.ofReal (ε * (d.ρ 0 / ε)) := by
      rw [ENNReal.ofReal_mul hε.le]
    _ = ENNReal.ofReal (d.ρ 0) := by
      congr 1
      field_simp [hε.ne']

end FunctionalInequalities.KLS.LineDensity
