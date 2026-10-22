import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Holder

/-!
# Real averages over finite measures

Averaging an a.e. pairwise bound over a finite nonzero measure, the essential supremum bounded by such an average, the
`L¹` norm of an integrable a.e. nonnegative function as its integral, and radius-normalized `L¹` estimates `R^{−N} ‖w‖₁ ≤ C T`
turned into integral and average bounds once `μ(univ) = m R^N`. (`Mathlib.Analysis.InnerProductSpace.Basic` is imported so that
the real Bochner integral uses the inner-product-space instance path of the reviewed statements.)
-/

/-! ## Averages of a.e. bounds and normalized L¹ estimates -/

noncomputable section RealAverages

open MeasureTheory Filter

namespace FunctionalInequalities.Analysis

/-- Averaging an a.e. pairwise bound `lc · g y ≤ uc · f x + E` over a finite nonzero measure in `x` gives
`lc · g y ≤ uc · (∫ f dμ)/μ(univ) + E` for a.e. `y`. -/
theorem average_of_ae_pairwise_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → ℝ) (g : Y → ℝ) {lc uc E : ℝ} (hf : Integrable f μ)
    (hpair : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, lc*g y ≤ uc*f x+E) :
    ∀ᵐ y ∂ν, lc*g y ≤ uc*((∫ x, f x ∂μ)/μ.real Set.univ)+E := by
  have hm : 0 < μ.real Set.univ := ENNReal.toReal_pos (by simpa using (NeZero.ne μ)) (measure_lt_top μ Set.univ).ne
  filter_upwards [hpair] with y hy
  have hmono := integral_mono_ae (integrable_const (lc*g y)) ((hf.const_mul uc).add (integrable_const E)) hy
  change (∫ x, lc*g y ∂μ) ≤ ∫ x, uc*f x+E ∂μ at hmono
  rw [integral_add (hf.const_mul uc) (integrable_const E)] at hmono
  simp only [integral_const_mul, integral_const, smul_eq_mul] at hmono
  have heq : uc*((∫ x, f x ∂μ)/μ.real Set.univ)+E =
      (uc*(∫ x, f x ∂μ)+E*μ.real Set.univ)/μ.real Set.univ := by field_simp
  rw [heq]
  apply (le_div_iff₀ hm).2
  nlinarith

/-- Under the averaged pairwise bound (with `lc > 0` and `g ≥ 0` a.e.), `essSup g ≤ (uc/lc) · (∫ f dμ)/μ(univ) + E/lc`. -/
theorem essSup_le_average_of_ae_pairwise_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [NeZero μ] [NeZero ν]
    (f : X → ℝ) (g : Y → ℝ) {lc uc E : ℝ} (hlc : 0 < lc) (hf : Integrable f μ)
    (hg0 : ∀ᵐ y ∂ν, 0 ≤ g y)
    (hpair : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, lc*g y ≤ uc*f x+E) :
    essSup g ν ≤ (uc/lc)*((∫ x, f x ∂μ)/μ.real Set.univ)+E/lc := by
  have hav := average_of_ae_pairwise_bound μ ν f g hf hpair
  have hg : ∀ᵐ y ∂ν, g y ≤ (uc/lc)*((∫ x, f x ∂μ)/μ.real Set.univ)+E/lc := by
    filter_upwards [hav] with y hy
    have hle : g y ≤ (uc*((∫ x, f x ∂μ)/μ.real Set.univ)+E)/lc := (le_div_iff₀ hlc).2 (by nlinarith)
    convert hle using 1; ring
  exact essSup_le_of_ae_le _ hg (isCoboundedUnder_le_of_eventually_le _ hg0)

/-- For an integrable a.e. nonnegative `w`, `‖w‖_{L¹} = ofReal (∫ w)`. -/
theorem eLpNorm_one_eq_ofReal_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x) :
    eLpNorm w 1 μ = ENNReal.ofReal (∫ x, w x ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm,← ofReal_integral_norm_eq_lintegral_enorm hw]
  congr 1
  apply integral_congr_ae
  filter_upwards [hw0] with x hx
  exact Real.norm_of_nonneg hx

/-- A radius-normalized `L¹` estimate `R^{−N} ‖w‖₁ ≤ C · T` of an integrable a.e. nonnegative `w` gives `∫ w ≤ C T R^N`. -/
theorem integral_le_of_normalized_eLpNorm_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    {R N C T : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (h : (ENNReal.ofReal R)^(-N) * eLpNorm w 1 μ ≤ ENNReal.ofReal C * ENNReal.ofReal T) :
    (∫ x, w x ∂μ) ≤ C*T*R^N := by
  rw [eLpNorm_one_eq_ofReal_integral μ w hw hw0,ENNReal.ofReal_rpow_of_pos hR,
    ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hR (-N)).le,← ENNReal.ofReal_mul hC] at h
  have hre : R^(-N)*(∫ x, w x ∂μ) ≤ C*T :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hT)).1 h
  have he : R^(-N)*R^N = 1 := by rw [← Real.rpow_add hR,neg_add_cancel,Real.rpow_zero]
  calc
    _ = (R^(-N)*(∫ x, w x ∂μ))*R^N := by rw [mul_right_comm,he,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hre (Real.rpow_pos_of_pos hR N).le

/-- If moreover `μ(univ) = m R^N` (`m > 0`), the radius cancels in the average: `(∫ w)/μ(univ) ≤ C T/m`. -/
theorem average_le_of_normalized_eLpNorm_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    {R N C T m : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hT : 0 ≤ T) (hm : 0 < m)
    (hmass : μ.real Set.univ = m*R^N)
    (h : (ENNReal.ofReal R)^(-N) * eLpNorm w 1 μ ≤ ENNReal.ofReal C * ENNReal.ofReal T) :
    (∫ x, w x ∂μ)/μ.real Set.univ ≤ C*T/m := by
  have hi := integral_le_of_normalized_eLpNorm_one μ w hw hw0 hR hC hT h
  rw [hmass]
  apply (div_le_iff₀ (mul_pos hm (Real.rpow_pos_of_pos hR N))).2
  calc
    _ ≤ C*T*R^N := hi
    _ = _ := by field_simp

end FunctionalInequalities.Analysis

end RealAverages

/-! ## Hölder moduli of averages -/

noncomputable section HolderMeans

namespace FunctionalInequalities.Analysis

section HolderAverages

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A real-valued `f` with `dist (f x) (f y) ≤ C · dist x y ^ r` is `(C, r)`-Hölder. -/
private theorem holderWith_real_of_dist_bound {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (C r : ℝ≥0)
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ)*dist x y^(r : ℝ)) :
    HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg]
  calc
    _ ≤ ENNReal.ofReal ((C : ℝ)*dist x y^(r : ℝ)) := ENNReal.ofReal_le_ofReal (h x y)
    _ = _ := by rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- If almost every `q t` is `(C, r)`-Hölder and every `t ↦ q t x` is integrable for a probability measure `μ`, then
`x ↦ ∫ q t x dμ(t)` is `(C, r)`-Hölder with the same constants. -/
theorem holderWith_probability_mean {Ω X : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Ω → X → ℝ) (C r : ℝ≥0)
    (hq : ∀ x, Integrable (fun t => q t x) μ)
    (hh : ∀ᵐ t ∂μ, HolderWith C r (q t)) :
    HolderWith C r (fun x => ∫ t, q t x ∂μ) := by
  apply holderWith_real_of_dist_bound
  intro x y
  rw [Real.dist_eq, ← integral_sub (hq x) (hq y)]
  have hbound : ∀ᵐ t ∂μ, ‖q t x - q t y‖ ≤ (C : ℝ)*dist x y^(r : ℝ) :=
    hh.mono fun t ht => by simpa only [Real.norm_eq_abs, Real.dist_eq] using ht.dist_le x y
  simpa [Measure.real, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hbound

/-- If `q t` is `(C, r)`-Hölder for every `t ∈ (0, 1]` and every `t ↦ q t x` is interval integrable on `[0, 1]`, then
`x ↦ ∫₀¹ q t x dt` is `(C, r)`-Hölder with the same constants. -/
theorem holderWith_unit_interval_mean {X : Type*} [PseudoMetricSpace X]
    (q : ℝ → X → ℝ) (C r : ℝ≥0)
    (hq : ∀ x, IntervalIntegrable (fun t => q t x) volume 0 1)
    (hh : ∀ t ∈ uIoc (0 : ℝ) 1, HolderWith C r (q t)) :
    HolderWith C r (fun x => ∫ t in (0 : ℝ)..1, q t x) := by
  apply holderWith_real_of_dist_bound
  intro x y
  rw [Real.dist_eq, ← intervalIntegral.integral_sub (hq x) (hq y)]
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖q t x - q t y‖ ≤ (C : ℝ)*dist x y^(r : ℝ) := fun t ht => by
    simpa only [Real.norm_eq_abs, Real.dist_eq] using (hh t ht).dist_le x y
  simpa only [sub_zero, abs_one, one_mul, mul_one, Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

end HolderAverages

end FunctionalInequalities.Analysis

end HolderMeans
