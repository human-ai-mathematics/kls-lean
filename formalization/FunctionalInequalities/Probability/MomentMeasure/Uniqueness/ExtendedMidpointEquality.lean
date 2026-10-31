module

public import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.MidpointEquality
public import FunctionalInequalities.Probability.MomentMeasure.FirstVariation
public import FunctionalInequalities.Analysis.Convex.EssentialContinuity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Equality in the midpoint Prékopa–Leindler inequality for extended-real potentials

Let `ψ₀, ψ₁ : E → ℝ ∪ {+∞}` be convex and lower semicontinuous on a finite-dimensional real
inner-product space with `∫ e^{-ψ₀} = ∫ e^{-ψ₁} = 1`, and let `ρ` be a Borel function with
`ρ((x + y)/2) ≥ √(e^{-ψ₀(x)} e^{-ψ₁(y)})` for all `x, y` and `∫ ρ ≤ 1`. Then
`ψ₁ = ψ₀(· − y₀)` everywhere, for some `y₀`
(`exists_eq_translate_of_midpoint_le_of_lintegral_le_one`). This is the equality case of
Prékopa's inequality used in Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1),
proof of Theorem 2, uniqueness (after Dubuc), for potentials that may take the value `+∞`.

Proof: convolution with the standard Gaussian kernel (`gaussSmooth`) preserves the midpoint
inequality and the masses (Prékopa–Leindler, the Gaussian being log-concave) and turns the
densities into everywhere positive log-concave ones, i.e. `e^{-ψᵢ'}` with finite convex `ψᵢ'`; the
finite case `exists_eq_translate_of_lintegral_midpointDensity_le_one` makes the smoothed densities
translates of each other; the characteristic function of the Gaussian has no zeros, so the
densities themselves agree almost everywhere up to the translation; finally two lower
semicontinuous convex potentials that agree almost everywhere agree everywhere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Kernel

private theorem integrable_exp_neg_half_sq_norm :
    Integrable (fun v : E => Real.exp (-(1 / 2) * ‖v‖ ^ 2)) (volume : Measure E) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (1 / 2 : ℂ))
    (by norm_num) 0 (0 : E)).norm
  refine h.congr (ae_of_all _ fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  norm_cast

/-- The normalizing constant `∫ exp(−‖v‖²/2) dv` of the Gaussian kernel. -/
private def gaussConst (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  ∫ v : E, Real.exp (-(1 / 2) * ‖v‖ ^ 2) ∂(volume : Measure E)

private theorem gaussConst_pos : 0 < gaussConst E := by
  rw [gaussConst, GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1 / 2)]
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The standard Gaussian probability density on `E`, as an `ℝ≥0∞`-valued function. -/
private def gauss (z : E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(1 / 2) * ‖z‖ ^ 2) / gaussConst E)

private theorem measurable_gauss : Measurable (gauss : E → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
    (measurable_const.mul (continuous_norm.measurable.pow_const 2))).div_const _)

private theorem gauss_pos (z : E) : 0 < gauss z :=
  ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) gaussConst_pos)

private theorem lintegral_gauss : ∫⁻ z, gauss z ∂(volume : Measure E) = 1 := by
  unfold gauss
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_half_sq_norm.div_const _)
    (ae_of_all _ fun z => (div_pos (Real.exp_pos _) gaussConst_pos).le), integral_div,
    ← gaussConst, div_self gaussConst_pos.ne', ENNReal.ofReal_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_sq_combo_le (u v : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖t • u + (1 - t) • v‖ ^ 2 ≤ t * ‖u‖ ^ 2 + (1 - t) * ‖v‖ ^ 2 := by
  have h1 : ‖t • u + (1 - t) • v‖ ^ 2 =
      t ^ 2 * ‖u‖ ^ 2 + 2 * (t * (1 - t)) * ⟪u, v⟫ + (1 - t) ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg (by linarith)]
    ring
  have h2 : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at h2
  rw [h1]
  nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - t)]

/-- The Gaussian kernel is log-concave. -/
private theorem gauss_rpow_mul_le (u v : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    gauss u ^ t * gauss v ^ (1 - t) ≤ gauss (t • u + (1 - t) • v) := by
  have hc := gaussConst_pos (E := E)
  have h1t : 0 < 1 - t := by linarith
  simp only [gauss]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) h1t.le, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.div_rpow (Real.exp_pos _).le hc.le, Real.div_rpow (Real.exp_pos _).le hc.le,
    div_mul_div_comm, ← Real.rpow_add hc, add_sub_cancel, Real.rpow_one,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) hc.le
  have := norm_sq_combo_le u v ht0.le ht1.le
  nlinarith

end Kernel

section Smoothing

/-- Convolution with the standard Gaussian kernel: `(ρ ⋆ γ)(x) = ∫ ρ(x − u) γ(u) du`. -/
private def gaussSmooth (ρ : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∫⁻ u, ρ (x - u) * gauss u ∂(volume : Measure E)

private theorem measurable_gaussSmooth {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable (gaussSmooth ρ) :=
  ((hρ.comp (measurable_fst.sub measurable_snd)).mul
    (measurable_gauss.comp measurable_snd)).lintegral_prod_right'

private theorem lintegral_gaussSmooth {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) :
    ∫⁻ x, gaussSmooth ρ x ∂(volume : Measure E) = ∫⁻ x, ρ x ∂(volume : Measure E) := by
  simp only [gaussSmooth]
  rw [lintegral_lintegral_swap ((hρ.comp (measurable_fst.sub measurable_snd)).mul
    (measurable_gauss.comp measurable_snd)).aemeasurable]
  have h1 : ∀ u : E, ∫⁻ x, ρ (x - u) * gauss u ∂(volume : Measure E) =
      (∫⁻ x, ρ x ∂(volume : Measure E)) * gauss u := fun u => by
    rw [lintegral_mul_const (gauss u) (show Measurable fun x => ρ (x - u) from
      hρ.comp (measurable_id.sub_const u)), lintegral_sub_right_eq_self (fun x => ρ x) u]
  simp_rw [h1]
  rw [lintegral_const_mul _ measurable_gauss, lintegral_gauss, mul_one]

private theorem gauss_le_gauss_zero (u : E) : gauss u ≤ gauss (0 : E) := by
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_)
    gaussConst_pos.le)
  simp only [norm_zero]
  nlinarith [sq_nonneg ‖u‖]

private theorem gaussSmooth_le {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (x : E) :
    gaussSmooth ρ x ≤ (∫⁻ x, ρ x ∂(volume : Measure E)) * gauss (0 : E) := by
  calc gaussSmooth ρ x ≤ ∫⁻ u, ρ (x - u) * gauss (0 : E) ∂(volume : Measure E) :=
        lintegral_mono fun u => by gcongr; exact gauss_le_gauss_zero u
    _ = (∫⁻ u, ρ (x - u) ∂(volume : Measure E)) * gauss (0 : E) :=
        lintegral_mul_const _ (hρ.comp (measurable_const.sub measurable_id))
    _ = (∫⁻ x, ρ x ∂(volume : Measure E)) * gauss (0 : E) := by
        rw [lintegral_sub_left_eq_self (fun x => ρ x) x]

/-- Prékopa–Leindler passes through Gaussian smoothing: if
`f₀(x)^t f₁(y)^{1−t} ≤ f₂(t x + (1 − t) y)` for all `x, y`, the same holds for the smoothed
functions. -/
private theorem gaussSmooth_rpow_mul_le {f₀ f₁ f₂ : E → ℝ≥0∞} (h₀ : Measurable f₀)
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hf : ∀ x y, f₀ x ^ t * f₁ y ^ (1 - t) ≤ f₂ (t • x + (1 - t) • y)) (x y : E) :
    gaussSmooth f₀ x ^ t * gaussSmooth f₁ y ^ (1 - t) ≤
      gaussSmooth f₂ (t • x + (1 - t) • y) := by
  have h1t : 0 < 1 - t := by linarith
  refine Analysis.lintegral_prekopaLeindler (volume : Measure E)
    (f := fun u => f₀ (x - u) * gauss u) (g := fun v => f₁ (y - v) * gauss v)
    (h := fun w => f₂ (t • x + (1 - t) • y - w) * gauss w)
    ((h₀.comp (measurable_const.sub measurable_id)).mul measurable_gauss)
    ((h₁.comp (measurable_const.sub measurable_id)).mul measurable_gauss)
    ((h₂.comp (measurable_const.sub measurable_id)).mul measurable_gauss) ht0 ht1 ?_
  intro u v
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ _ h1t.le]
  have harg : t • x + (1 - t) • y - (t • u + (1 - t) • v) = t • (x - u) + (1 - t) • (y - v) := by
    module
  calc f₀ (x - u) ^ t * gauss u ^ t * (f₁ (y - v) ^ (1 - t) * gauss v ^ (1 - t))
      = (f₀ (x - u) ^ t * f₁ (y - v) ^ (1 - t)) * (gauss u ^ t * gauss v ^ (1 - t)) := by ring
    _ ≤ f₂ (t • (x - u) + (1 - t) • (y - v)) * gauss (t • u + (1 - t) • v) :=
        mul_le_mul' (hf _ _) (gauss_rpow_mul_le u v ht0 ht1)
    _ = f₂ (t • x + (1 - t) • y - (t • u + (1 - t) • v)) * gauss (t • u + (1 - t) • v) := by
        rw [harg]

/-- A Gaussian smoothing of a function that is positive on a nonempty open set is positive. -/
private theorem gaussSmooth_ne_zero {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) {U : Set E}
    (hU : IsOpen U) (hUne : U.Nonempty) (hpos : ∀ x ∈ U, ρ x ≠ 0) (x : E) :
    gaussSmooth ρ x ≠ 0 := by
  intro h0
  rw [gaussSmooth, lintegral_eq_zero_iff (show Measurable fun u => ρ (x - u) * gauss u from
    (hρ.comp (measurable_const.sub measurable_id)).mul measurable_gauss)] at h0
  set V : Set E := (fun u => x - u) ⁻¹' U with hV
  have hVo : IsOpen V := hU.preimage (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := hUne
  have hVne : V.Nonempty := ⟨x - z, by simp only [hV, mem_preimage, sub_sub_cancel]; exact hz⟩
  have hsub : V ⊆ {u | ¬ (ρ (x - u) * gauss u = (0 : E → ℝ≥0∞) u)} := by
    intro u hu
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, mul_eq_zero, not_or]
    exact ⟨hpos _ hu, (gauss_pos u).ne'⟩
  exact (hVo.measure_pos (volume : Measure E) hVne).ne' (measure_mono_null hsub (ae_iff.mp h0))

end Smoothing

section Potential

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The density of a real value of a potential. -/
private theorem density_eq_ofReal {ψ : E → EReal} {x : E} (htop : ψ x ≠ ⊤) (hbot : ψ x ≠ ⊥) :
    density ψ x = ENNReal.ofReal (Real.exp (-(ψ x).toReal)) := by
  rw [density, ← EReal.coe_toReal htop hbot, ← EReal.coe_neg, EReal.exp_coe, EReal.toReal_coe]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The density `e^{-ψ}` of a convex potential is log-concave. -/
private theorem density_rpow_mul_le {ψ : E → EReal} (hψ : ConvexPotential ψ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (x y : E) :
    density ψ x ^ t * density ψ y ^ (1 - t) ≤ density ψ (t • x + (1 - t) • y) := by
  have h1t : 0 < 1 - t := by linarith
  by_cases hx : ψ x = ⊤
  · have h0 : density ψ x = 0 := by rw [density, hx, EReal.neg_top, EReal.exp_bot]
    rw [h0, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact bot_le
  by_cases hy : ψ y = ⊤
  · have h0 : density ψ y = 0 := by rw [density, hy, EReal.neg_top, EReal.exp_bot]
    rw [h0, ENNReal.zero_rpow_of_pos h1t, mul_zero]
    exact bot_le
  have hz : ψ (t • x + (1 - t) • y) ≠ ⊤ :=
    hψ.convex_domain (show x ∈ {x | ψ x ≠ ⊤} from hx) (show y ∈ {x | ψ x ≠ ⊤} from hy) ht0.le
      h1t.le (by ring)
  have hconv := hψ.convexOn_toReal.2 (show x ∈ {x | ψ x ≠ ⊤} from hx)
    (show y ∈ {x | ψ x ≠ ⊤} from hy) ht0.le h1t.le (by ring)
  simp only [smul_eq_mul] at hconv
  rw [density_eq_ofReal hx (hψ.1 x), density_eq_ofReal hy (hψ.1 y),
    density_eq_ofReal hz (hψ.1 _), ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1t.le,
    ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  linarith

/-- **The smoothed potential.** Let `ρ` be Borel and log-concave
(`ρ(x)^t ρ(y)^{1−t} ≤ ρ(t x + (1 − t) y)`), with `∫ ρ = 1`, positive on a nonempty open set.
Then `ρ ⋆ γ = e^{-φ}` for a finite convex `φ` with `∫ e^{-φ} = 1`. -/
private theorem exists_convex_gaussSmooth_eq {ρ : E → ℝ≥0∞} (hρ : Measurable ρ)
    (hlc : ∀ t : ℝ, 0 < t → t < 1 → ∀ x y, ρ x ^ t * ρ y ^ (1 - t) ≤ ρ (t • x + (1 - t) • y))
    (hmass : ∫⁻ x, ρ x ∂(volume : Measure E) = 1) {U : Set E} (hU : IsOpen U)
    (hUne : U.Nonempty) (hpos : ∀ x ∈ U, ρ x ≠ 0) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ∀ x, ENNReal.ofReal (Real.exp (-φ x)) = gaussSmooth ρ x := by
  have hfin : ∀ x, gaussSmooth ρ x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (by rw [hmass, one_mul]; exact ENNReal.ofReal_ne_top) (gaussSmooth_le hρ x)
  have hne : ∀ x, gaussSmooth ρ x ≠ 0 := gaussSmooth_ne_zero hρ hU hUne hpos
  set F : E → ℝ := fun x => (gaussSmooth ρ x).toReal with hFdef
  have hF : ∀ x, 0 < F x := fun x => ENNReal.toReal_pos (hne x) (hfin x)
  have hFeq : ∀ x, ENNReal.ofReal (F x) = gaussSmooth ρ x := fun x => ENNReal.ofReal_toReal (hfin x)
  refine ⟨fun x => -Real.log (F x), ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_, fun x => ?_⟩
  · simp only [smul_eq_mul]
    rcases ha.lt_or_eq with ha' | ha'
    · rcases hb.lt_or_eq with hb' | hb'
      · have hb1 : b = 1 - a := by linarith
        subst hb1
        have hPL := gaussSmooth_rpow_mul_le hρ hρ hρ ha' (by linarith) (hlc a ha' (by linarith))
          x y
        have hreal : F x ^ a * F y ^ (1 - a) ≤ F (a • x + (1 - a) • y) := by
          have := ENNReal.toReal_mono (hfin _) hPL
          rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
        have hlog := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (hF x) _)
          (Real.rpow_pos_of_pos (hF y) _)) hreal
        rw [Real.log_mul (Real.rpow_pos_of_pos (hF x) a).ne'
          (Real.rpow_pos_of_pos (hF y) _).ne', Real.log_rpow (hF x), Real.log_rpow (hF y)] at hlog
        linarith
      · subst hb'
        have ha1 : a = 1 := by linarith
        subst ha1
        simp
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simp
  · have hm : (fun x => Real.exp (-(-Real.log (F x)))) = F := funext fun x => by
      rw [neg_neg, Real.exp_log (hF x)]
    simp only [hm]
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (hF x).le)
      (measurable_gaussSmooth hρ).ennreal_toReal.aestronglyMeasurable]
    simp only [hFeq]
    rw [lintegral_gaussSmooth hρ, hmass, ENNReal.toReal_one]
  · rw [neg_neg, Real.exp_log (hF x), hFeq]

end Potential

section Deconvolution

/-- The measure `ρ dx` convolved with the Gaussian measure has density `ρ ⋆ γ`. -/
private theorem withDensity_conv_gauss {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) :
    (volume : Measure E).withDensity ρ ∗ (volume : Measure E).withDensity gauss =
      (volume : Measure E).withDensity (gaussSmooth ρ) := by
  ext A hA
  set I : E → ℝ≥0∞ := A.indicator 1 with hI
  have hIm : Measurable I := measurable_one.indicator hA
  have hIadd : Measurable fun q : E × E => I (q.1 + q.2) := hIm.comp measurable_add
  rw [← lintegral_indicator_one hA, Measure.lintegral_conv hIm,
    lintegral_withDensity_eq_lintegral_mul _ hρ (hIadd.lintegral_prod_right'),
    withDensity_apply _ hA, ← lintegral_indicator hA]
  have hin : ∀ x, ∫⁻ y, I (x + y) ∂(volume : Measure E).withDensity gauss =
      ∫⁻ u, gauss u * I (x + u) ∂(volume : Measure E) := fun x => by
    rw [lintegral_withDensity_eq_lintegral_mul _ measurable_gauss
      (show Measurable fun y => I (x + y) from hIm.comp (measurable_const.add measurable_id))]
    rfl
  simp only [Pi.mul_apply, hin]
  have hF : Measurable fun q : E × E => I q.1 * (ρ (q.1 - q.2) * gauss q.2) :=
    (hIm.comp measurable_fst).mul ((hρ.comp (measurable_fst.sub measurable_snd)).mul
      (measurable_gauss.comp measurable_snd))
  have hG : Measurable fun q : E × E => ρ q.1 * (gauss q.2 * I (q.1 + q.2)) :=
    (hρ.comp measurable_fst).mul ((measurable_gauss.comp measurable_snd).mul hIadd)
  calc ∫⁻ x, ρ x * ∫⁻ u, gauss u * I (x + u) ∂(volume : Measure E) ∂(volume : Measure E)
      = ∫⁻ x, ∫⁻ u, ρ x * (gauss u * I (x + u)) ∂(volume : Measure E) ∂(volume : Measure E) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (ρ x) (show Measurable fun u => gauss u * I (x + u) from
          measurable_gauss.mul (hIm.comp (measurable_const.add measurable_id)))]
    _ = ∫⁻ u, ∫⁻ x, ρ x * (gauss u * I (x + u)) ∂(volume : Measure E) ∂(volume : Measure E) :=
        lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ u, ∫⁻ w, I w * (ρ (w - u) * gauss u) ∂(volume : Measure E) ∂(volume : Measure E) := by
        refine lintegral_congr fun u => ?_
        rw [← lintegral_add_right_eq_self (fun w => I w * (ρ (w - u) * gauss u)) u]
        refine lintegral_congr fun x => ?_
        simp only [add_sub_cancel_right]
        ring
    _ = ∫⁻ w, ∫⁻ u, I w * (ρ (w - u) * gauss u) ∂(volume : Measure E) ∂(volume : Measure E) :=
        (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = ∫⁻ w, A.indicator (gaussSmooth ρ) w ∂(volume : Measure E) := by
        refine lintegral_congr fun w => ?_
        rw [lintegral_const_mul (I w) (show Measurable fun u => ρ (w - u) * gauss u from
          (hρ.comp (measurable_const.sub measurable_id)).mul measurable_gauss)]
        by_cases hw : w ∈ A
        · simp only [hI, Set.indicator_of_mem hw, Pi.one_apply, one_mul, gaussSmooth]
        · simp only [hI, Set.indicator_of_notMem hw, zero_mul]

/-- The characteristic function of the Gaussian measure has no zeros. -/
private theorem charFun_withDensity_gauss_ne_zero (t : E) :
    charFun ((volume : Measure E).withDensity gauss) t ≠ 0 := by
  have hc := gaussConst_pos (E := E)
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul measurable_gauss
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have hpt : ∀ x : E, (gauss x).toReal • Complex.exp (⟪x, t⟫ * Complex.I) =
      ((gaussConst E)⁻¹ : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) * ((‖x‖ : ℂ) ^ 2) + Complex.I * ⟪t, x⟫) := fun x => by
    rw [gauss, ENNReal.toReal_ofReal (div_pos (Real.exp_pos _) hc).le, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_exp, div_eq_inv_mul, mul_assoc, ← Complex.exp_add,
      real_inner_comm]
    congr 3
    · push_cast
      ring
    · ring
  simp_rw [hpt]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num)]
  refine mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne'))
    (mul_ne_zero ?_ (Complex.exp_ne_zero _))
  refine Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
  norm_num [Real.pi_ne_zero]

/-- **Deconvolution.** Two finite-mass functions with the same Gaussian smoothing agree almost
everywhere. -/
private theorem ae_eq_of_gaussSmooth_eq {ρ σ : E → ℝ≥0∞} (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρf : ∫⁻ x, ρ x ∂(volume : Measure E) ≠ ⊤) (hσf : ∫⁻ x, σ x ∂(volume : Measure E) ≠ ⊤)
    (h : ∀ x, gaussSmooth ρ x = gaussSmooth σ x) : ρ =ᵐ[volume] σ := by
  have : IsFiniteMeasure ((volume : Measure E).withDensity ρ) := isFiniteMeasure_withDensity hρf
  have : IsFiniteMeasure ((volume : Measure E).withDensity σ) := isFiniteMeasure_withDensity hσf
  have : IsFiniteMeasure ((volume : Measure E).withDensity gauss) :=
    isFiniteMeasure_withDensity (by rw [lintegral_gauss]; exact ENNReal.one_ne_top)
  have hconv : (volume : Measure E).withDensity ρ ∗ (volume : Measure E).withDensity gauss =
      (volume : Measure E).withDensity σ ∗ (volume : Measure E).withDensity gauss := by
    rw [withDensity_conv_gauss hρ, withDensity_conv_gauss hσ, funext h]
  have hchar : charFun ((volume : Measure E).withDensity ρ) =
      charFun ((volume : Measure E).withDensity σ) := funext fun t => by
    have h1 := congrArg (fun m => charFun m t) hconv
    simp only [charFun_conv] at h1
    exact mul_right_cancel₀ (charFun_withDensity_gauss_ne_zero t) h1
  exact (withDensity_eq_iff hρ.aemeasurable hσ.aemeasurable hρf).mp
    (Measure.ext_of_charFun hchar)

end Deconvolution

section Pointwise

/-- A lower semicontinuous potential that agrees almost everywhere with a convex potential whose
domain has nonempty interior lies below it everywhere. -/
private theorem le_of_ae_eq {χ₁ χ₂ : E → EReal} (hl₁ : LowerSemicontinuous χ₁)
    (h₂ : ConvexPotential χ₂) (hint : (interior {x | χ₂ x ≠ ⊤}).Nonempty)
    (hae : χ₁ =ᵐ[volume] χ₂) (x : E) : χ₁ x ≤ χ₂ x := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc₂, hc₁⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hx : χ₂ x ≠ ⊤ := ne_top_of_lt hc₂
  set f : E → ℝ := fun y => (χ₂ y).toReal with hfdef
  have hfx : χ₂ x = (f x : EReal) := (EReal.coe_toReal hx (h₂.1 x)).symm
  set r := f x with hr
  have hrc : r < c := by rw [hfx] at hc₂; exact_mod_cast hc₂
  -- lower semicontinuity of `χ₁` at `x`
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hl₁ x c hc₁)
  -- a ball around an interior point on which `χ₂` is bounded above
  obtain ⟨x₀, hx₀⟩ := hint
  have hcont : ContinuousAt f x₀ :=
    (h₂.convexOn_toReal.continuousOn_interior x₀ hx₀).continuousAt
      (isOpen_interior.mem_nhds hx₀)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp
    ((hcont.eventually (gt_mem_nhds (lt_add_one (f x₀)))).and
      (isOpen_interior.mem_nhds hx₀))
  set M := f x₀ + 1 with hM
  set K := |M - r| + ‖x₀ - x‖ + δ + 1 with hK
  have hK0 : 0 < K := by positivity
  set η := min (c - r) ε with hη
  have hη0 : 0 < η := lt_min (by linarith) hε
  set s := min (1 / 2) (η / (2 * K)) with hs
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hsK : s * K ≤ η / 2 := by
    have := min_le_right (1 / 2 : ℝ) (η / (2 * K))
    rw [← hs, le_div_iff₀ (by positivity)] at this
    linarith
  set p := s • x₀ + (1 - s) • x with hp
  have hsub : Metric.ball p (s * δ) ⊆ {y | χ₁ y ≠ χ₂ y} := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    set w := s⁻¹ • (y - (1 - s) • x) with hw
    have hyw : y = s • w + (1 - s) • x := by
      rw [hw, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, sub_add_cancel]
    have hwx₀ : ‖w - x₀‖ < δ := by
      have he : w - x₀ = s⁻¹ • (y - p) := by
        rw [hw, hp]
        simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
        abel
      rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0, inv_mul_lt_iff₀ hs0]
      linarith
    obtain ⟨hwM, hwint⟩ := hδball (show dist w x₀ < δ by rwa [dist_eq_norm])
    have hwdom : w ∈ {x | χ₂ x ≠ ⊤} := interior_subset hwint
    have hconv := h₂.convexOn_toReal.2 hwdom hx hs0.le (by linarith : (0 : ℝ) ≤ 1 - s)
      (by ring)
    simp only [smul_eq_mul] at hconv
    rw [← hyw] at hconv
    have hydom : χ₂ y ≠ ⊤ := by
      rw [hyw]
      exact h₂.convex_domain hwdom hx hs0.le (by linarith) (by ring)
    have hfy : f y < c := by
      have h1 : s * f w ≤ s * M := mul_le_mul_of_nonneg_left hwM.le hs0.le
      have h2 : s * (M - r) ≤ s * K := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (by linarith [norm_nonneg (x₀ - x)])) hs0.le
      have h3 : η ≤ c - r := min_le_left _ _
      nlinarith
    have hdist : dist y x < ε := by
      rw [dist_eq_norm, hyw]
      have he : s • w + (1 - s) • x - x = s • (w - x) := by module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      have hwx : ‖w - x‖ ≤ ‖w - x₀‖ + ‖x₀ - x‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (w - x₀) (x₀ - x)
      have h4 : s * ‖w - x‖ ≤ s * K := mul_le_mul_of_nonneg_left
        (hwx.trans (by linarith [abs_nonneg (M - r)])) hs0.le
      have h5 : η ≤ ε := min_le_right _ _
      linarith
    have h₁y : (c : EReal) < χ₁ y := hball hdist
    intro heq
    rw [heq, ← EReal.coe_toReal hydom (h₂.1 y)] at h₁y
    have : c < f y := by exact_mod_cast h₁y
    linarith
  have hpos := (Metric.isOpen_ball (x := p) (ε := s * δ)).measure_pos (volume : Measure E)
    (Metric.nonempty_ball.mpr (mul_pos hs0 hδ))
  exact hpos.ne' (measure_mono_null hsub (ae_iff.mp hae))

end Pointwise

/-- **Equality in the midpoint Prékopa–Leindler inequality for extended-real potentials**
(Dubuc; Cordero-Erausquin–Klartag arXiv:1304.0630v1, proof of Theorem 2, uniqueness). Let
`ψ₀, ψ₁ : E → ℝ ∪ {+∞}` be convex and lower semicontinuous with `∫ e^{-ψ₀} = ∫ e^{-ψ₁} = 1`, and
let `ρ ≥ 0` be Borel with `e^{-ψ₀(x)/2} e^{-ψ₁(y)/2} ≤ ρ((x + y)/2)` for all `x, y` and
`∫ ρ ≤ 1`. Then `ψ₁ = ψ₀(· − y₀)` everywhere, for some `y₀`. -/
theorem exists_eq_translate_of_midpoint_le_of_lintegral_le_one {ψ₀ ψ₁ : E → EReal}
    (hψ₀ : ConvexPotential ψ₀) (hψ₁ : ConvexPotential ψ₁)
    (hl₀ : LowerSemicontinuous ψ₀) (hl₁ : LowerSemicontinuous ψ₁)
    (hn₀ : mass volume ψ₀ = 1) (hn₁ : mass volume ψ₁ = 1)
    {ρ : E → ℝ≥0∞} (hρm : Measurable ρ)
    (hmid : ∀ x y, density ψ₀ x ^ (1 / 2 : ℝ) * density ψ₁ y ^ (1 - 1 / 2 : ℝ) ≤
      ρ ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y))
    (hρ : ∫⁻ z, ρ z ∂(volume : Measure E) ≤ 1) :
    ∃ y₀ : E, ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  have hm₀ : Measurable (density ψ₀) := EReal.measurable_exp.comp hl₀.measurable.neg
  have hm₁ : Measurable (density ψ₁) := EReal.measurable_exp.comp hl₁.measurable.neg
  have hint₀ := interior_domain_nonempty_of_mass_ne_zero volume hψ₀ (by rw [hn₀]; exact one_ne_zero)
  have hint₁ := interior_domain_nonempty_of_mass_ne_zero volume hψ₁ (by rw [hn₁]; exact one_ne_zero)
  have hpos : ∀ {ψ : E → EReal}, ∀ x ∈ interior {x | ψ x ≠ ⊤}, density ψ x ≠ 0 := by
    intro ψ x hx h0
    have hxd : ψ x ≠ ⊤ := interior_subset hx
    rw [density, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff] at h0
    exact hxd h0
  obtain ⟨φ₀, hc₀, hn₀', he₀⟩ := exists_convex_gaussSmooth_eq hm₀
    (fun t ht0 ht1 => density_rpow_mul_le hψ₀ ht0 ht1) hn₀ isOpen_interior hint₀ (hpos (ψ := ψ₀))
  obtain ⟨φ₁, hc₁, hn₁', he₁⟩ := exists_convex_gaussSmooth_eq hm₁
    (fun t ht0 ht1 => density_rpow_mul_le hψ₁ ht0 ht1) hn₁ isOpen_interior hint₁ (hpos (ψ := ψ₁))
  -- the midpoint density of the smoothed potentials is dominated by `ρ ⋆ γ`
  have hmidle : ∀ z, midpointDensity φ₀ φ₁ z ≤ gaussSmooth ρ z := by
    intro z
    refine iSup_le fun a => ?_
    have hPL := gaussSmooth_rpow_mul_le hm₀ hm₁ hρm (t := 1 / 2) (by norm_num) (by norm_num)
      hmid a ((2 : ℝ) • z - a)
    have harg : (1 / 2 : ℝ) • a + (1 - 1 / 2 : ℝ) • ((2 : ℝ) • z - a) = z := by module
    rw [harg, ← he₀, ← he₁, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_add] at hPL
    refine le_trans (le_of_eq ?_) hPL
    congr 2
    ring
  have hmid1 : ∫⁻ z, midpointDensity φ₀ φ₁ z ∂(volume : Measure E) ≤ 1 :=
    (lintegral_mono hmidle).trans (by rw [lintegral_gaussSmooth hρm]; exact hρ)
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_of_lintegral_midpointDensity_le_one hc₀ hc₁ hn₀' hn₁'
    hmid1
  -- the densities agree up to the translation
  set σ : E → ℝ≥0∞ := fun x => density ψ₀ (x - y₀) with hσ
  have hσm : Measurable σ := hm₀.comp (measurable_id.sub_const y₀)
  have hsm : ∀ y, gaussSmooth (density ψ₁) y = gaussSmooth σ y := by
    intro y
    rw [← he₁, hy₀, he₀]
    simp only [gaussSmooth, hσ, sub_right_comm]
  have hfin₁ : ∫⁻ x, density ψ₁ x ∂(volume : Measure E) ≠ ⊤ := by
    change mass volume ψ₁ ≠ ⊤
    rw [hn₁]; exact ENNReal.one_ne_top
  have hfinσ : ∫⁻ x, σ x ∂(volume : Measure E) ≠ ⊤ := by
    rw [hσ, lintegral_sub_right_eq_self (fun x => density ψ₀ x) y₀]
    change mass volume ψ₀ ≠ ⊤
    rw [hn₀]; exact ENNReal.one_ne_top
  have hae := ae_eq_of_gaussSmooth_eq hm₁ hσm hfin₁ hfinσ hsm
  have haeψ : ψ₁ =ᵐ[volume] fun x => ψ₀ (x - y₀) := by
    filter_upwards [hae] with x hx
    have h := EReal.exp_strictMono.injective hx
    exact neg_injective h
  -- the translate is a lower semicontinuous convex potential with full-dimensional domain
  set χ : E → EReal := fun x => ψ₀ (x - y₀) with hχ
  have hχc : ConvexPotential χ := by
    refine ⟨fun x => hψ₀.1 _, ?_⟩
    have hset : {q : E × ℝ | χ q.1 ≤ (q.2 : EReal)} =
        (fun q => q + ((-y₀, 0) : E × ℝ)) ⁻¹' {q : E × ℝ | ψ₀ q.1 ≤ (q.2 : EReal)} := by
      ext q
      change ψ₀ (q.1 - y₀) ≤ (q.2 : EReal) ↔ ψ₀ (q.1 + -y₀) ≤ ((q.2 + 0 : ℝ) : EReal)
      rw [sub_eq_add_neg, add_zero]
    rw [hset]
    exact hψ₀.2.translate_preimage_left _
  have hχl : LowerSemicontinuous χ := hl₀.comp (continuous_id.sub continuous_const)
  have hχint : (interior {x | χ x ≠ ⊤}).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hint₀
    refine ⟨x₀ + y₀, mem_interior_iff_mem_nhds.mpr ?_⟩
    have hc : ContinuousAt (fun x : E => x - y₀) (x₀ + y₀) :=
      (continuous_id.sub continuous_const).continuousAt
    have hn : {x | ψ₀ x ≠ ⊤} ∈ 𝓝 ((x₀ + y₀) - y₀) := by
      rw [add_sub_cancel_right]
      exact mem_interior_iff_mem_nhds.mp hx₀
    exact hc.preimage_mem_nhds hn
  refine ⟨y₀, fun y => le_antisymm ?_ ?_⟩
  · exact le_of_ae_eq hl₁ hχc hχint haeψ y
  · exact le_of_ae_eq hχl hψ₁ hint₁ haeψ.symm y

end FunctionalInequalities.Probability.MomentMeasure
