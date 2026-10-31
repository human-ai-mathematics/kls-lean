module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Integrals of exponential functions on the line

Source: Blueprint `thm:one-dimensional-logconcave-poincare`, supporting calculus. Read
`integral_exp_affine`, `integral_exp_affine_Ioi` and `integral_exp_affine_Iic`.

The chord and tangent bounds of a log-concave density are exponentials `C · exp (κ (s - x₀))`.
This module records their interval integrals and, for the decaying direction, their half-line
integrals with integrability, so that mass bounds of log-concave laws reduce to one-line
computations.

Section `TotalVariation`: for a `C¹` function `g` tending to `+∞`, `∫_{(a, ∞)} g' e^{-g} =
e^{-g(a)}` when `g` is nondecreasing on `(a, ∞)` (`lintegral_Ioi_deriv_mul_exp_neg_eq`), and the
total variation of `e^{-g}` for a convex `g` tending to `+∞` at `±∞` is
`∫ |g'| e^{-g} = 2 e^{-inf g}` (`lintegral_abs_deriv_mul_exp_neg_eq`); this is the one-dimensional
identity in Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, (15).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace FunctionalInequalities.Probability.Line

/-- The antiderivative of `C · exp (κ (s - x₀))`. -/
theorem hasDerivAt_exp_affine {κ : ℝ} (hκ : κ ≠ 0) (C x₀ s : ℝ) :
    HasDerivAt (fun t ↦ C / κ * Real.exp (κ * (t - x₀))) (C * Real.exp (κ * (s - x₀))) s := by
  have h : HasDerivAt (fun t ↦ κ * (t - x₀)) κ s := by
    simpa using ((hasDerivAt_id s).sub_const x₀).const_mul κ
  have h2 := (h.exp).const_mul (C / κ)
  refine h2.congr_deriv ?_
  field_simp

/-- The interval integral of an exponential of an affine argument. -/
theorem integral_exp_affine (C κ x₀ u v : ℝ) (hκ : κ ≠ 0) :
    ∫ s in u..v, C * Real.exp (κ * (s - x₀)) =
      C / κ * (Real.exp (κ * (v - x₀)) - Real.exp (κ * (u - x₀))) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hasDerivAt_exp_affine hκ C x₀ s)
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable _ _)]
  ring

/-- A decaying exponential is integrable on a right half-line. -/
theorem integrableOn_exp_affine_Ioi {C κ : ℝ} (hC : 0 ≤ C) (hκ : κ < 0) (x₀ y : ℝ) :
    IntegrableOn (fun s ↦ C * Real.exp (κ * (s - x₀))) (Ioi y) := by
  have hκ' : κ ≠ 0 := hκ.ne
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t ↦ C / κ * Real.exp (κ * (t - x₀)))
    (l := 0) ?_ (fun s _ ↦ hasDerivAt_exp_affine hκ' C x₀ s) (fun s _ ↦ ?_) ?_
  · exact (hasDerivAt_exp_affine hκ' C x₀ y).continuousAt.continuousWithinAt
  · exact mul_nonneg hC (Real.exp_pos _).le
  · have h : Tendsto (fun t : ℝ ↦ κ * (t - x₀)) atTop atBot := by
      have : Tendsto (fun t : ℝ ↦ t - x₀) atTop atTop :=
        tendsto_atTop_add_const_right _ (-x₀) tendsto_id
      exact Tendsto.const_mul_atTop_of_neg hκ this
    have := (Real.tendsto_exp_atBot.comp h).const_mul (C / κ)
    simpa using this

/-- The right half-line integral of a decaying exponential. -/
theorem integral_exp_affine_Ioi {C κ : ℝ} (hC : 0 ≤ C) (hκ : κ < 0) (x₀ y : ℝ) :
    ∫ s in Ioi y, C * Real.exp (κ * (s - x₀)) = -(C / κ) * Real.exp (κ * (y - x₀)) := by
  have hκ' : κ ≠ 0 := hκ.ne
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t ↦ C / κ * Real.exp (κ * (t - x₀)))
    (m := 0) (hasDerivAt_exp_affine hκ' C x₀ y).continuousAt.continuousWithinAt
    (fun s _ ↦ hasDerivAt_exp_affine hκ' C x₀ s) (integrableOn_exp_affine_Ioi hC hκ x₀ y) ?_]
  · ring
  · have h : Tendsto (fun t : ℝ ↦ κ * (t - x₀)) atTop atBot := by
      have : Tendsto (fun t : ℝ ↦ t - x₀) atTop atTop :=
        tendsto_atTop_add_const_right _ (-x₀) tendsto_id
      exact Tendsto.const_mul_atTop_of_neg hκ this
    have := (Real.tendsto_exp_atBot.comp h).const_mul (C / κ)
    simpa using this

/-- A growing exponential is integrable on a left half-line. -/
theorem integrableOn_exp_affine_Iic {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (x₀ y : ℝ) :
    IntegrableOn (fun s ↦ C * Real.exp (κ * (s - x₀))) (Iic y) := by
  have hκ' : κ ≠ 0 := hκ.ne'
  have hint : IntegrableOn (fun s ↦ C * Real.exp (-κ * (s - -x₀))) (Ioi (-y)) :=
    integrableOn_exp_affine_Ioi hC (neg_neg_iff_pos.mpr hκ) (-x₀) (-y)
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  have := hint.comp_neg
  rw [neg_Ioi, neg_neg] at this
  refine this.congr_fun (fun x _ ↦ ?_) measurableSet_Iio
  simp only
  congr 2
  ring

/-- The left half-line integral of a growing exponential. -/
theorem integral_exp_affine_Iic {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ) (x₀ y : ℝ) :
    ∫ s in Iic y, C * Real.exp (κ * (s - x₀)) = C / κ * Real.exp (κ * (y - x₀)) := by
  have hκ' : κ ≠ 0 := hκ.ne'
  rw [integral_Iic_of_hasDerivAt_of_tendsto (f := fun t ↦ C / κ * Real.exp (κ * (t - x₀)))
    (m := 0) (hasDerivAt_exp_affine hκ' C x₀ y).continuousAt.continuousWithinAt
    (fun s _ ↦ hasDerivAt_exp_affine hκ' C x₀ s) (integrableOn_exp_affine_Iic hC hκ x₀ y) ?_]
  · ring
  · have h : Tendsto (fun t : ℝ ↦ κ * (t - x₀)) atBot atBot := by
      have : Tendsto (fun t : ℝ ↦ t - x₀) atBot atBot :=
        tendsto_atBot_add_const_right _ (-x₀) tendsto_id
      exact Tendsto.const_mul_atBot hκ this
    have := (Real.tendsto_exp_atBot.comp h).const_mul (C / κ)
    simpa using this

section TotalVariation

/-- `∫_{(a, ∞)} g' e^{-g} = e^{-g(a)}` for a `C¹` function `g` nondecreasing on `(a, ∞)` and
tending to `+∞`. -/
theorem lintegral_Ioi_deriv_mul_exp_neg_eq {g : ℝ → ℝ} (hg1 : ContDiff ℝ 1 g) {a : ℝ}
    (hmono : ∀ t ∈ Ioi a, 0 ≤ deriv g t) (htop : Tendsto g atTop atTop) :
    ∫⁻ t in Ioi a, ENNReal.ofReal (deriv g t * Real.exp (-g t)) =
      ENNReal.ofReal (Real.exp (-g a)) := by
  have hderiv : ∀ t ∈ Ici a,
      HasDerivAt (fun s : ℝ => -Real.exp (-g s))
        (deriv g t * Real.exp (-g t)) t := by
    intro t _
    have hgt : HasDerivAt g (deriv g t) t :=
      (hg1.differentiable (by norm_num)).differentiableAt.hasDerivAt
    refine ((Real.hasDerivAt_exp (-g t)).comp t hgt.neg).neg.congr_deriv ?_
    ring
  have hpos : ∀ t ∈ Ioi a, 0 ≤ deriv g t * Real.exp (-g t) := by
    intro t ht
    exact mul_nonneg (hmono t ht) (Real.exp_pos _).le
  have hlim0 :
      Tendsto (fun t : ℝ => Real.exp (-g t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
  have hlim :
      Tendsto (fun t : ℝ => -Real.exp (-g t)) atTop (𝓝 0) := by
    simpa using hlim0.neg
  have hint : IntegrableOn
      (fun t : ℝ => deriv g t * Real.exp (-g t)) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hnonneg :
      ∀ᵐ t ∂(volume.restrict (Ioi a)),
        0 ≤ deriv g t * Real.exp (-g t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpos t ht
  have hintegral :
      ∫ t in Ioi a, deriv g t * Real.exp (-g t) =
        Real.exp (-g a) := by
    simpa using
      (integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg, hintegral]

/-- One-dimensional total variation of `e^{-g}` for a convex `g` tending to `+∞` at `±∞`:
`∫ |g'| e^{-g} = 2 e^{-inf g}` (for `C¹` `g`). -/
theorem lintegral_abs_deriv_mul_exp_neg_eq {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hg1 : ContDiff ℝ 1 g) (htop : Tendsto g atTop atTop) (hbot : Tendsto g atBot atTop) :
    ∫⁻ t, ENNReal.ofReal (|deriv g t| * Real.exp (-g t)) =
      ENNReal.ofReal (2 * Real.exp (-⨅ t, g t)) := by
  obtain ⟨a, ha⟩ :=
    hg1.continuous.exists_forall_le
      (show Tendsto g (cocompact ℝ) atTop by
        rw [cocompact_eq_atBot_atTop]
        exact hbot.sup htop)
  have hbdd : BddBelow (range g) := by
    refine ⟨g a, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact ha t
  have hinf : (⨅ t, g t) = g a := le_antisymm (ciInf_le hbdd a) (le_ciInf ha)
  have hlocal : IsLocalMin g a := Filter.Eventually.of_forall ha
  have hzero : deriv g a = 0 := hlocal.deriv_eq_zero
  have hd : Differentiable ℝ g := hg1.differentiable (by norm_num)
  have hmono := hg.monotoneOn_deriv fun x _ => hd x
  have hnonneg (t : ℝ) (ht : t ∈ Ioi a) : 0 ≤ deriv g t :=
    hzero ▸ hmono (mem_univ a) (mem_univ t) (le_of_lt ht)
  have hnonpos (t : ℝ) (ht : t ∈ Iio a) : deriv g t ≤ 0 :=
    hzero ▸ hmono (mem_univ t) (mem_univ a) (le_of_lt ht)
  have hdneg (t : ℝ) : deriv (fun s : ℝ => g (-s)) t = -deriv g (-t) := by
    simpa only [Function.comp_def, mul_neg_one] using
      ((hd (-t)).hasDerivAt.comp t (hasDerivAt_id t).neg).deriv
  have hneg_nonneg (t : ℝ) (ht : t ∈ Ioi (-a)) : 0 ≤ deriv (fun s : ℝ => g (-s)) t := by
    rw [hdneg]
    exact neg_nonneg.mpr (hnonpos (-t) (by simp only [mem_Iio, mem_Ioi] at ht ⊢; linarith))
  let F : ℝ → ENNReal := fun t => ENNReal.ofReal (|deriv g t| * Real.exp (-g t))
  have hderivcont : Continuous (deriv g) := hg1.continuous_deriv (by norm_num)
  have hF : Measurable F :=
    (ENNReal.continuous_ofReal.comp
        (hderivcont.abs.mul (Real.continuous_exp.comp hg1.continuous.neg))).measurable
  have hright : (∫⁻ t in Ioi a, F t) = ENNReal.ofReal (Real.exp (-g a)) := by
    calc
      (∫⁻ t in Ioi a, F t) = ∫⁻ t in Ioi a, ENNReal.ofReal (deriv g t * Real.exp (-g t)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only [F]
        rw [abs_of_nonneg (hnonneg t ht)]
      _ = _ := lintegral_Ioi_deriv_mul_exp_neg_eq hg1 hnonneg htop
  have hneg_integral :=
    lintegral_Ioi_deriv_mul_exp_neg_eq (g := fun t : ℝ => g (-t)) (a := -a)
      (hg1.comp contDiff_neg) hneg_nonneg (hbot.comp tendsto_neg_atTop_atBot)
  have hreflect : (∫⁻ t in Ioi (-a), F (-t)) = ∫⁻ t in Iio a, F t := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Iio]
    calc
      (∫⁻ t, (Ioi (-a)).indicator (fun t => F (-t)) t) = ∫⁻ t, ((Iio a).indicator F) (-t) := by
        apply lintegral_congr
        intro t
        have hi : t ∈ Ioi (-a) ↔ -t ∈ Iio a := by
          simp only [mem_Ioi, mem_Iio]
          constructor <;> intro ht <;> linarith
        by_cases ht : t ∈ Ioi (-a)
        · rw [indicator_of_mem ht, indicator_of_mem (hi.mp ht)]
        · rw [indicator_of_notMem ht, indicator_of_notMem (fun h => ht (hi.mpr h))]
      _ = ∫⁻ t, (Iio a).indicator F t ∂(Measure.map (fun t : ℝ => -t) volume) := by
        exact (lintegral_map (hF.indicator measurableSet_Iio) measurable_neg).symm
      _ = _ := by rw [(Measure.measurePreserving_neg (volume : Measure ℝ)).map_eq]
  have hleft : (∫⁻ t in Iio a, F t) = ENNReal.ofReal (Real.exp (-g a)) := by
    calc
      (∫⁻ t in Iio a, F t) = ∫⁻ t in Ioi (-a), F (-t) := hreflect.symm
      _ =
          ∫⁻ t in Ioi (-a),
            ENNReal.ofReal (deriv (fun s : ℝ => g (-s)) t * Real.exp (-g (-t))) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht' : -t ∈ Iio a := by
          change -t < a
          change -a < t at ht
          linarith
        dsimp only [F]
        rw [hdneg, abs_of_nonpos (hnonpos (-t) ht')]
      _ = _ := by simpa only [neg_neg] using hneg_integral
  have hic : (∫⁻ t in Iic a, F t) = ∫⁻ t in Iio a, F t := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Iio]
    apply lintegral_congr
    intro t
    by_cases hta : t < a
    · rw [indicator_of_mem (show t ∈ Iic a from hta.le),
        indicator_of_mem (show t ∈ Iio a from hta)]
    · by_cases heq : t = a
      · subst t
        simp [F, hzero]
      · have hgt : a < t := lt_of_le_of_ne (not_lt.mp hta) (Ne.symm heq)
        rw [indicator_of_notMem (show t ∉ Iic a from not_le.mpr hgt),
          indicator_of_notMem (show t ∉ Iio a from hta)]
  have hsplit : (∫⁻ t in Iic a, F t) + (∫⁻ t in Ioi a, F t) = ∫⁻ t, F t := by
    simpa only [compl_Iic] using (lintegral_add_compl F measurableSet_Iic)
  change (∫⁻ t, F t) = _
  calc
    (∫⁻ t, F t) = (∫⁻ t in Iic a, F t) + (∫⁻ t in Ioi a, F t) := hsplit.symm
    _ = ENNReal.ofReal (Real.exp (-g a)) + ENNReal.ofReal (Real.exp (-g a)) := by
      rw [hic, hleft, hright]
    _ = ENNReal.ofReal (2 * Real.exp (-g a)) := by
      rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal (2 * Real.exp (-⨅ t, g t)) := by rw [hinf]

end TotalVariation

end FunctionalInequalities.Probability.Line
