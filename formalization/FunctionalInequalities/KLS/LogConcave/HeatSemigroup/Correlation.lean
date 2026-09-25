import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Perimeter
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

/-!
# Indicator heat correlation and L1 displacement

For the actual Markov heat operator of a full-dimensional log-concave law, the L1 displacement
of an indicator equals twice its loss of uncentered heat correlation. This identity includes
zero and full mass, and all nonnegative times. It is the algebraic interface between the
spectral decay estimate and small-time perimeter estimate.
-/

open MeasureTheory Set InnerProductSpace
open scoped ContDiff
noncomputable section
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- Indicator L1 displacement equals twice the loss of uncentered heat correlation. -/
theorem integral_abs_indicator_sub_operator_eq_correlation
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    let χ := indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
    let g := operator m B hν hi ht χ
    (∫ x, |D.indicator (1 : V → ℝ) x - g x| ∂(ν : Measure V)) =
      2 * ((ν : Measure V).real D - inner ℝ χ g) := by
  dsimp
  let χ : Lp ℝ 2 (ν : Measure V) :=
    indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
  let g := operator m B hν hi ht χ
  have hχae : (χ : V → ℝ) =ᵐ[(ν : Measure V)] D.indicator (1 : V → ℝ) :=
    indicatorConstLp_coeFn
  have hχ0 : (0 : Lp ℝ 2 (ν : Measure V)) ≤ χ := by
    apply (Lp.coeFn_le (0 : Lp ℝ 2 (ν : Measure V)) χ).mp
    filter_upwards [Lp.coeFn_zero ℝ 2 (ν : Measure V), hχae] with x hz hx
    rw [hz, hx]
    exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) x
  have hχ1 : χ ≤ L2.const ν 1 := by
    apply (Lp.coeFn_le χ (L2.const ν 1)).mp
    filter_upwards [hχae, L2.const_coeFn ν 1] with x hx hc
    rw [hx, hc]
    by_cases hxs : x ∈ D
    · simp [Set.indicator_of_mem hxs]
    · simp [Set.indicator_of_notMem hxs]
  have hmarkov := HeatSemigroup.subMarkov m B hν hi ht hχ0 hχ1
  have hg0 : 0 ≤ᵐ[(ν : Measure V)] (g : V → ℝ) := by
    filter_upwards [(Lp.coeFn_le (0 : Lp ℝ 2 (ν : Measure V)) g).mpr hmarkov.1,
      Lp.coeFn_zero ℝ 2 (ν : Measure V)] with x hx hz
    simpa only [hz, Pi.zero_apply] using hx
  have hg1 : (g : V → ℝ) ≤ᵐ[(ν : Measure V)] (L2.const ν 1 : V → ℝ) :=
    (Lp.coeFn_le g (L2.const ν 1)).mpr hmarkov.2
  have hpoint : ∀ᵐ x ∂(ν : Measure V),
      |D.indicator (1 : V → ℝ) x - g x| =
        D.indicator (fun x => 1 - g x) x + Dᶜ.indicator g x := by
    filter_upwards [hg0, hg1, L2.const_coeFn ν 1] with x hx0 hx1 hc
    rw [hc] at hx1
    by_cases hx : x ∈ D
    · have hxc : x ∉ Dᶜ := by simpa using hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_notMem hxc, Pi.one_apply, add_zero]
      rw [abs_of_nonneg (by linarith)]
    · simp only [Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_compl hx), zero_add,
        zero_sub, abs_neg]
      simpa only [Pi.zero_apply] using abs_of_nonneg hx0
  have hgI : Integrable (g : V → ℝ) (ν : Measure V) :=
    (Lp.memLp g).integrable one_le_two
  have hsubI : Integrable (fun x : V => 1 - g x) (ν : Measure V) :=
    (integrable_const (1 : ℝ)).sub hgI
  have hrightI : Integrable (D.indicator (fun x => 1 - g x)) (ν : Measure V) :=
    hsubI.indicator hD
  have hleftI : Integrable (Dᶜ.indicator (g : V → ℝ)) (ν : Measure V) :=
    hgI.indicator hD.compl
  rw [integral_congr_ae hpoint, integral_add hrightI hleftI,
    integral_indicator hD, integral_indicator hD.compl]
  have hmean : (∫ x, g x ∂(ν : Measure V)) = (ν : Measure V).real D := by
    rw [HeatSemigroup.integral m B hν hi ht χ]
    rw [integral_congr_ae hχae]
    exact integral_indicator_one hD
  have hcomp := integral_add_compl hD hgI
  have hchi : inner ℝ χ g = ∫ x in D, g x ∂(ν : Measure V) := by
    exact MeasureTheory.L2.inner_indicatorConstLp_one hD (measure_ne_top (ν : Measure V) D) g
  rw [integral_sub (integrable_const _) hgI.integrableOn,
      setIntegral_const, hchi]
  simp only [smul_eq_mul, mul_one] at *
  linarith [hcomp, hmean]

/-- The same L1 displacement is the loss of centered indicator correlation from its initial
variance. This is the form directly consumed by the spectral estimate. -/
theorem integral_abs_indicator_sub_operator_eq_center_correlation
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    let χ := indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
    (∫ x, |D.indicator (1 : V → ℝ) x -
      operator m B hν hi ht χ x| ∂(ν : Measure V)) =
      2 * ((ν : Measure V).real D * (1 - (ν : Measure V).real D) -
        inner ℝ (L2.center ν χ) (operator m B hν hi ht (L2.center ν χ))) := by
  dsimp
  let χ : Lp ℝ 2 (ν : Measure V) :=
    indicatorConstLp 2 hD (measure_ne_top (ν : Measure V) D) (1 : ℝ)
  have hχae : (χ : V → ℝ) =ᵐ[(ν : Measure V)] D.indicator (1 : V → ℝ) :=
    indicatorConstLp_coeFn
  have hχmean : L2.mean ν χ = (ν : Measure V).real D := by
    rw [L2.mean_eq_integral]
    rw [integral_congr_ae hχae]
    exact integral_indicator_one hD
  have hcenter := center_operator m B hν hi ht χ
  have hmean := HeatSemigroup.mean m B hν hi ht χ
  have hinner := L2.inner_center_center ν χ (operator m B hν hi ht χ)
  rw [hcenter, hmean, hχmean] at hinner
  rw [integral_abs_indicator_sub_operator_eq_correlation m B hν hi hD ht]
  rw [hinner]
  ring

/-- A finite upper bound on the literature Poincare constant forces a quantitative L1
displacement of every indicator under the actual unit-gradient heat flow. -/
theorem two_mul_variance_decay_le_integral_abs_indicator_sub_operator
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {D : Set V} (hD : MeasurableSet D) {t : ℝ} (ht : 0 ≤ t) :
    2 * (1 - Real.exp (-t / (C : ℝ))) *
      ((ν : Measure V).real D * (1 - (ν : Measure V).real D)) ≤
      ∫ x, |D.indicator (1 : V → ℝ) x -
        operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          (indicatorConstLp 2 hD (measure_ne_top _ _) (1 : ℝ)) x| ∂(ν : Measure V) := by
  have hcorr := inner_center_indicator_le_exp_of_literature_le m hν hi C hC hLit hD ht
  have hident := integral_abs_indicator_sub_operator_eq_center_correlation
    m (ContinuousLinearMap.id ℝ V) hν hi hD ht
  dsimp at hcorr hident
  rw [hident]
  nlinarith

include hν hi in
/-- The smooth convex model's pi-coefficient heat bound combines with literature Poincare
decay to control the mass balance by relative perimeter. -/
theorem two_mul_variance_decay_le_pi_perimeter
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (D : SmoothDomain V)
    (hP : relativePerimeter ρ (interior (ν : Measure V).support) D ≠ ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    2 * (1 - Real.exp (-t / (C : ℝ))) *
      ((ν : Measure V).real D.carrier * (1 - (ν : Measure V).real D.carrier)) ≤
      (2 * Real.sqrt (t / Real.pi)) *
        (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal := by
  exact (two_mul_variance_decay_le_integral_abs_indicator_sub_operator m hν hi
    C hC hLit D.isOpen.measurableSet ht).trans
      (integral_abs_indicator_sub_operator_le_pi m hν hi hνU hU hconv hρ D hP ht)

private theorem exp_neg_five_four_le :
    Real.exp (-(5 / 4 : ℝ)) ≤ (24576 / 85621 : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5 / 4 by norm_num) 6
  have hs' : (85621 / 24576 : ℝ) ≤ Real.exp (5 / 4) := by
    convert hs using 1
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [Real.exp_neg]
  calc
    (Real.exp (5 / 4 : ℝ))⁻¹ ≤ (85621 / 24576 : ℝ)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hs'
    _ = _ := by norm_num

/-- The fixed heat time `5C/4` supplies the numerical coefficient needed for `pi` Buser:
`2 sqrt(5/4) ≤ pi (1 - exp(-5/4))`. -/
theorem pi_heat_scalar :
    2 * Real.sqrt (5 / 4 : ℝ) ≤ Real.pi * (1 - Real.exp (-(5 / 4 : ℝ))) := by
  have he := exp_neg_five_four_le
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_d2]
  have hroot : Real.sqrt (5 / 4 : ℝ) ≤ (11181 / 10000 : ℝ) := by
    have hn := Real.sqrt_nonneg (5 / 4 : ℝ)
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 / 4 by norm_num)
    nlinarith
  have hfactor : (0 : ℝ) ≤ 1 - Real.exp (-(5 / 4 : ℝ)) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hp hfactor]

private theorem two_sqrt_time_le (C : ℝ) (hC : 0 < C) :
    2 * Real.sqrt (((5 / 4 : ℝ) * C) / Real.pi) ≤
      (1 - Real.exp (-(5 / 4 : ℝ))) * Real.sqrt (Real.pi * C) := by
  let a := 1 - Real.exp (-(5 / 4 : ℝ))
  let q := Real.sqrt (5 / 4 : ℝ)
  let p := Real.sqrt Real.pi
  let s := Real.sqrt C
  have hp : 0 < p := Real.sqrt_pos.2 Real.pi_pos
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have h1 : Real.sqrt (((5 / 4 : ℝ) * C) / Real.pi) = q * s / p := by
    rw [Real.sqrt_div (mul_nonneg (by norm_num) hC.le),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 4)]
  have h2 : Real.sqrt (Real.pi * C) = p * s := by
    rw [Real.sqrt_mul Real.pi_pos.le]
  rw [h1, h2]
  have hbound := mul_le_mul_of_nonneg_right pi_heat_scalar hs
  have hbound' := div_le_div_of_nonneg_right hbound hp.le
  have heq : Real.pi * a * s / p = a * (p * s) := by
    dsimp [a]
    rw [← hp2]
    field_simp
  calc
    2 * (q * s / p) = (2 * q * s) / p := by ring
    _ ≤ Real.pi * a * s / p := hbound'
    _ = _ := heq

private theorem min_mass_le_two_variance (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    min p (1 - p) ≤ 2 * p * (1 - p) := by
  rcases le_total p (1 - p) with h | h
  · rw [min_eq_left h]
    have hx : 0 ≤ p * (1 - 2 * p) := mul_nonneg hp0 (by linarith)
    nlinarith
  · rw [min_eq_right h]
    have hx : 0 ≤ (1 - p) * (2 * p - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith

include hν hi in
/-- Smooth convex tilted laws satisfy the pi-coefficient perimeter lower bound at every
finite literature Poincare upper bound. Zero and full-mass domains are included. -/
theorem min_mass_le_sqrt_pi_mul_perimeter
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ univ U)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ)
    (D : SmoothDomain V)
    (hP : relativePerimeter ρ (interior (ν : Measure V).support) D ≠ ⊤) :
    min ((ν : Measure V).real D.carrier) (1 - (ν : Measure V).real D.carrier) ≤
      Real.sqrt (Real.pi * (C : ℝ)) *
        (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal := by
  let c : ℝ := C
  let t : ℝ := (5 / 4) * c
  let p : ℝ := (ν : Measure V).real D.carrier
  let a : ℝ := 1 - Real.exp (-(5 / 4 : ℝ))
  let P : ℝ := (relativePerimeter ρ (interior (ν : Measure V).support) D).toReal
  have hc : 0 < c := by exact_mod_cast hC
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hraw := two_mul_variance_decay_le_pi_perimeter m hν hi hνU hU hconv
    C hC hLit hρ D hP ht
  have htime : -t / c = -(5 / 4 : ℝ) := by
    dsimp [t]
    field_simp
  rw [htime] at hraw
  have hscale := two_sqrt_time_le c hc
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hscaled := mul_le_mul_of_nonneg_right hscale hP0
  have ha : 0 < a := by
    dsimp [a]
    have he := exp_neg_five_four_le
    linarith
  have hchain : a * (2 * p * (1 - p)) ≤ a * (Real.sqrt (Real.pi * c) * P) := by
    dsimp [a, p, P, t, c] at hraw hscaled ⊢
    nlinarith [hraw, hscaled]
  have hmid : 2 * p * (1 - p) ≤ Real.sqrt (Real.pi * c) * P :=
    le_of_mul_le_mul_left hchain ha
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [← probReal_univ (μ := (ν : Measure V))]
    exact measureReal_mono (subset_univ _)
  exact (min_mass_le_two_variance p hp0 hp1).trans hmid

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
