import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.PoissonIterate.Criterion
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Nonvacuity of BKL Theorem 3.1: the standard Gaussian on `ℝ¹`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Theorem 3.1, is formalized as
`KLS.RegularPotential.poincare_le_of_taylor` (`HeatSemigroup/PoissonIterate/Criterion.lean`). This
module shows that its hypotheses are jointly satisfiable in positive dimension: for the standard
Gaussian `γ = volume.tilted (-‖·‖²/2)` on `ℝ¹ = EuclideanSpace ℝ (Fin 1)` every hypothesis is
discharged, with the explicit Taylor constant `R = 8`.

## What is proved

For every finite-dimensional real inner product space `E`:

* `regularPotential_half_norm_sq`: `‖x‖²/2` is a regular potential (BKL (12)) with `a = b = 1`
  (temperate growth, Hessian form exactly `‖v‖²`);
* `integral_exp_inner_tilted_half_norm_sq`: the moment generating function
  `∫ e^{⟪z, x⟫} dγ = e^{‖z‖²/2}`, from Mathlib's complex Gaussian integral;
* `integral_id_tilted_half_norm_sq` and `integral_inner_sq_tilted_half_norm_sq`: `γ` is centered
  and `∫ ⟪v, x⟫² dγ = ‖v‖²`, the first two derivatives of the moment generating function at `0`.

On `ℝ¹`:

* `norm_iteratedFDeriv_exp_neg_half_norm_sq_le`: `‖∇^j e^{-‖z‖²/2}(0)‖ ≤ j!`, through the Hermite
  polynomials (`d^j/dt^j e^{-t²/2} = (-1)^j He_j(t) e^{-t²/2}`, `|He_j(0)| ≤ (j-1)!!`);
* `norm_iteratedFDeriv_integral_exp_inner_smul_tilted_half_norm_sq_le`: the numerator
  `N(z) = ∫ e^{⟪z, x⟫} f(x) dγ` has `‖∇^k N(0)‖ ≤ 4 k! ‖f‖_{L²(γ)}`;
* `norm_taylorTensor_tilted_half_norm_sq_le`: `‖T_d f‖ ≤ 4 (d + 1) ‖f‖_{L²(γ)}` (operator norm);
* `norm_coordTensor_taylorTensor_tilted_half_norm_sq_le`: (29) with `R = 8` in the
  Hilbert–Schmidt norm of the standard basis;
* `gaussian_taylor_hypotheses` and `gaussian_poincare_le_of_taylor_witness`: all hypotheses of
  Theorem 3.1 for `n = 1`, `V = ‖·‖²/2`, `a = b = 1`, `R = 8`, and its conclusion
  `C_P(γ) ≤ K · 8²` obtained from the library theorem.

## The argument

By the moment generating function, `F_f(z) = e^{-‖z‖²/2} N(z)` (`tiltAverage_eq_mul`). The
derivatives of `N` at `0` are the moments `∫ f ∏ ⟪x, h_j⟫ dγ`
(`iteratedFDeriv_integral_exp_inner_smul`); with `‖x‖^k ≤ k! e^{‖x‖}` and Cauchy–Schwarz they are
at most `k! ‖e^{‖x‖}‖_{L²(γ)} ‖f‖₂`, and in dimension one `e^{2‖x‖} ≤ e^{2x₁} + e^{-2x₁}` gives
`∫ e^{2‖x‖} dγ ≤ 2e² ≤ 16`. The Leibniz rule with `binom(d, i) i! (d-i)! = d!` gives
`‖∇^d F_f(0)‖ ≤ 4 (d + 1) d! ‖f‖₂`, hence `‖T_d f‖ ≤ 4 (d + 1) ‖f‖₂ ≤ 8^d ‖f‖₂` for `d ≥ 1`; in
dimension one the coefficient array has one entry, so its norm is at most the operator norm.

## What this is not

The constant `R = 8` is not optimized (the sharp bound is `‖T_d f‖ ≤ ‖f‖₂ / √(d!)`, by Hermite
orthogonality). The Taylor bound is proved only on `ℝ¹`: the moment bound `∫ e^{2‖x‖} dγ ≤ 16`
is dimension-dependent, and no dimension-free instance of (29) is claimed. The witness is a
nonvacuity check of the hypotheses of Theorem 3.1; it gives no new information on the Gaussian
(whose Poincaré constant is `1` by Bakry–Émery) and is not a step towards the KLS bound.

Placement: `KLS/LogConcave/` next to `Regular.lean`, whose `RegularPotential` structure and law it
instantiates; it consumes `PoissonIterate/Criterion.lean` and is not imported by the route.
-/

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff Nat

namespace FunctionalInequalities.KLS

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem hasFDerivAt_half_norm_sq (y : E) :
    HasFDerivAt (fun x : E => ‖x‖ ^ 2 / 2) (innerSL ℝ y) y := by
  have h : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (2 • innerSL ℝ y) y := by
    simpa using (hasFDerivAt_id y).norm_sq
  have hf : (fun x : E => ‖x‖ ^ 2 / 2) = fun x => 1 / 2 * ‖x‖ ^ 2 := by
    funext x
    ring
  have hL : innerSL ℝ y = (1 / 2 : ℝ) • (2 • innerSL ℝ y) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num
  rw [hf, hL]
  exact h.const_mul (1 / 2 : ℝ)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Hessian form of `‖x‖² / 2` is `‖v‖²`. -/
theorem bilinearIteratedFDerivTwo_half_norm_sq (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun x : E => ‖x‖ ^ 2 / 2) x v v = ‖v‖ ^ 2 := by
  have hc : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2 / 2) :=
    (contDiff_norm_sq ℝ).div_const 2
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hc x v v]
  have hfun : (fun y : E => fderiv ℝ (fun x : E => ‖x‖ ^ 2 / 2) y v) = fun y => ⟪v, y⟫ := by
    funext y
    rw [(hasFDerivAt_half_norm_sq y).fderiv, innerSL_apply_apply, real_inner_comm]
  rw [hfun]
  change (fderiv ℝ (innerSL ℝ v) x) v = _
  rw [((innerSL ℝ v).hasFDerivAt (x := x)).fderiv, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The standard Gaussian potential is regular** (BKL (12)) with `a = b = 1`. -/
theorem regularPotential_half_norm_sq : RegularPotential (fun x : E => ‖x‖ ^ 2 / 2) 1 1 where
  temperate := by
    have h := (Function.hasTemperateGrowth_norm_sq E).mul
      (Function.HasTemperateGrowth.const (1 / 2 : ℝ))
    have hf : (fun x : E => ‖x‖ ^ 2 / 2) = (fun x : E => ‖x‖ ^ 2) * fun _ => (1 / 2 : ℝ) := by
      funext x
      simp [div_eq_mul_inv]
    rw [hf]
    exact h
  pos := one_pos
  lower x v := by rw [bilinearIteratedFDerivTwo_half_norm_sq, one_mul]
  upper x v := by rw [bilinearIteratedFDerivTwo_half_norm_sq, one_mul]

omit [CompleteSpace E] in
/-- The Gaussian integral `∫ e^{-‖x‖²/2 + ⟪z, x⟫} dx` as a complex number. -/
private theorem ofReal_integral_exp_gaussian (z : E) :
    ((∫ x, Real.exp (-(‖x‖ ^ 2 / 2) + ⟪z, x⟫) : ℝ) : ℂ) =
      (Real.pi / (1 / 2 : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (‖z‖ ^ 2 / 2) := by
  have hb : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := E) hb 1 z
  calc ((∫ x, Real.exp (-(‖x‖ ^ 2 / 2) + ⟪z, x⟫) : ℝ) : ℂ)
      = ∫ x, ((Real.exp (-(‖x‖ ^ 2 / 2) + ⟪z, x⟫) : ℝ) : ℂ) := integral_complex_ofReal.symm
    _ = ∫ v : E, Complex.exp (-(1 / 2) * ‖v‖ ^ 2 + 1 * ⟪z, v⟫) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Complex.ofReal_exp]
      push_cast
      ring_nf
    _ = _ := by
      rw [h]
      ring_nf

omit [CompleteSpace E] in
/-- **Moment generating function of the standard Gaussian**:
`∫ e^{⟪z, x⟫} dγ = e^{‖z‖²/2}` for `γ = volume.tilted (-‖·‖²/2)`. -/
theorem integral_exp_inner_tilted_half_norm_sq (z : E) :
    ∫ x, Real.exp ⟪z, x⟫ ∂((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) =
      Real.exp (‖z‖ ^ 2 / 2) := by
  rw [integral_tilted]
  simp only [Pi.neg_apply, smul_eq_mul]
  have hnum : (∫ x : E, Real.exp (-(‖x‖ ^ 2 / 2)) / (∫ y : E, Real.exp (-(‖y‖ ^ 2 / 2))) *
      Real.exp ⟪z, x⟫) =
      (∫ x : E, Real.exp (-(‖x‖ ^ 2 / 2) + ⟪z, x⟫)) / (∫ y : E, Real.exp (-(‖y‖ ^ 2 / 2))) := by
    rw [← integral_div]
    congr 1
    funext x
    rw [Real.exp_add]
    ring
  rw [hnum]
  have h0 := ofReal_integral_exp_gaussian (E := E) 0
  simp only [inner_zero_left, add_zero, norm_zero] at h0
  have hz := ofReal_integral_exp_gaussian (E := E) z
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, hz, h0, Complex.ofReal_exp]
  have hne : (Real.pi / (1 / 2 : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro h
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact this (by simpa using h.1)
  push_cast
  field_simp
  simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem hasFDerivAt_exp_half_norm_sq (y : E) :
    HasFDerivAt (fun z : E => Real.exp (‖z‖ ^ 2 / 2))
      (Real.exp (‖y‖ ^ 2 / 2) • innerSL ℝ y) y :=
  (hasFDerivAt_half_norm_sq y).exp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem contDiff_exp_half_norm_sq :
    ContDiff ℝ ∞ (fun z : E => Real.exp (‖z‖ ^ 2 / 2)) :=
  ContDiff.exp ((contDiff_norm_sq ℝ).div_const 2)

omit [CompleteSpace E] in
/-- The moment generating function in the form of the Laplace integrals of
`Analysis/BakryEmery/Tilt/SquareIntegrable.lean`. -/
private theorem laplace_one_eq :
    (fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ)
        ∂((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2))) =
      fun z : E => Real.exp (‖z‖ ^ 2 / 2) := by
  funext z
  simp only [smul_eq_mul, mul_one]
  exact integral_exp_inner_tilted_half_norm_sq z

/-- Every direction moment `∫ ∏ ⟪x, h_j⟫ dγ` is the `d`-th derivative of `e^{‖z‖²/2}` at `0`. -/
private theorem integral_prod_inner_eq (d : ℕ) (h : Fin d → E) :
    ∫ x, ∏ j, ⟪x, h j⟫ ∂((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) =
      iteratedFDeriv ℝ d (fun z : E => Real.exp (‖z‖ ^ 2 / 2)) 0 h := by
  have hV := regularPotential_half_norm_sq (E := E)
  have H := iteratedFDeriv_integral_exp_inner_smul
    ((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) (g := fun _ => (1 : ℝ))
    aestronglyMeasurable_const (fun r => by simpa using hV.integrable_exp_mul_norm r) d 0 h
  rw [laplace_one_eq] at H
  rw [H]
  simp

/-- **The standard Gaussian is centered**: `∫ x dγ = 0`. -/
theorem integral_id_tilted_half_norm_sq :
    ∫ x, x ∂((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) = 0 := by
  have hV := regularPotential_half_norm_sq (E := E)
  have hint : Integrable (fun x : E => x)
      ((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) := by
    refine (hV.integrable_exp_mul_norm 1).mono' continuous_id.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [one_mul]
    linarith [Real.add_one_le_exp ‖x‖]
  apply ext_inner_left ℝ
  intro h
  rw [← integral_inner hint, inner_zero_right]
  have H := integral_prod_inner_eq (E := E) 1 (fun _ => h)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] at H
  simp_rw [real_inner_comm _ h]
  rw [H, iteratedFDeriv_one_apply, (hasFDerivAt_exp_half_norm_sq (0 : E)).fderiv]
  simp

/-- **The standard Gaussian has identity covariance**: `∫ ⟪v, x⟫² dγ = ‖v‖²`. -/
theorem integral_inner_sq_tilted_half_norm_sq (v : E) :
    ∫ x, ⟪v, x⟫ ^ 2 ∂((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) = ‖v‖ ^ 2 := by
  have H := integral_prod_inner_eq (E := E) 2 ![v, v]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at H
  have hsq : (fun x : E => ⟪v, x⟫ ^ 2) = fun x => ⟪x, v⟫ * ⟪x, v⟫ := by
    funext x
    rw [real_inner_comm, sq]
  rw [hsq, H, ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_fderiv_apply
      (contDiff_exp_half_norm_sq.of_le (WithTop.coe_le_coe.mpr le_top))]
  have hfun : (fun y : E => fderiv ℝ (fun z : E => Real.exp (‖z‖ ^ 2 / 2)) y v) =
      fun y => Real.exp (‖y‖ ^ 2 / 2) * ⟪v, y⟫ := by
    funext y
    rw [(hasFDerivAt_exp_half_norm_sq y).fderiv]
    simp [real_inner_comm]
  have hd : HasFDerivAt (fun y : E => Real.exp (‖y‖ ^ 2 / 2) * ⟪v, y⟫)
      (Real.exp (‖(0 : E)‖ ^ 2 / 2) • innerSL ℝ v +
        ⟪v, (0 : E)⟫ • (Real.exp (‖(0 : E)‖ ^ 2 / 2) • innerSL ℝ (0 : E))) 0 :=
    (hasFDerivAt_exp_half_norm_sq (0 : E)).mul ((innerSL ℝ v).hasFDerivAt)
  rw [hfun, hd.fderiv]
  simp

omit [CompleteSpace E] in
private theorem integrable_exp_inner_tilted_half_norm_sq (w : E) :
    Integrable (fun x => Real.exp ⟪w, x⟫)
      ((volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2)) := by
  refine ((regularPotential_half_norm_sq (E := E)).integrable_exp_mul_norm ‖w‖).mono'
    (by fun_prop : Continuous fun x : E => Real.exp ⟪w, x⟫).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (real_inner_le_norm w x)

end General

/-! ### The derivatives of `e^{-t²/2}` at `0` -/

/-- `|d^j/dt^j e^{-t²/2}|_{t=0}| ≤ j!`: the value is `±He_j(0)`, which is `0` for odd `j` and
`±(j-1)!!` for even `j`. -/
private theorem abs_iteratedDeriv_gaussian_zero_le (j : ℕ) :
    |iteratedDeriv j (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) 0| ≤ j ! := by
  rw [iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian,
    ← Polynomial.coeff_zero_eq_aeval_zero']
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
    Real.exp_zero, mul_one, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, eq_intCast]
  rcases Nat.even_or_odd j with hj | hj
  · rw [Polynomial.coeff_hermite_of_even_add (by simpa using hj)]
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, abs_mul, abs_pow, abs_neg,
      abs_one, one_pow, one_mul, Nat.abs_cast]
    exact_mod_cast (Nat.doubleFactorial_le_factorial _).trans (Nat.factorial_le (Nat.sub_le _ _))
  · rw [Polynomial.coeff_hermite_of_odd_add (by simpa using hj)]
    simp only [Int.cast_zero, abs_zero]
    positivity

/-! ### The standard Gaussian on `ℝ¹` -/

section One

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

local notation "γ₁" =>
  Measure.tilted (volume : Measure (EuclideanSpace ℝ (Fin 1)))
    (-fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ 2 / 2)

/-- In dimension one, `‖x‖ = |⟪e₁, x⟫|`. -/
private theorem norm_eq_abs_inner_basisFun (x : ℝ¹) :
    ‖x‖ = |⟪EuclideanSpace.basisFun (Fin 1) ℝ 0, x⟫| := by
  set e := EuclideanSpace.basisFun (Fin 1) ℝ 0
  have hx : ⟪e, x⟫ • e = x := by
    simpa [e] using (EuclideanSpace.basisFun (Fin 1) ℝ).sum_repr' x
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 0
  conv_lhs => rw [← hx]
  rw [norm_smul, he, mul_one, Real.norm_eq_abs]

/-- `‖∇^j e^{-‖z‖²/2}(0)‖ ≤ j!` on `ℝ¹`. -/
theorem norm_iteratedFDeriv_exp_neg_half_norm_sq_le (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ¹ => Real.exp (-(‖z‖ ^ 2 / 2))) 0‖ ≤ j ! := by
  set e := EuclideanSpace.basisFun (Fin 1) ℝ 0
  let L : ℝ¹ →L[ℝ] ℝ := innerSL ℝ e
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 0
  have hL : ‖L‖ ≤ 1 := by
    simp only [L, innerSL_apply_norm, he, le_refl]
  have hfun : (fun z : ℝ¹ => Real.exp (-(‖z‖ ^ 2 / 2))) =
      (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) ∘ L := by
    funext z
    simp only [Function.comp_apply, L, innerSL_apply_apply]
    rw [norm_eq_abs_inner_basisFun z, sq_abs]
  have hg : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) := by fun_prop
  rw [hfun, L.iteratedFDeriv_comp_right hg 0 (WithTop.coe_le_coe.mpr le_top), map_zero]
  calc
    ‖(iteratedFDeriv ℝ j (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) 0).compContinuousLinearMap
        fun _ => L‖ ≤
        ‖iteratedFDeriv ℝ j (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) 0‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j (fun t : ℝ => Real.exp (-(t ^ 2 / 2))) 0‖ * 1 := by
      gcongr
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
    _ ≤ j ! := by
      rw [mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact abs_iteratedDeriv_gaussian_zero_le j

/-- `∫ e^{2‖x‖} dγ ≤ 2 e² ≤ 16` on `ℝ¹`, from `e^{2|t|} ≤ e^{2t} + e^{-2t}` and the moment
generating function. -/
theorem integral_exp_two_mul_norm_tilted_half_norm_sq_le : ∫ x, Real.exp (2 * ‖x‖) ∂γ₁ ≤ 16 := by
  set e := EuclideanSpace.basisFun (Fin 1) ℝ 0
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 1) ℝ).orthonormal.1 0
  have hV := regularPotential_half_norm_sq (E := ℝ¹)
  have hint₁ := integrable_exp_inner_tilted_half_norm_sq ((2 : ℝ) • e)
  have hint₂ := integrable_exp_inner_tilted_half_norm_sq (-((2 : ℝ) • e))
  have hpt (x : ℝ¹) : Real.exp (2 * ‖x‖) ≤
      Real.exp ⟪(2 : ℝ) • e, x⟫ + Real.exp ⟪-((2 : ℝ) • e), x⟫ := by
    rw [norm_eq_abs_inner_basisFun x, inner_neg_left, real_inner_smul_left]
    rcases abs_cases ⟪e, x⟫ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · linarith [Real.exp_pos (-(2 * ⟪e, x⟫))]
    · rw [mul_neg]
      linarith [Real.exp_pos (2 * ⟪e, x⟫)]
  calc
    ∫ x, Real.exp (2 * ‖x‖) ∂γ₁ ≤
        ∫ x, (Real.exp ⟪(2 : ℝ) • e, x⟫ + Real.exp ⟪-((2 : ℝ) • e), x⟫) ∂γ₁ :=
      integral_mono (hV.integrable_exp_mul_norm 2) (hint₁.add hint₂) hpt
    _ = 2 * Real.exp 2 := by
      rw [integral_add hint₁ hint₂, integral_exp_inner_tilted_half_norm_sq,
        integral_exp_inner_tilted_half_norm_sq, norm_neg, norm_smul, he]
      norm_num
      ring
    _ ≤ 16 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have h0 := Real.exp_pos 1
      nlinarith

/-- `‖e^{‖x‖}‖_{L²(γ)} ≤ 4` on `ℝ¹`. -/
private theorem eLpNorm_exp_norm_le :
    (eLpNorm (fun x : ℝ¹ => Real.exp (1 * ‖x‖)) 2 γ₁).toReal ≤ 4 := by
  have hV := regularPotential_half_norm_sq (E := ℝ¹)
  have hw : MemLp (fun x : ℝ¹ => Real.exp (1 * ‖x‖)) 2 γ₁ := by
    apply (memLp_two_iff_integrable_sq
      (by fun_prop : Continuous (fun x : ℝ¹ => Real.exp (1 * ‖x‖))).aestronglyMeasurable).2
    refine (hV.integrable_exp_mul_norm 2).congr (Eventually.of_forall fun x => ?_)
    change Real.exp (2 * ‖x‖) = Real.exp (1 * ‖x‖) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hw.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  have hsq : (fun x : ℝ¹ => ‖Real.exp (1 * ‖x‖)‖ ^ (ENNReal.toReal 2)) =
      fun x => Real.exp (2 * ‖x‖) := by
    funext x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ENNReal.toReal_ofNat, Real.rpow_two,
      ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hsq, ENNReal.toReal_ofNat]
  calc
    (∫ x, Real.exp (2 * ‖x‖) ∂γ₁) ^ (2 : ℝ)⁻¹ ≤ ((4 : ℝ) ^ 2) ^ ((2 : ℕ) : ℝ)⁻¹ := by
      have h16 : ((4 : ℝ) ^ 2) ^ ((2 : ℕ) : ℝ)⁻¹ = (16 : ℝ) ^ (2 : ℝ)⁻¹ := by norm_num
      rw [h16]
      exact Real.rpow_le_rpow (integral_nonneg fun _ => (Real.exp_pos _).le)
        integral_exp_two_mul_norm_tilted_half_norm_sq_le (by norm_num)
    _ = 4 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

private theorem integral_exp_mul_norm_le_cauchy_schwarz {f : ℝ¹ → ℝ} (hf : MemLp f 2 γ₁) :
    (∫ x, Real.exp (1 * ‖x‖) * ‖f x‖ ∂γ₁) ≤ 4 * (eLpNorm f 2 γ₁).toReal := by
  have hV := regularPotential_half_norm_sq (E := ℝ¹)
  have hw : MemLp (fun x : ℝ¹ => Real.exp (1 * ‖x‖)) 2 γ₁ := by
    apply (memLp_two_iff_integrable_sq
      (by fun_prop : Continuous (fun x : ℝ¹ => Real.exp (1 * ‖x‖))).aestronglyMeasurable).2
    refine (hV.integrable_exp_mul_norm 2).congr (Eventually.of_forall fun x => ?_)
    change Real.exp (2 * ‖x‖) = Real.exp (1 * ‖x‖) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have heq :
      (∫ x, Real.exp (1 * ‖x‖) * ‖f x‖ ∂γ₁) =
        ⟪hw.toLp (fun x => Real.exp (1 * ‖x‖)), hf.norm.toLp (fun x => ‖f x‖)⟫ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp, hf.norm.coeFn_toLp] with x hx hfx
    rw [hx, hfx]
    simp [mul_comm]
  rw [heq]
  calc
    ⟪hw.toLp (fun x => Real.exp (1 * ‖x‖)), hf.norm.toLp (fun x => ‖f x‖)⟫ ≤
        ‖hw.toLp (fun x => Real.exp (1 * ‖x‖))‖ *
          ‖hf.norm.toLp (fun x => ‖f x‖)‖ := real_inner_le_norm _ _
    _ = (eLpNorm (fun x : ℝ¹ => Real.exp (1 * ‖x‖)) 2 γ₁).toReal * (eLpNorm f 2 γ₁).toReal := by
      rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm]
    _ ≤ 4 * (eLpNorm f 2 γ₁).toReal := by
      gcongr
      exact eLpNorm_exp_norm_le

/-- **Sharp moment bound for the Laplace numerator** on `ℝ¹`:
`‖∇^k (z ↦ ∫ e^{⟪z, x⟫} f(x) dγ)(0)‖ ≤ 4 k! ‖f‖_{L²(γ)}`, from `‖x‖^k ≤ k! e^{‖x‖}`. -/
theorem norm_iteratedFDeriv_integral_exp_inner_smul_tilted_half_norm_sq_le {f : ℝ¹ → ℝ}
    (hf : MemLp f 2 γ₁) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂γ₁) 0‖ ≤
      4 * k ! * (eLpNorm f 2 γ₁).toReal := by
  classical
  have hV := regularPotential_half_norm_sq (E := ℝ¹)
  have := hV.isProbabilityMeasure
  have hgi := integrable_exp_mul_norm_of_memLp γ₁ hV.integrable_exp_mul_norm hf
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro h
  rw [iteratedFDeriv_integral_exp_inner_smul γ₁ hf.aestronglyMeasurable hgi k 0 h]
  simp only [inner_zero_left, Real.exp_zero, one_mul, smul_eq_mul]
  have hprod (x : ℝ¹) : ‖∏ j, ⟪x, h j⟫‖ ≤ k ! * Real.exp (1 * ‖x‖) * ∏ j, ‖h j‖ := by
    have hpow : ‖x‖ ^ k ≤ k ! * Real.exp (1 * ‖x‖) := by
      have := Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) k
      rw [one_mul]
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    calc
      ‖∏ j, ⟪x, h j⟫‖ = ∏ j, ‖⟪x, h j⟫‖ := norm_prod _ _
      _ ≤ ∏ j, (‖x‖ * ‖h j‖) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => norm_inner_le_norm x (h j))
      _ = ‖x‖ ^ k * ∏ j, ‖h j‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ k ! * Real.exp (1 * ‖x‖) * ∏ j, ‖h j‖ := by gcongr
  calc
    ‖∫ x, (∏ j, ⟪x, h j⟫) * f x ∂γ₁‖ ≤
        ∫ x, (k ! * ∏ j, ‖h j‖) * (Real.exp (1 * ‖x‖) * ‖f x‖) ∂γ₁ := by
      apply norm_integral_le_of_norm_le ((hgi 1).const_mul _)
      filter_upwards [] with x
      rw [norm_mul]
      calc
        ‖∏ j, ⟪x, h j⟫‖ * ‖f x‖ ≤ (k ! * Real.exp (1 * ‖x‖) * ∏ j, ‖h j‖) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right (hprod x) (norm_nonneg _)
        _ = _ := by ring
    _ = (k ! * ∏ j, ‖h j‖) * ∫ x, Real.exp (1 * ‖x‖) * ‖f x‖ ∂γ₁ := integral_const_mul _ _
    _ ≤ (k ! * ∏ j, ‖h j‖) * (4 * (eLpNorm f 2 γ₁).toReal) := by
      gcongr
      exact integral_exp_mul_norm_le_cauchy_schwarz hf
    _ = 4 * k ! * (eLpNorm f 2 γ₁).toReal * ∏ j, ‖h j‖ := by ring

/-- The tilt average of the standard Gaussian: `F_f(z) = e^{-‖z‖²/2} ∫ e^{⟪z, x⟫} f(x) dγ(x)`. -/
private theorem tiltAverage_eq_mul (f : ℝ¹ → ℝ) :
    tiltAverage γ₁ f = fun z => Real.exp (-(‖z‖ ^ 2 / 2)) * ∫ x, Real.exp ⟪z, x⟫ • f x ∂γ₁ := by
  funext z
  rw [tiltAverage, expTilt, integral_tilted, integral_exp_inner_tilted_half_norm_sq]
  simp_rw [div_eq_mul_inv, mul_comm (Real.exp ⟪z, _⟫), mul_smul]
  rw [integral_smul, smul_eq_mul, Real.exp_neg]

/-- **Explicit Taylor bound for the standard Gaussian on `ℝ¹`** (operator norm):
`‖T_d f‖ ≤ 4 (d + 1) ‖f‖_{L²(γ)}` for every `f ∈ L²(γ)` and every `d`. -/
theorem norm_taylorTensor_tilted_half_norm_sq_le {f : ℝ¹ → ℝ} (hf : MemLp f 2 γ₁) (d : ℕ) :
    ‖taylorTensor γ₁ f d‖ ≤ 4 * (d + 1) * (eLpNorm f 2 γ₁).toReal := by
  have hV := regularPotential_half_norm_sq (E := ℝ¹)
  have := hV.isProbabilityMeasure
  set F := (eLpNorm f 2 γ₁).toReal
  let A : ℝ¹ → ℝ := fun z => Real.exp (-(‖z‖ ^ 2 / 2))
  let N : ℝ¹ → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • f x ∂γ₁
  have hA : ContDiff ℝ ∞ A := ContDiff.exp ((contDiff_norm_sq ℝ).div_const 2).neg
  have hN : ContDiff ℝ ∞ N :=
    contDiff_integral_exp_inner_smul_of_integrable γ₁ hf.aestronglyMeasurable
      (integrable_exp_mul_norm_of_memLp γ₁ hV.integrable_exp_mul_norm hf)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (d + 1)) :
      (d.choose i : ℝ) * (i ! : ℝ) * (4 * ((d - i) ! : ℝ) * F) = 4 * d ! * F := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [← h]
    push_cast
    ring
  calc
    ‖taylorTensor γ₁ f d‖ =
        ‖((d ! : ℕ) : ℝ)⁻¹‖ * ‖iteratedFDeriv ℝ d (fun z => A z * N z) 0‖ := by
      rw [taylorTensor, norm_smul, tiltAverage_eq_mul]
    _ ≤ ‖((d ! : ℕ) : ℝ)⁻¹‖ *
        ∑ i ∈ Finset.range (d + 1),
          (d.choose i : ℝ) * ‖iteratedFDeriv ℝ i A 0‖ * ‖iteratedFDeriv ℝ (d - i) N 0‖ := by
      gcongr
      exact norm_iteratedFDeriv_mul_le hA hN 0 (WithTop.coe_le_coe.mpr le_top)
    _ ≤ ‖((d ! : ℕ) : ℝ)⁻¹‖ *
        ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (i ! : ℝ) * (4 * ((d - i) ! : ℝ) * F) := by
      gcongr with i hi
      · exact norm_iteratedFDeriv_exp_neg_half_norm_sq_le i
      · exact norm_iteratedFDeriv_integral_exp_inner_smul_tilted_half_norm_sq_le hf (d - i)
    _ = ‖((d ! : ℕ) : ℝ)⁻¹‖ * ((d + 1) * (4 * d ! * F)) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ = 4 * (d + 1) * F := by
      rw [norm_inv, Real.norm_of_nonneg (by positivity)]
      field_simp

private theorem four_mul_succ_le_eight_pow {d : ℕ} (hd : 1 ≤ d) : 4 * (d + 1) ≤ 8 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have h1 : 1 ≤ 8 ^ d := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

/-- **BKL (29) for the standard Gaussian on `ℝ¹` with `R = 8`**: in the Hilbert–Schmidt norm of
the coefficient array in the standard basis, `|T_d f| ≤ 8^d ‖f‖_{L²(γ)}` for `d ≥ 1`. -/
theorem norm_coordTensor_taylorTensor_tilted_half_norm_sq_le {f : ℝ¹ → ℝ}
    (hf : MemLp f 2 γ₁) {d : ℕ} (hd : 1 ≤ d) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin 1) ℝ) (taylorTensor γ₁ f d)‖ ≤
      8 ^ d * (eLpNorm f 2 γ₁).toReal := by
  calc
    ‖coordTensor (EuclideanSpace.basisFun (Fin 1) ℝ) (taylorTensor γ₁ f d)‖ ≤
        Real.sqrt ((1 : ℕ) : ℝ) ^ d * ‖taylorTensor γ₁ f d‖ :=
      norm_coordTensor_le _ _
    _ = ‖taylorTensor γ₁ f d‖ := by
      rw [Nat.cast_one, Real.sqrt_one, one_pow, one_mul]
    _ ≤ 4 * (d + 1) * (eLpNorm f 2 γ₁).toReal := norm_taylorTensor_tilted_half_norm_sq_le hf d
    _ ≤ 8 ^ d * (eLpNorm f 2 γ₁).toReal := by
      gcongr
      exact_mod_cast four_mul_succ_le_eight_pow hd

end One

/-! ### Nonvacuity of BKL Theorem 3.1 in dimension one -/

/-- The standard Gaussian law on `ℝ¹`, as the regular law of `‖x‖²/2`. -/
local notation "γLaw" =>
  (((RegularPotential.law (regularPotential_half_norm_sq (E := EuclideanSpace ℝ (Fin 1))) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)))) : Measure (EuclideanSpace ℝ (Fin 1)))

/-- **The hypotheses of BKL Theorem 3.1 hold for the standard Gaussian on `ℝ¹`**: its potential
`‖x‖²/2` is regular with `a = b = 1`, the law is centered, `∫ ⟪v, x⟫² dγ ≤ ‖v‖²` (with equality),
and (29) holds with `R = 8`. -/
theorem gaussian_taylor_hypotheses :
    (∫ x, x ∂γLaw) = 0 ∧
      (∀ v : EuclideanSpace ℝ (Fin 1), ∫ x, ⟪v, x⟫ ^ 2 ∂γLaw ≤ ‖v‖ ^ 2) ∧
      (∀ (f : EuclideanSpace ℝ (Fin 1) → ℝ), MemLp f 2 γLaw → ∀ d : ℕ, 1 ≤ d →
        ‖coordTensor (EuclideanSpace.basisFun (Fin 1) ℝ) (taylorTensor γLaw f d)‖ ≤
          (8 : ℝ) ^ d * (eLpNorm f 2 γLaw).toReal) :=
  ⟨integral_id_tilted_half_norm_sq, fun v => (integral_inner_sq_tilted_half_norm_sq v).le,
    fun _ hf _ hd => norm_coordTensor_taylorTensor_tilted_half_norm_sq_le hf hd⟩

/-- **Nonvacuity witness for BKL Theorem 3.1 in positive dimension**: applying
`RegularPotential.poincare_le_of_taylor` to the standard Gaussian on `ℝ¹`, with every hypothesis
discharged (`n = 1`, `a = b = 1`, `R = 8`), gives `C_P(γ) ≤ K · 8²`. -/
theorem gaussian_poincare_le_of_taylor_witness : ∃ K : ℝ,
    Poincare.LocalSlope.Intrinsic.constant
        (regularPotential_half_norm_sq (E := EuclideanSpace ℝ (Fin 1))).law ≤
      ENNReal.ofReal (K * 8 ^ 2) := by
  obtain ⟨K, -, hK⟩ := RegularPotential.poincare_le_of_taylor
  obtain ⟨hcen, hcov, h29⟩ := gaussian_taylor_hypotheses
  exact ⟨K, hK 1 _ 1 1 regularPotential_half_norm_sq hcen hcov 8 (by norm_num) h29⟩

end FunctionalInequalities.KLS
