import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable

/-!
# The logarithmic Laplace transform and cumulant tensors

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 4 and the linear step of Proposition 7.1. For a
nonzero finite measure `μ` with all exponential moments, `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` is smooth,
the tilt average of a linear function is a directional derivative, `F_{⟪v,·⟫}(z) = DΛ_μ(z) v`, and
the Taylor tensors of linear functions are cumulant tensors,
`T_d ⟪v, ·⟫ = κ_{d+1}(v, ·, …, ·) / d!` with `κ_m = ∇^m Λ_μ(0)`.

The third cumulant of a centered law is its third moment. Conditionally on the quadratic-form
estimate of Letwin (2026, Theorem 1.2), stated as the explicit premise `LetwinQuadraticBound`, a
centered isotropic probability law with all exponential moments satisfies `R^μ_3 ≤ 8 Id`
(BKL Lemma 4.2 in that conditional, restricted form; the Letwin estimate is not proved here).
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The logarithmic Laplace transform `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` (BKL Section 4). -/
def logLaplace (μ : Measure E) (z : E) : ℝ :=
  Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ)

/-- The cumulant tensor `κ_m^μ = ∇^m Λ_μ(0)` (BKL Section 4), as a continuous `m`-linear form. -/
def cumulant (μ : Measure E) (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  iteratedFDeriv ℝ n (logLaplace μ) 0

omit [CompleteSpace E] in
/-- The logarithmic Laplace transform is smooth for a nonzero finite measure with all exponential
moments. -/
theorem contDiff_logLaplace (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiff ℝ ∞ (logLaplace μ) := by
    have hZ : ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
      simpa [smul_eq_mul, mul_one] using
        (contDiff_integral_exp_inner_smul μ hexp
          (g := fun _ : E => (1 : ℝ))
          (M := 1) (k := 0)
          (hg := measurable_const.aestronglyMeasurable)
          (hgb := by
            intro x
            simp))
    have hpos : ∀ z : E, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      intro z
      have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
        refine (hexp ‖z‖).mono' ?_ ?_
        · exact
            (Real.continuous_exp.comp
              (continuous_const.inner continuous_id)).aestronglyMeasurable
        · filter_upwards [] with x
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
      exact integral_exp_pos hzint
    change ContDiff ℝ ∞
      (fun z : E => Real.log (∫ x, Real.exp ⟪z, x⟫ ∂μ))
    exact hZ.log (fun z => (hpos z).ne')

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private lemma bkl_integrable_exp_inner (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
  refine (hexp ‖z‖).mono'
    ((continuous_const.inner continuous_id).rexp.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (real_inner_le_norm z x)

omit [CompleteSpace E] in
private lemma bkl_hasFDerivAt_laplace (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    HasFDerivAt (fun y => ∫ x, Real.exp ⟪y, x⟫ ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • innerSL ℝ x ∂μ) z := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y x => Real.exp ⟪y, x⟫)
    (F' := fun y x => Real.exp ⟪y, x⟫ • innerSL ℝ x)
    (s := Metric.ball z 1)
    (bound := fun x => Real.exp ((‖z‖ + 2) * ‖x‖))
    (Metric.ball_mem_nhds z zero_lt_one) ?_
    (bkl_integrable_exp_inner μ hexp z) ?_ ?_
    (hexp (‖z‖ + 2)) ?_
  · exact Filter.Eventually.of_forall fun y =>
      (continuous_const.inner continuous_id).rexp.aestronglyMeasurable
  · exact ((continuous_const.inner continuous_id).rexp.smul
      (innerSL ℝ).continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x y hy => by
      have hy' : ‖y‖ ≤ ‖z‖ + 1 := by
        have hdist : ‖y - z‖ < 1 := by
          simpa [dist_eq_norm] using hy
        calc
          ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
            simpa [add_comm, norm_sub_rev] using norm_le_norm_add_norm_sub z y
          _ ≤ ‖z‖ + 1 := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        innerSL_apply_norm]
      calc
        Real.exp ⟪y, x⟫ * ‖x‖ ≤
            Real.exp ((‖z‖ + 1) * ‖x‖) * Real.exp ‖x‖ := by
          exact mul_le_mul
            (Real.exp_le_exp.mpr
              ((real_inner_le_norm y x).trans
                (mul_le_mul_of_nonneg_right hy' (norm_nonneg x))))
            (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1)
              (Real.add_one_le_exp ‖x‖))
            (norm_nonneg x) (Real.exp_pos _).le
        _ = Real.exp ((‖z‖ + 2) * ‖x‖) := by
          rw [← Real.exp_add]
          congr 1
          ring
  · exact Filter.Eventually.of_forall fun x y _ => by
      simpa only [innerSL_apply_apply, real_inner_comm] using
        (innerSL ℝ x).hasFDerivAt.exp

omit [CompleteSpace E] in
/-- The tilt average of a linear function is a derivative of `Λ_μ`: `F_ℓ(z) = ⟪v, ∇Λ_μ(z)⟫` for
`ℓ = ⟪v, ·⟫` (proof of BKL Proposition 7.1). -/
theorem tiltAverage_inner_eq_fderiv_logLaplace (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v z : E) :
    tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v := by
  have hi := bkl_integrable_exp_inner μ hexp z
  have hd := bkl_hasFDerivAt_laplace μ hexp z
  have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
  have hlog := hd.log hp
  change tiltAverage μ (fun x => ⟪v, x⟫) z =
    fderiv ℝ (fun y => Real.log (∫ x, Real.exp ⟪y, x⟫ ∂μ)) z v
  rw [hlog.fderiv]
  change (∫ x, ⟪v, x⟫ ∂(μ.tilted fun x => ⟪z, x⟫)) =
    (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ *
      (∫ x, Real.exp ⟪z, x⟫ • innerSL ℝ x ∂μ) v
  rw [integral_tilted]
  have hdi : Integrable (fun x => Real.exp ⟪z, x⟫ • innerSL ℝ x) μ := by
    refine (hexp (‖z‖ + 1)).mono' ?_ ?_
    · exact ((continuous_const.inner continuous_id).rexp.smul
        (innerSL ℝ).continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          innerSL_apply_norm]
        calc
          Real.exp ⟪z, x⟫ * ‖x‖ ≤
              Real.exp (‖z‖ * ‖x‖) * Real.exp ‖x‖ :=
            mul_le_mul
              (Real.exp_le_exp.mpr (real_inner_le_norm z x))
              (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1)
                (Real.add_one_le_exp ‖x‖))
              (norm_nonneg x) (Real.exp_pos _).le
          _ = Real.exp ((‖z‖ + 1) * ‖x‖) := by
            rw [← Real.exp_add]
            congr 1
            ring
  rw [ContinuousLinearMap.integral_apply hdi]
  simp_rw [smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_comm,
    div_eq_mul_inv]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma bkl_cumulant_swap_front {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v w : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) g x (Fin.cons v (Fin.cons w h)) =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons w (Fin.cons v h)) := by
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (m := ∞) (by norm_cast)
  have ha : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n g y h) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F h).contDiff.comp hd
  have heq (a : E) :
      (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons a h)) =
        fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ n g z h) y a := by
    funext y
    simpa using (hd.differentiable (by simp) y).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons a h)
  have hleft :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons v (Fin.cons w h))
  have hright :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons w (Fin.cons v h))
  rw [hleft, hright]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [heq w, heq v]
  rw [fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const w),
    fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const v)]
  simpa using
    ((ha.of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).contDiffAt.isSymmSndFDerivAt
      (by simp)).eq v w

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma bkl_cumulant_cons_snoc {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g x (Fin.cons v h) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc h v) := by
  induction n generalizing x with
  | zero =>
      congr 1
      ext i
      fin_cases i
      simp [Fin.snoc_zero]
  | succ n ih =>
      rw [← Fin.cons_self_tail h]
      rw [bkl_cumulant_swap_front hg n x v (h 0) (Fin.tail h)]
      rw [← Fin.cons_snoc_eq_snoc_cons]
      have heq :
          (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons v (Fin.tail h))) =
            fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.snoc (Fin.tail h) v) := by
        funext y
        exact ih y (Fin.tail h)
      rw [(hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left',
        (hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left']
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun a : E → F => fderiv ℝ a x (h 0)) heq

omit [CompleteSpace E] in
/-- **Taylor tensors of linear functions are cumulants** (proof of BKL Proposition 7.1):
for `ℓ = ⟪v, ·⟫`, `T_d ℓ = κ_{d+1}(v, ·, …, ·) / d!`. -/
theorem taylorTensor_inner_eq_cumulant (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
    (h : Fin d → E) :
    taylorTensor μ (fun x => ⟪v, x⟫) d h = (d.factorial : ℝ)⁻¹ * cumulant μ (d + 1) (Fin.cons v h) := by
  have heq : tiltAverage μ (fun x => ⟪v, x⟫) =
      fun z => fderiv ℝ (logLaplace μ) z v := by
    funext z
    exact tiltAverage_inner_eq_fderiv_logLaplace μ hexp v z
  have hL := contDiff_logLaplace μ hexp
  have hd : ContDiff ℝ ∞ (fderiv ℝ (logLaplace μ)) :=
    hL.fderiv_right (by simp)
  have hder :
      iteratedFDeriv ℝ d (fun z => fderiv ℝ (logLaplace μ) z v) 0 h =
        iteratedFDeriv ℝ d (fderiv ℝ (logLaplace μ)) 0 h v :=
    iteratedFDeriv_clm_apply_const_apply hd (by norm_cast; simp)
  simp only [taylorTensor, smul_apply, smul_eq_mul, heq]
  rw [hder]
  have hs := bkl_cumulant_cons_snoc hL d 0 v h
  have ht := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := logLaplace μ) (x := (0 : E)) (Fin.snoc h v)
  simp only [Fin.init_snoc, Fin.snoc_last] at ht
  rw [ht] at hs
  exact congrArg (fun a : ℝ => (d.factorial : ℝ)⁻¹ * a) hs.symm

section ThirdCumulant

/-- The quadratic-form estimate of Letwin (2026, Theorem 1.2), stated as a property of the law `μ`:
`Var_μ⟨Mx, x⟩ ≤ 8 |M|²_HS` for every self-adjoint `M`, with `|M|²_HS = ∑_{i,j} ⟪M e_i, e_j⟫²` in an
orthonormal basis. This names the hypothesis; it is not proved here. -/
def LetwinQuadraticBound (μ : Measure E) : Prop :=
  ∀ M : E →L[ℝ] E, IsSelfAdjoint M →
    ∫ x, (⟪M x, x⟫ - ∫ y, ⟪M y, y⟫ ∂μ) ^ 2 ∂μ ≤
      8 * ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ E i), stdOrthonormalBasis ℝ E j⟫ ^ 2

variable (μ : Measure E) [IsProbabilityMeasure μ]
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)

omit [CompleteSpace E] in
include hexp in
/-- The first derivative of the logarithmic Laplace transform at `0` is the mean. -/
theorem fderiv_logLaplace_zero_apply (v : E) :
    fderiv ℝ (logLaplace μ) 0 v = ∫ x, ⟪v, x⟫ ∂μ := by
    calc
      fderiv ℝ (logLaplace μ) 0 v =
          tiltAverage μ (fun x => ⟪v, x⟫) 0 :=
        (tiltAverage_inner_eq_fderiv_logLaplace μ hexp v 0).symm
      _ = ∫ x, ⟪v, x⟫ ∂μ := by
        simp [tiltAverage, expTilt]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma third_second_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v w : E) :
    iteratedFDeriv ℝ 2 f x ![v, w] =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [(hf.differentiable_iteratedFDeriv (m := 1) (by norm_num) x).iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_succ]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma third_second_mul {f g : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x v w : E) (hf0 : f x = 0) (hg0 : g x = 1)
    (hg1 : fderiv ℝ g x = 0) :
    iteratedFDeriv ℝ 2 (fun y => f y * g y) x ![v, w] =
      iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  have hdg := hg.fderiv_right (m := ∞) (by simp)
  have hfw : Differentiable ℝ (fun y => fderiv ℝ f y w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp hdf).differentiable (by simp)
  have hgw : Differentiable ℝ (fun y => fderiv ℝ g y w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.comp hdg).differentiable (by simp)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =
      fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
    funext y
    rw [fderiv_fun_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp
  rw [third_second_apply (hf.mul hg), third_second_apply hf, heq]
  rw [fderiv_fun_add (f := fun y => f y * fderiv ℝ g y w)
    (g := fun y => g y * fderiv ℝ f y w)
    ((hf.differentiable (by simp) x).mul (hgw x))
    ((hg.differentiable (by simp) x).mul (hfw x))]
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hgw x),
    fderiv_fun_mul (hg.differentiable (by simp) x) (hfw x)]
  simp [hf0, hg0, hg1]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
include hexp in
private lemma third_exp_inner_integrable (u : E) (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖) * ‖⟪u, x⟫‖) μ := by
  refine ((hexp (r + 1)).const_mul ‖u‖).mono'
    (by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖) * ‖⟪u, x⟫‖)).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
    le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
  calc
    Real.exp (r * ‖x‖) * ‖⟪u, x⟫‖ ≤
        Real.exp (r * ‖x‖) * (‖u‖ * Real.exp ‖x‖) := by
      gcongr
      exact (norm_inner_le_norm u x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg u))
    _ = ‖u‖ * Real.exp ((r + 1) * ‖x‖) := by
      rw [add_mul, one_mul, Real.exp_add]
      ring

omit [CompleteSpace E] in
include hexp in
/-- For a centered law, the second Taylor tensor of a linear function is half the third moment:
`T_2⟪u, ·⟫(v, w) = ½ ∫ ⟪u, x⟫ ⟪v, x⟫ ⟪w, x⟫ dμ`. -/
theorem taylorTensor_two_inner_eq_of_centered (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    taylorTensor μ (fun x => ⟪u, x⟫) 2 ![v, w] = (1 / 2 : ℝ) * ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
  let F := tiltAverage μ (fun x => ⟪u, x⟫)
  let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • ⟪u, x⟫ ∂μ
  have hF : ContDiff ℝ ∞ F := by
    have heq : F = fun z => fderiv ℝ (logLaplace μ) z u :=
      funext (tiltAverage_inner_eq_fderiv_logLaplace μ hexp u)
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ ℝ u).contDiff.comp
      ((contDiff_logLaplace μ hexp).fderiv_right (by simp))
  have hZ : ContDiff ℝ ∞ Z :=
    contDiff_integral_exp_inner_smul_of_integrable μ
      measurable_const.aestronglyMeasurable (by simpa using hexp)
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hF0 : F 0 = 0 := by simpa [F, tiltAverage, expTilt] using hc u
  have hZ1 : fderiv ℝ Z 0 = 0 := by
    ext a
    have h := iteratedFDeriv_integral_exp_inner_smul μ
      (g := fun _ : E => (1 : ℝ)) measurable_const.aestronglyMeasurable
      (by simpa using hexp) 1 0 ![a]
    have h' : fderiv ℝ Z 0 a = ∫ x, ⟪a, x⟫ ∂μ := by
      simpa [Z, iteratedFDeriv_one_apply, real_inner_comm] using h
    exact h'.trans (hc a)
  have hNZ : N = fun z => F z * Z z := by
    funext z
    have hi : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
      refine (hexp ‖z‖).mono'
        (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable ?_
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
    dsimp [N, F, Z]
    rw [tiltAverage, expTilt, integral_tilted]
    simp only [smul_eq_mul, mul_one, div_eq_mul_inv]
    rw [show (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * ⟪u, x⟫) =
      (fun x => (Real.exp ⟪z, x⟫ * ⟪u, x⟫) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹) by
        funext x; ring]
    rw [integral_mul_const]
    field_simp
  have hsecond := third_second_mul hF hZ 0 v w hF0 hZ0 hZ1
  rw [← hNZ] at hsecond
  have hm := iteratedFDeriv_integral_exp_inner_smul μ
    (g := fun x => ⟪u, x⟫)
    (by fun_prop : Continuous (fun x : E => ⟪u, x⟫)).aestronglyMeasurable
    (third_exp_inner_integrable μ hexp u) 2 0 ![v, w]
  have hm' : iteratedFDeriv ℝ 2 N 0 ![v, w] =
      ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    simpa [N, Fin.prod_univ_two, smul_eq_mul, real_inner_comm,
      mul_comm, mul_left_comm, mul_assoc] using hm
  simp only [taylorTensor, smul_apply, smul_eq_mul]
  change (Nat.factorial 2 : ℝ)⁻¹ * iteratedFDeriv ℝ 2 F 0 ![v, w] = _
  rw [← hsecond, hm']
  norm_num

omit [CompleteSpace E] in
include hexp in
/-- The third cumulant of a centered law is its third moment. -/
theorem cumulant_three_eq_integral (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    have hvec : Fin.cons u ![v, w] = ![u, v, w] := by
      funext i
      fin_cases i <;> rfl
    have h :=
      taylorTensor_inner_eq_cumulant μ hexp u 2 ![v, w]
    rw [taylorTensor_two_inner_eq_of_centered μ hexp hc u v w] at h
    rw [hvec] at h
    norm_num [Nat.factorial] at h
    linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
omit [InnerProductSpace ℝ E] in
include hexp in
private lemma third_memLp_poly {g : E → ℝ} (hg : Continuous g)
    {C : ℝ} {k : ℕ} (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    MemLp g 2 μ := by
  apply (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
  refine ((hexp (2 * (k : ℝ))).const_mul (C ^ 2)).mono'
    (hg.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  have he : (1 + ‖x‖) ^ k ≤ Real.exp ((k : ℝ) * ‖x‖) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by simpa [add_comm] using Real.add_one_le_exp ‖x‖) k
  calc
    ‖g x ^ 2‖ = ‖g x‖ ^ 2 := norm_pow _ _
    _ ≤ (C * Real.exp ((k : ℝ) * ‖x‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((hb x).trans (mul_le_mul_of_nonneg_left he hC)) 2
    _ = C ^ 2 * Real.exp (2 * (k : ℝ) * ‖x‖) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
include hexp in
private lemma third_memLp_inner (v : E) :
    MemLp (fun x => ⟪v, x⟫) 2 μ := by
  apply third_memLp_poly μ hexp (by fun_prop) (norm_nonneg v) (k := 1)
  intro x
  simpa only [pow_one] using
    (norm_inner_le_norm v x).trans
      (mul_le_mul_of_nonneg_left (by linarith : ‖x‖ ≤ 1 + ‖x‖) (norm_nonneg v))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure μ] in
include hexp in
private lemma third_memLp_inner_mul (v w : E) :
    MemLp (fun x => ⟪v, x⟫ * ⟪w, x⟫) 2 μ := by
  apply third_memLp_poly μ hexp (by fun_prop)
    (mul_nonneg (norm_nonneg v) (norm_nonneg w)) (k := 2)
  intro x
  calc
    ‖⟪v, x⟫ * ⟪w, x⟫‖ ≤ (‖v‖ * ‖x‖) * (‖w‖ * ‖x‖) := by
      rw [norm_mul]
      exact mul_le_mul (norm_inner_le_norm v x) (norm_inner_le_norm w x)
        (norm_nonneg _) (by positivity)
    _ = (‖v‖ * ‖w‖) * ‖x‖ ^ 2 := by ring
    _ ≤ (‖v‖ * ‖w‖) * (1 + ‖x‖) ^ 2 := by gcongr; linarith

include hexp in
/-- **BKL Lemma 4.2, conditional on the Letwin bound**: for a centered isotropic probability law
with all exponential moments satisfying `LetwinQuadraticBound`, `R^μ_3 ≤ 8 Id`, that is
`∑_{j,k} κ_3(u, e_j, e_k)² ≤ 8 |u|²` for every `u`. -/
theorem sum_sq_cumulant_three_le_of_letwin (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫) (hL : LetwinQuadraticBound μ) (u : E) :
    ∑ j, ∑ k, cumulant μ 3 ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤
      8 * ‖u‖ ^ 2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let C := fun j k => ∫ x, ⟪u, x⟫ * ⟪b j, x⟫ * ⟪b k, x⟫ ∂μ
  let S : ℝ := ∑ j, ∑ k, C j k ^ 2
  let M : E →L[ℝ] E := ∑ j, ∑ k, C j k • (innerSL ℝ (b k)).smulRight (b j)
  let Q : E → ℝ := fun x => ⟪M x, x⟫
  let f : E → ℝ := fun x => ⟪u, x⟫
  let q : E → ℝ := fun x => Q x - ∫ y, Q y ∂μ
  have hC : ∀ j k, C j k = C k j := by
    intro j k
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hMxy (x y : E) :
      ⟪M x, y⟫ = ∑ j, ∑ k, C j k * ⟪b k, x⟫ * ⟪b j, y⟫ := by
    simp [M, sum_inner, real_inner_smul_left, mul_assoc]
  have hM : IsSelfAdjoint M := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
    intro x y
    change ⟪M x, y⟫ = ⟪x, M y⟫
    conv_rhs => rw [real_inner_comm]
    rw [hMxy, hMxy, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hC k j]
    ring
  have hMij (i j) : ⟪M (b i), b j⟫ = C j i := by
    rw [hMxy]
    simp [b.inner_eq_ite]
  have hvar : ∫ x, q x ^ 2 ∂μ ≤ 8 * S := by
    simpa only [q, Q, hMij, hC, S, b] using hL M hM
  have hf : MemLp f 2 μ := third_memLp_inner μ hexp u
  have hQ : MemLp Q 2 μ := by
    have heq : Q = fun x => ∑ j, ∑ k, C j k * (⟪b k, x⟫ * ⟪b j, x⟫) := by
      funext x
      simp only [Q, hMxy, mul_assoc]
    rw [heq]
    exact memLp_finsetSum _ fun j _ =>
      memLp_finsetSum _ fun k _ =>
        (third_memLp_inner_mul μ hexp (b k) (b j)).const_mul (C j k)
  have hq : MemLp q 2 μ := hQ.sub (memLp_const _)
  have hcross : ∫ x, f x * q x ∂μ = S := by
    have hprod : ∀ j k, Integrable (fun x => ⟪u, x⟫ * (⟪b k, x⟫ * ⟪b j, x⟫)) μ :=
      fun j k => hf.integrable_mul (third_memLp_inner_mul μ hexp (b k) (b j))
    have hprodC : ∀ j k, Integrable (fun x => C j k * (⟪u, x⟫ * (⟪b k, x⟫ * ⟪b j, x⟫))) μ :=
      fun j k => (hprod j k).const_mul _
    have hsum : Integrable (fun x => f x * Q x) μ := hf.integrable_mul hQ
    simp only [q, mul_sub]
    rw [integral_sub hsum ((hf.integrable (by norm_num)).mul_const (∫ y, Q y ∂μ)),
      integral_mul_const]
    simp only [f, hc, zero_mul, sub_zero]
    simp_rw [Q, hMxy, Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        have heq : (fun x => ⟪u, x⟫ * (C j k * ⟪b k, x⟫ * ⟪b j, x⟫)) =
            fun x => C j k * (⟪u, x⟫ * ⟪b j, x⟫ * ⟪b k, x⟫) := by
          funext x; ring
        rw [heq, integral_const_mul]
        exact (pow_two (C j k)).symm
      · intro k _
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodC j k
    · intro j _
      apply integrable_finsetSum
      intro k _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hprodC j k
  have hf2 : Integrable (fun x => f x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hq2 : Integrable (fun x => q x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hq.aestronglyMeasurable).1 hq
  have hsq : 0 ≤ (∫ x, q x ^ 2 ∂μ) - 16 * S + 64 * ‖u‖ ^ 2 := by
    have hn := integral_nonneg (μ := μ) (f := fun x => (q x - 8 * f x) ^ 2)
      (fun x => sq_nonneg _)
    have heq : (fun x => (q x - 8 * f x) ^ 2) =
        fun x => q x ^ 2 - 16 * (f x * q x) + 64 * f x ^ 2 := by
      funext x; ring
    rw [heq, integral_add (f := fun x => q x ^ 2 - 16 * (f x * q x))
      (g := fun x => 64 * f x ^ 2)
      (hq2.sub ((hf.integrable_mul hq).const_mul 16))
      (hf2.const_mul 64),
      integral_sub (f := fun x => q x ^ 2) (g := fun x => 16 * (f x * q x))
      hq2 ((hf.integrable_mul hq).const_mul 16),
      integral_const_mul, integral_const_mul, hcross] at hn
    have he : ∫ x, f x ^ 2 ∂μ = ‖u‖ ^ 2 := by
      simpa only [f, pow_two, real_inner_self_eq_norm_sq] using hiso u u
    rwa [he] at hn
  have hκ (v w : E) :
      cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    have ht := taylorTensor_two_inner_eq_of_centered μ hexp hc u v w
    rw [taylorTensor_inner_eq_cumulant μ hexp u 2 ![v, w]] at ht
    norm_num at ht
    linarith
  simp_rw [hκ]
  change S ≤ 8 * ‖u‖ ^ 2
  linarith

end ThirdCumulant

end FunctionalInequalities.Analysis.BakryEmery
