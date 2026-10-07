import FunctionalInequalities.Analysis.BakryEmery.Tilt

/-!
# The logarithmic Laplace transform and cumulant tensors

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 4 and the linear step of Proposition 7.1. For a
nonzero finite measure `μ` with all exponential moments, `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` is smooth,
the tilt average of a linear function is a directional derivative, `F_{⟪v,·⟫}(z) = DΛ_μ(z) v`, and
the Taylor tensors of linear functions are cumulant tensors,
`T_d ⟪v, ·⟫ = κ_{d+1}(v, ·, …, ·) / d!` with `κ_m = ∇^m Λ_μ(0)`.
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

end FunctionalInequalities.Analysis.BakryEmery
