import FunctionalInequalities.Analysis.WaveSplitting.AverageError
import FunctionalInequalities.Analysis.BakryEmery.Laplacian
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Finite wave splitting for a potential: weight, classical density and orthonormal identification

Specialization of the coordinate objects of this family to a potential `U`: the coefficient
`b_j = D_(a_j) U` and the weight `w = exp (-U)`.

* `fderiv_exp_neg_apply`: the weight equation `D_(a_j) w = -b_j w`.
* `exists_timeAverage_error_lt`: classical form-range approximation. For compactly supported
  smooth `h` and `ε > 0` an actual cellwise time average `q ∈ C_c^∞` has
  `sqrt FE_w(J_cl q - h) < ε`.
* For an orthonormal basis `a`: `Σ_j (D_(a_j) f)^2 = ‖∇f‖²`, `Σ_j D_(a_j) D_(a_j) f = Δf`,
  `Σ_j b_j D_(a_j) f = ⟪∇U, ∇f⟫`, hence `formOperator a b f = f - ℒf` with the weighted Laplacian
  `ℒf = Δf - ⟪∇U, ∇f⟫`, and `FE_w(f) = ∫ exp (-U) (f² + ‖∇f‖²) dm`.
* Normalization: if `μ = m.tilted (-U)` is a probability measure, then `exp (-U)` is
  `m`-integrable, `Z = ∫ exp (-U) dm > 0` and `FE_w(f) = Z ∫ (f² + ‖∇f‖²) dμ`.

Everything here is classical and pointwise or integral; the closed gradient, its adjoint and
the class-level statements are in `KLS/LogConcave/HeatSemigroup/FormRange.lean`.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.WaveSplitting

/-! ## The potential weight and classical density -/

section Weight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The potential weight `exp (-U)` of a `C¹` potential is `C¹`. -/
theorem contDiff_exp_neg {U : E → ℝ} (hU : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (fun x => Real.exp (-U x)) :=
  Real.contDiff_exp.comp hU.neg

/-- The weight equation `D_v exp (-U) = -(D_v U) exp (-U)`. -/
theorem fderiv_exp_neg_apply {U : E → ℝ} (hU : Differentiable ℝ U) (x v : E) :
    fderiv ℝ (fun x => Real.exp (-U x)) x v = -(fderiv ℝ U x v * Real.exp (-U x)) := by
  have h : HasFDerivAt (fun x => Real.exp (-U x)) (Real.exp (-U x) • -fderiv ℝ U x) x :=
    ((hU x).hasFDerivAt.neg).exp
  rw [h.fderiv]
  simp only [FunLike.coe_smul, FunLike.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
  [m.IsAddHaarMeasure]

/-- **Classical form-range approximation for a potential.** For a smooth potential `U`, any
directions `a`, the coefficient `b_j = D_(a_j) U` and the weight `w = exp (-U)`: every
compactly supported smooth `h` and every `ε > 0` admit an actual cellwise time average
`q ∈ C_c^∞` with `sqrt FE_w(J_cl q - h) < ε`. The horizon is chosen first, then the mesh. -/
theorem exists_timeAverage_error_lt {d : ℕ} (a : Fin d → E) {U h : E → ℝ}
    (hU : ContDiff ℝ ∞ U) (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ContDiff ℝ ∞ (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ
        (initial h) N) ∧
      HasCompactSupport (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ
        (initial h) N) ∧
      √(weightedFormEnergy m (fun x => Real.exp (-U x)) a (fun x =>
          formOperator a (fun j x => fderiv ℝ U x (a j))
            (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) N) x -
            h x)) < ε := by
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by simp)
  have hwb (j : Fin d) (x : E) : fderiv ℝ (fun x => Real.exp (-U x)) x (a j) =
      -(fderiv ℝ U x (a j) * Real.exp (-U x)) :=
    fderiv_exp_neg_apply (hU1.differentiable one_ne_zero) x (a j)
  set W := √(∫ x, Real.exp (-U x) * h x ^ 2 ∂m)
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  set L := 2 * (W + 1) / ε
  have hL : 0 < L := by positivity
  obtain ⟨C, hC, hbound⟩ := exists_timeAverage_error_bound m a hb (contDiff_exp_neg hU1)
    (fun x => (Real.exp_pos _).le) hwb hh hc hL
  obtain ⟨N, hN⟩ := exists_nat_gt (max L (2 * C * L / ε))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _ |>.trans' hL.le) hN
  set δ := L / N
  have hδ : 0 < δ := div_pos hL hNpos
  have hδ1 : δ ≤ 1 := by
    rw [div_le_one hNpos]; exact (le_max_left _ _).trans hN.le
  have hNδ : (N : ℝ) * δ = L := by simp only [δ]; field_simp
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hc
  refine ⟨N, δ, hδ, contDiff_timeAverage a hb _ (smooth_initial hh) δ N,
    hasCompactSupport_timeAverage a _ _ hR hδ.le N, ?_⟩
  have h₁ := hbound N δ hδ hδ1 hNδ
  have h₂ : W / L < ε / 2 := by
    rw [div_lt_iff₀ hL]; simp only [L]; field_simp; nlinarith
  have h₃ : C * δ < ε / 2 := by
    have hlt : 2 * C * L / ε < N := (le_max_right _ _).trans_lt hN
    rw [div_lt_iff₀ hε] at hlt
    simp only [δ]
    rw [mul_div_assoc', div_lt_iff₀ hNpos]
    nlinarith
  linarith

end Weight

/-! ## Orthonormal directions and potential coefficients -/

section Orthonormal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {ι : Type*} [Fintype ι]

/-- In an orthonormal basis, the squared directional derivatives sum to `‖∇f‖²`. -/
theorem sum_fderiv_sq_eq_norm_gradient_sq (e : OrthonormalBasis ι ℝ V) (f : V → ℝ) (x : V) :
    ∑ j, fderiv ℝ f x (e j) ^ 2 = ‖gradient f x‖ ^ 2 := by
  rw [← e.sum_sq_inner_left]
  simp only [inner_gradient_left]

/-- In an orthonormal basis, `Σ_j (D_(e_j) U)(D_(e_j) f) = ⟪∇U, ∇f⟫`. -/
theorem sum_fderiv_mul_fderiv_eq_inner_gradient (e : OrthonormalBasis ι ℝ V) (U f : V → ℝ)
    (x : V) : ∑ j, fderiv ℝ U x (e j) * fderiv ℝ f x (e j) = ⟪gradient U x, gradient f x⟫ := by
  rw [← e.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_gradient_left, real_inner_comm, inner_gradient_left]

variable [FiniteDimensional ℝ V]

omit [CompleteSpace V] in
/-- In an orthonormal basis, the iterated directional derivatives sum to the Laplacian, at a
point where the derivative is differentiable. -/
theorem sum_fderiv_fderiv_eq_laplacian (e : OrthonormalBasis ι ℝ V) {f : V → ℝ} {x : V}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    ∑ j, fderiv ℝ (fun y => fderiv ℝ f y (e j)) x (e j) = Laplacian.laplacian f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply, BakryEmery.fderiv_fderiv_apply hf]
  rfl

/-- **Operator identification.** For an orthonormal basis `e` and the coefficient
`b_j = D_(e_j) U`, the classical operator is `J_cl f = f - ℒf`, `ℒf = Δf - ⟪∇U, ∇f⟫`. -/
theorem formOperator_eq_sub_weightedLaplacian (e : OrthonormalBasis ι ℝ V) (U : V → ℝ)
    {f : V → ℝ} (hf : ContDiff ℝ 2 f) :
    formOperator e (fun j x => fderiv ℝ U x (e j)) f =
      fun x => f x - BakryEmery.weightedLaplacian U f x := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  rw [formOperator, Finset.sum_sub_distrib, sum_fderiv_fderiv_eq_laplacian e hd,
    sum_fderiv_mul_fderiv_eq_inner_gradient e, BakryEmery.weightedLaplacian_apply]

/-- For a smooth potential and a smooth compactly supported `f`, the classical operator in an
orthonormal basis is smooth. -/
theorem contDiff_formOperator (e : OrthonormalBasis ι ℝ V) {U f : V → ℝ} (hU : ContDiff ℝ ∞ U)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (formOperator e (fun j x => fderiv ℝ U x (e j)) f) := by
  rw [formOperator_eq_sub_weightedLaplacian e U (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact hf.sub (BakryEmery.contDiff_weightedLaplacian hU hf (by decide) (by decide))

/-- The classical operator in an orthonormal basis preserves compact support. -/
theorem hasCompactSupport_formOperator (e : OrthonormalBasis ι ℝ V) (U : V → ℝ) {f : V → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    HasCompactSupport (formOperator e (fun j x => fderiv ℝ U x (e j)) f) := by
  rw [formOperator_eq_sub_weightedLaplacian e U hf]
  exact hfc.sub (BakryEmery.hasCompactSupport_weightedLaplacian U hfc)

variable [MeasurableSpace V] (m : Measure V)

omit [FiniteDimensional ℝ V] in
/-- **Energy identification.** In an orthonormal basis the weighted coordinate form energy is
`∫ w (f² + ‖∇f‖²) dm`. -/
theorem weightedFormEnergy_eq_integral_norm_gradient (e : OrthonormalBasis ι ℝ V)
    (w f : V → ℝ) :
    weightedFormEnergy m w e f = ∫ x, w x * (f x ^ 2 + ‖gradient f x‖ ^ 2) ∂m := by
  rw [weightedFormEnergy_eq]
  simp only [sum_fderiv_sq_eq_norm_gradient_sq e f]

end Orthonormal

/-! ## Normalization of the tilted law -/

section Tilted

variable {E : Type*} [MeasurableSpace E] (m : Measure E) {U : E → ℝ} {μ : Measure E}
  [IsProbabilityMeasure μ]

/-- If `m.tilted (-U)` is a probability measure, then `exp (-U)` is `m`-integrable. -/
theorem integrable_exp_neg_of_tilted (hμU : μ = m.tilted (-U)) :
    Integrable (fun x => Real.exp (-U x)) m := by
  by_contra h
  have h0 : μ = 0 := by rw [hμU]; exact tilted_of_not_integrable h
  have h1 := measure_univ (μ := μ)
  rw [h0] at h1
  simp at h1

/-- If `m.tilted (-U)` is a probability measure, the normalization `Z = ∫ exp (-U) dm` is
positive. -/
theorem integral_exp_neg_pos_of_tilted (hμU : μ = m.tilted (-U)) :
    0 < ∫ x, Real.exp (-U x) ∂m := by
  have hm : NeZero m := ⟨fun h => by
    have h1 := measure_univ (μ := μ)
    rw [hμU, h, tilted_zero_measure] at h1
    simp at h1⟩
  exact integral_exp_pos (f := fun x => -U x) (integrable_exp_neg_of_tilted m hμU)

/-- **The density of the tilted law.** For every `g`,
`∫ exp (-U) g dm = Z ∫ g dμ` with `Z = ∫ exp (-U) dm`; no integrability of `g` is needed. -/
theorem integral_exp_neg_mul_eq_of_tilted (hμU : μ = m.tilted (-U)) (g : E → ℝ) :
    ∫ x, Real.exp (-U x) * g x ∂m = (∫ x, Real.exp (-U x) ∂m) * ∫ x, g x ∂μ := by
  have hZ := (integral_exp_neg_pos_of_tilted m hμU).ne'
  rw [hμU, integral_tilted]
  simp only [Pi.neg_apply, smul_eq_mul, div_mul_eq_mul_div, integral_div]
  field_simp

/-- **Energy normalization.** In an orthonormal basis and for `μ = m.tilted (-U)`,
`FE_w(f) = Z ∫ (f² + ‖∇f‖²) dμ` with `w = exp (-U)` and `Z = ∫ exp (-U) dm > 0`. -/
theorem weightedFormEnergy_eq_mul_integral {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] (m : Measure V) {U : V → ℝ}
    {μ : Measure V} [IsProbabilityMeasure μ] (hμU : μ = m.tilted (-U)) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) (f : V → ℝ) :
    weightedFormEnergy m (fun x => Real.exp (-U x)) e f =
      (∫ x, Real.exp (-U x) ∂m) * ∫ x, (f x ^ 2 + ‖gradient f x‖ ^ 2) ∂μ := by
  rw [weightedFormEnergy_eq_integral_norm_gradient,
    integral_exp_neg_mul_eq_of_tilted m hμU (fun x => f x ^ 2 + ‖gradient f x‖ ^ 2)]

end Tilted

end FunctionalInequalities.Analysis.WaveSplitting
