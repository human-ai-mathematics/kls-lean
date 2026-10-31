module

public import FunctionalInequalities.Analysis.Convex.Quadratic

/-!
# Polynomial half-ball barrier

Caffarelli–Nirenberg–Spruck CPAM37(1984), Lemma5.1 p386: actual
polynomial differential data and generated negative operator margin. The same
ordinary height-budget floor serves nonnegativity and curved-boundary control.
Ambient m+1 includes the line; no solution or boundary comparison is assumed.
-/

@[expose] public section

noncomputable section
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis

private def halfballHessian (m : ℕ) (E : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  Matrix.diagonal (fun i => 2 - if i = Fin.last m then 2 * (E + 1) else 0)

private lemma halfballHessian_apply (m : ℕ) (E : ℝ) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    Matrix.toEuclideanLin (halfballHessian m E) x =
      (2 : ℝ) • x - (2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) 1 := by
  ext i
  simp only [halfballHessian, Matrix.toLpLin_apply 2 2, Matrix.mulVec_diagonal,
    WithLp.ofLp_toLp, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hi : i = Fin.last m
  · subst i
    simp
    ring
  · simp [hi]

private lemma halfball_polynomial_quadratic (m : ℕ) (E : ℝ) :
    (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        x (Fin.last m) + ‖x‖ ^ 2 - (E + 1) * (x (Fin.last m)) ^ 2) =
      quadraticAt (halfballHessian m E) 0 (EuclideanSpace.single (Fin.last m) 1) 0 := by
  funext x
  simp only [quadraticAt, sub_zero, zero_add, halfballHessian_apply,
    EuclideanSpace.inner_single_left, map_one, one_mul, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, EuclideanSpace.inner_single_right, starRingEnd_apply,
    star_trivial]
  ring

/-- The actual polynomial is one canonical quadratic: all-order smoothness,
coordinate Hessian and actual Frechet evaluations share the existing producers. -/
theorem halfball_polynomial_differential_data (m : ℕ) (E : ℝ) :
    let P : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun x =>
      x (Fin.last m) + ‖x‖ ^ 2 - (E + 1) * (x (Fin.last m)) ^ 2
    ContDiff ℝ ∞ P ∧
      (∀ x,
          hessianMatrix P x =
            Matrix.diagonal (fun i => 2 - if i = Fin.last m then 2 * (E + 1) else 0)) ∧
        (∀ x b,
          (fderiv ℝ P x) b =
            ⟪EuclideanSpace.single (Fin.last m) 1 + (2 : ℝ) • x -
                (2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) 1,
              b⟫) := by
  dsimp only
  rw [halfball_polynomial_quadratic]
  have hh : (halfballHessian m E).IsHermitian := Matrix.isHermitian_diagonal _
  refine
    ⟨contDiff_quadraticAt_all _ _ _ _, fun x => by
      simpa only [halfballHessian] using
        hessianMatrix_quadraticAt hh 0 (EuclideanSpace.single (Fin.last m) 1) 0 x,
      ?_⟩
  intro x b
  rw [← inner_gradient_left, gradient_quadraticAt hh, sub_zero, halfballHessian_apply]
  congr 1
  abel

private lemma halfball_tangent_norm (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖x‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i : Fin m => x i.castSucc) : EuclideanSpace ℝ (Fin m))‖ ^ 2 +
        (x (Fin.last m)) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact Fin.sum_univ_castSucc _

private lemma halfball_coefficient_diag (m : ℕ) {ell Λ : ℝ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hell :
      ∀ w : EuclideanSpace ℝ (Fin (m + 1)),
        ell * ‖w‖ ^ 2 ≤ (∑ i, ∑ j, A i j * w i * w j) ∧
          (∑ i, ∑ j, A i j * w i * w j) ≤ Λ * ‖w‖ ^ 2)
    (i : Fin (m + 1)) : ell ≤ A i i ∧ A i i ≤ Λ := by
  simpa [PiLp.single_apply] using hell (EuclideanSpace.single i 1)

private lemma halfball_trace (m : ℕ) (E : ℝ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    Matrix.trace (A * halfballHessian m E) =
      2 * Matrix.trace A - 2 * (E + 1) * A (Fin.last m) (Fin.last m) := by
  change
    (∑ i, (A * halfballHessian m E) i i) =
      2 * (∑ i, A i i) - 2 * (E + 1) * A (Fin.last m) (Fin.last m)
  simp only [halfballHessian, Matrix.mul_diagonal, mul_sub, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  ring

private lemma halfball_gradient_norm (m : ℕ) {E : ℝ} (hE : 0 < E)
    (x : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖EuclideanSpace.single (Fin.last m) (1 : ℝ) + (2 : ℝ) • x -
          (2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ ≤
      1 + 2 * (E + 2) * ‖x‖ := by
  have hcoord : |x (Fin.last m)| ≤ ‖x‖ := PiLp.norm_apply_le x _
  calc
    _ ≤
        ‖EuclideanSpace.single (Fin.last m) (1 : ℝ) + (2 : ℝ) • x‖ +
          ‖(2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ :=
      norm_sub_le _ _
    _ ≤
        (‖EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ + ‖(2 : ℝ) • x‖) +
          ‖(2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = 1 + 2 * ‖x‖ + 2 * (E + 1) * |x (Fin.last m)| := by
      simp only [norm_smul, PiLp.norm_single, Real.norm_eq_abs, abs_one, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by linarith : 0 < E + 1), mul_one]
    _ ≤ 1 + 2 * (E + 2) * ‖x‖ := by nlinarith

/-- A height budget makes the actual polynomial dominate the squared norm. -/
theorem halfball_polynomial_norm_floor {m : ℕ} {E : ℝ} {x : EuclideanSpace ℝ (Fin (m + 1))}
    (hxn : 0 ≤ x (Fin.last m)) (hbudget : (E + 1) * x (Fin.last m) ≤ 1) :
    ‖x‖ ^ 2 ≤ x (Fin.last m) + ‖x‖ ^ 2 - (E + 1) * (x (Fin.last m)) ^ 2 := by
  have h := mul_nonneg hxn (sub_nonneg.mpr hbudget)
  nlinarith

/-- On the curved boundary the same height budget gives the radius-squared floor. -/
theorem halfball_polynomial_curved_lower {m : ℕ} {E δ : ℝ} (hE : 0 ≤ E)
    (hsmall : δ ≤ 1 / (2 * (E + 1))) (x : EuclideanSpace ℝ (Fin (m + 1))) (hnorm : ‖x‖ = δ)
    (hxn : 0 ≤ x (Fin.last m)) :
    δ ^ 2 ≤ x (Fin.last m) + ‖x‖ ^ 2 - (E + 1) * (x (Fin.last m)) ^ 2 := by
  have hcoord : x (Fin.last m) ≤ δ :=
    (le_abs_self _).trans ((PiLp.norm_apply_le x _).trans hnorm.le)
  have hbudget : (E + 1) * x (Fin.last m) ≤ 1 := by
    have hd := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (E + 1))).mp hsmall
    nlinarith
  simpa only [hnorm] using halfball_polynomial_norm_floor hxn hbudget

theorem exists_halfball_polynomial_negative_operator (m : ℕ) {ell Λ B : ℝ} (hell_pos : 0 < ell)
    (hΛ : 0 < Λ) (hB : 0 ≤ B) :
    ∃ E δ : ℝ,
      0 < E ∧
        0 < δ ∧
          δ < 1 ∧
            let P : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := fun y =>
              y (Fin.last m) + ‖y‖ ^ 2 - (E + 1) * (y (Fin.last m)) ^ 2
            ContDiff ℝ ∞ P ∧
              (∀ y,
                  P y =
                    y (Fin.last m) +
                        ‖(WithLp.toLp 2 (fun i : Fin m => y i.castSucc) :
                              EuclideanSpace ℝ (Fin m))‖ ^
                          2 -
                      E * (y (Fin.last m)) ^ 2) ∧
                ∀ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
                  (_hell :
                    ∀ w : EuclideanSpace ℝ (Fin (m + 1)),
                      ell * ‖w‖ ^ 2 ≤ (∑ i, ∑ j, A i j * w i * w j) ∧
                        (∑ i, ∑ j, A i j * w i * w j) ≤ Λ * ‖w‖ ^ 2)
                  (b : EuclideanSpace ℝ (Fin (m + 1))) (_hb : ‖b‖ ≤ B) (a : ℝ) (_ha : a ≤ 0)
                  (x : EuclideanSpace ℝ (Fin (m + 1))) (_hxn : 0 ≤ x (Fin.last m))
                  (_hx : ‖x‖ < δ),
                  0 ≤ P x ∧
                    Matrix.trace
                            (A * FunctionalInequalities.Probability.Stein.hessianMatrix P x) +
                          (fderiv ℝ P x) b +
                        a * P x ≤
                      -1 := by
  let N : ℝ := m + 1
  let E : ℝ := (N * Λ + B + 1) / ell + 1
  have hN : 0 < N := by dsimp [N]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hEmul : (E - 1) * ell = N * Λ + B + 1 := by
    dsimp [E]
    field_simp
    ring
  let δ : ℝ := min (1 / 2) (1 / (4 * (E + 2)))
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨E, δ, hE, hδ0, hδ1, ?_⟩
  intro P
  have data := halfball_polynomial_differential_data m E
  refine ⟨data.1, ?_, ?_⟩
  · intro y
    have hn := halfball_tangent_norm m y
    dsimp [P]
    rw [hn]
    ring
  · intro A hell b hb a ha x hxn hx
    have diag := halfball_coefficient_diag m A hell
    have htrace : Matrix.trace A ≤ N * Λ := by
      calc
        Matrix.trace A = ∑ i, A i i := rfl
        _ ≤ ∑ _i : Fin (m + 1), Λ := Finset.sum_le_sum (fun i _ => (diag i).2)
        _ = N * Λ := by simp [N]
    have hxnabs : |x (Fin.last m)| ≤ ‖x‖ := PiLp.norm_apply_le x _
    have hxnle : x (Fin.last m) ≤ ‖x‖ := (le_abs_self _).trans hxnabs
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hxsmall : ‖x‖ * (4 * (E + 2)) < 1 := by
      have hxδ : ‖x‖ < 1 / (4 * (E + 2)) := lt_of_lt_of_le hx (min_le_right _ _)
      exact (lt_div_iff₀ (by positivity)).mp hxδ
    have hbudget : (E + 1) * x (Fin.last m) ≤ 1 := by nlinarith
    have hP : 0 ≤ P x := by
      exact (sq_nonneg ‖x‖).trans (halfball_polynomial_norm_floor hxn hbudget)
    have hG :
      ‖EuclideanSpace.single (Fin.last m) (1 : ℝ) + (2 : ℝ) • x -
            (2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ ≤
        2 := by
      calc
        _ ≤ 1 + 2 * (E + 2) * ‖x‖ := halfball_gradient_norm m hE x
        _ ≤ 2 := by nlinarith
    have hDrift : (fderiv ℝ P x) b ≤ 2 * B := by
      rw [data.2.2 x b]
      calc
        _ ≤
            ‖EuclideanSpace.single (Fin.last m) (1 : ℝ) + (2 : ℝ) • x -
                  (2 * (E + 1) * x (Fin.last m)) • EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ *
              ‖b‖ :=
          real_inner_le_norm _ _
        _ ≤ 2 * B := mul_le_mul hG hb (norm_nonneg b) (by norm_num)
    have hHess : hessianMatrix P x = halfballHessian m E := data.2.1 x
    have hzero : a * P x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hP
    refine ⟨hP, ?_⟩
    rw [hHess, halfball_trace]
    have hn :=
      mul_le_mul_of_nonneg_left (diag (Fin.last m)).1 (show 0 ≤ 2 * (E + 1) by positivity)
    nlinarith

end FunctionalInequalities.Analysis

end
