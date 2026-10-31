module

public import FunctionalInequalities.Analysis.Elliptic.Barrier
public import examples.EllipticDrift
@[expose] public section

noncomputable section
open scoped ContDiff
namespace FunctionalInequalities.Analysis
namespace HalfBallPolynomialClient

private lemma generated_normal_point (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let x : EuclideanSpace ℝ (Fin (m + 1)) := (δ / 2) • EuclideanSpace.single (Fin.last m) 1
    x (Fin.last m) = δ / 2 ∧ 0 < x (Fin.last m) ∧ ‖x‖ < δ := by
  dsimp only
  have he :
    ((δ / 2) • EuclideanSpace.single (Fin.last m) (1 : ℝ) : EuclideanSpace ℝ (Fin (m + 1)))
        (Fin.last m) =
      δ / 2 := by
    simp
  refine ⟨he, ?_, ?_⟩
  · rw [he]; positivity
  · rw [norm_smul, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity)]
    norm_num
    linarith

theorem generated_scalar_polynomial_client :
    ∃ E δ : ℝ,
      0 < E ∧
        0 < δ ∧
          δ < 1 ∧
            let P : EuclideanSpace ℝ (Fin 1) → ℝ := fun y => y 0 + ‖y‖ ^ 2 - (E + 1) * (y 0) ^ 2
            let x : EuclideanSpace ℝ (Fin 1) := (δ / 2) • EuclideanSpace.single 0 1
            ContDiff ℝ ∞ P ∧
              0 < x 0 ∧
                0 ≤ P x ∧
                  Matrix.trace
                          ((1 : Matrix (Fin 1) (Fin 1) ℝ) *
                            FunctionalInequalities.Probability.Stein.hessianMatrix P x) +
                        (fderiv ℝ P x) (-EuclideanSpace.single 0 1) +
                      (-7) * P x ≤
                    -1 := by
  obtain ⟨E, δ, hE, hδ0, hδ1, h⟩ :=
    exists_halfball_polynomial_negative_operator 0 (ell := 1) (Λ := 1) (B := 1) one_pos one_pos
      (by norm_num)
  refine ⟨E, δ, hE, hδ0, hδ1, ?_⟩
  intro P x
  have hp := generated_normal_point 0 hδ0
  have hell :
    ∀ w : EuclideanSpace ℝ (Fin 1),
      1 * ‖w‖ ^ 2 ≤ (∑ i, ∑ j, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j * w i * w j) ∧
        (∑ i, ∑ j, (1 : Matrix (Fin 1) (Fin 1) ℝ) i j * w i * w j) ≤ 1 * ‖w‖ ^ 2 := by
    intro w
    simp only [EuclideanSpace.real_norm_sq_eq]
    simp [pow_two]
  have hb : ‖(-EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 1))‖ ≤ 1 := by simp
  have hh := h.2.2 1 hell (-EuclideanSpace.single 0 1) hb (-7) (by norm_num) x hp.2.1.le hp.2.2
  exact ⟨h.1, hp.2.1, hh⟩

theorem generated_skew_polynomial_client (k : ℝ) :
    ∃ E δ : ℝ,
      0 < E ∧
        0 < δ ∧
          δ < 1 ∧
            let P : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => y 1 + ‖y‖ ^ 2 - (E + 1) * (y 1) ^ 2
            let x : EuclideanSpace ℝ (Fin 2) := (δ / 2) • EuclideanSpace.single 1 1
            ContDiff ℝ ∞ P ∧
              0 < x 1 ∧
                0 ≤ P x ∧
                  Matrix.trace
                          ((!![1, k; -k, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
                            FunctionalInequalities.Probability.Stein.hessianMatrix P x) +
                        (fderiv ℝ P x) (WithLp.toLp 2 ![1, -1]) +
                      (-3) * P x ≤
                    -1 := by
  obtain ⟨E, δ, hE, hδ0, hδ1, h⟩ :=
    exists_halfball_polynomial_negative_operator 1 (ell := 1) (Λ := 1) (B := 2) one_pos one_pos
      (by norm_num)
  refine ⟨E, δ, hE, hδ0, hδ1, ?_⟩
  intro P x
  have hp := generated_normal_point 1 hδ0
  have hell :
    ∀ w : EuclideanSpace ℝ (Fin 2),
      1 * ‖w‖ ^ 2 ≤ (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * w i * w j) ∧
        (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * w i * w j) ≤ 1 * ‖w‖ ^ 2 := by
    intro w
    rw [CNSCoefficientScopeAudit.quadratic_identity, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hb : ‖(WithLp.toLp 2 ![1, -1] : EuclideanSpace ℝ (Fin 2))‖ ≤ 2 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  have hh :=
    h.2.2 (CNSCoefficientScopeAudit.coefficient k) hell (WithLp.toLp 2 ![1, -1]) hb (-3)
      (by norm_num) x hp.2.1.le hp.2.2
  exact ⟨h.1, hp.2.1, hh⟩

end HalfBallPolynomialClient
end FunctionalInequalities.Analysis
#print axioms
  FunctionalInequalities.Analysis.HalfBallPolynomialClient.generated_scalar_polynomial_client
#print axioms
  FunctionalInequalities.Analysis.HalfBallPolynomialClient.generated_skew_polynomial_client
