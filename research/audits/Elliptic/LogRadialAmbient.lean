module

public import FunctionalInequalities.Analysis.LogRadial.Operator
public import examples.EllipticDrift

/-!
# Clients of the ambient tangent–normal barrier operator margin

Both clients APPLY `tangent_normal_log_radial_barrier_trace_lower`, with `ℓ = Λ = 1`, `ε = 1/24`, `β
= 0`.

* `standard_tangent_skew_client` (`m = 0`, ambient `ℝ²`): tangent `ζ = e₀`, the skew coefficient
  `[[1, k], [-k, 1]]` of the audit fixture with an ARBITRARY `k` (quadratic form `‖v‖²` by the
  fixture's
  `quadratic_identity`), at `x = (1, 1)`. Margin `1 / (4 √2)`.
* `oblique_tangent_identity_client` (`m = 1`, ambient `ℝ³`): the oblique unit tangent `ζ = (1/√2,
  1/√2, 0)`,
  `A = I`, at `x = ζ + e₂`. The unit norm, the tangency and the ellipticity are generated here.
  Margin
  `1 / (4 √2)`, since `⟨ζ, x⟩ = 1` and `x₂ = 1`.
-/

@[expose] public section

noncomputable section
open scoped ContDiff

namespace FunctionalInequalities.Analysis.AmbientBarrierPlaneClient

open FunctionalInequalities.Analysis

/-- **Ambient `ℝ²`, standard tangent, arbitrary skew coefficient.** -/
theorem standard_tangent_skew_client (k : ℝ) :
    let zeta : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]
    let φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
      (Real.sqrt (((∑ i, zeta i * y i) - 0) ^ 2 + (y 1) ^ 2) + ((∑ i, zeta i * y i) - 0) -
          1 / 24 * y 1 * Real.log (((∑ i, zeta i * y i) - 0) ^ 2 + (y 1) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ x ∧
      1 / (4 * Real.sqrt 2) ≤
        Matrix.trace
          (CNSCoefficientScopeAudit.coefficient k *
            ((Matrix.of fun i j =>
                fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                  (EuclideanSpace.single j (1 : ℝ))) :
              Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro zeta x φ
  have hznorm : ‖zeta‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [zeta, Fin.sum_univ_two]
  have hztan : zeta (Fin.last 1) = 0 := by simp [zeta]
  have hell :
    ∀ v : EuclideanSpace ℝ (Fin 2),
      1 * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ∧
        (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ≤ 1 * ‖v‖ ^ 2 :=
    fun v => by
    rw [CNSCoefficientScopeAudit.quadratic_identity, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have h :=
    tangent_normal_log_radial_barrier_trace_lower (m := 0) zeta hznorm hztan
      (CNSCoefficientScopeAudit.coefficient k) (ell := 1) (Λ := 1) (ε := 1 / 24) one_pos one_pos
      (by norm_num) (by norm_num) hell 0 (x := x) (by simp [x])
  have e : ((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2 = 2 := by
    simp [zeta, x, Fin.sum_univ_two]
    norm_num
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [e] at h2
  exact h2

/--
**Ambient `ℝ³`, oblique tangent `(1/√2, 1/√2, 0)`, identity coefficients, point `ζ + e₂`.** -/
theorem oblique_tangent_identity_client :
    let zeta : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1 / Real.sqrt 2, 1 / Real.sqrt 2, 0]
    let x : EuclideanSpace ℝ (Fin 3) := zeta + EuclideanSpace.single 2 1
    let φ : EuclideanSpace ℝ (Fin 3) → ℝ := fun y =>
      (Real.sqrt (((∑ i, zeta i * y i) - 0) ^ 2 + (y 2) ^ 2) + ((∑ i, zeta i * y i) - 0) -
          1 / 24 * y 2 * Real.log (((∑ i, zeta i * y i) - 0) ^ 2 + (y 2) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ x ∧
      1 / (4 * Real.sqrt 2) ≤
        Matrix.trace
          ((1 : Matrix (Fin 3) (Fin 3) ℝ) *
            ((Matrix.of fun i j =>
                fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                  (EuclideanSpace.single j (1 : ℝ))) :
              Matrix (Fin 3) (Fin 3) ℝ)) := by
  intro zeta x φ
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hs4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2]
    norm_num
      -- generated: unit norm, tangency, ellipticity of the identity

  have hznorm : ‖zeta‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [zeta, Fin.sum_univ_three, hs2]
    norm_num
  have hztan : zeta (Fin.last 2) = 0 := by simp [zeta]
  have hell :
    ∀ v : EuclideanSpace ℝ (Fin 3),
      1 * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * v i * v j) ∧
        (∑ i, ∑ j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * v i * v j) ≤ 1 * ‖v‖ ^ 2 :=
    fun v => by
    have hq : (∑ i, ∑ j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * v i * v j) = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Matrix.one_apply, Fin.sum_univ_three, sq_abs]
      ring
    rw [hq, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hx : 0 < x (Fin.last 2) := by simp [x, zeta]
  have h :=
    tangent_normal_log_radial_barrier_trace_lower (m := 1) zeta hznorm hztan
      (1 : Matrix (Fin 3) (Fin 3) ℝ) (ell := 1) (Λ := 1) (ε := 1 / 24) one_pos one_pos
      (by norm_num) (by norm_num) hell 0 hx
  have e : ((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 2)) ^ 2 = 2 := by
    simp [zeta, x, Fin.sum_univ_three]
    field_simp
    rw [hs4]
    norm_num
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [e] at h2
  exact h2

end FunctionalInequalities.Analysis.AmbientBarrierPlaneClient

#print axioms FunctionalInequalities.Analysis.AmbientBarrierPlaneClient.standard_tangent_skew_client
#print axioms
  FunctionalInequalities.Analysis.AmbientBarrierPlaneClient.oblique_tangent_identity_client
