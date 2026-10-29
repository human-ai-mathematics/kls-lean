import FunctionalInequalities.Analysis.Matrix.Positivity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete skew elliptic coefficients and drift points

The family `[[1,k],[-k,1]]` has identity symmetric part and quadratic form;
its raw entries need not be bounded by the ellipticity constants. The chosen
positive-radius point, tangent and nonzero drift give explicit norm, distance
and coefficient data for the half-ball/logarithmic-barrier examples supporting
Caffarelli–Nirenberg–Spruck CPAM 37 (1984), Lemma 5.1.
-/
noncomputable section
open scoped Matrix.Norms.Elementwise

namespace CNSCoefficientScopeAudit

def coefficient (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, k; -k, 1]

theorem quadratic_identity (k : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ i, ∑ j, coefficient k i j * x i * x j) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, coefficient, Real.norm_eq_abs, sq_abs]
  ring

theorem symmetric_part_identity (k : ℝ) :
    (1 / 2 : ℝ) • (coefficient k + (coefficient k).transpose) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coefficient] <;> ring

theorem trace_identity (k : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ) (hH : H.IsHermitian) :
    Matrix.trace (coefficient k * H) = Matrix.trace H := by
  have h01 : H 0 1 = H 1 0 := by simpa using hH.apply 1 0
  simp [Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_two, coefficient, h01]

theorem coefficient_not_posSemidef {k : ℝ} (hk : k ≠ 0) : ¬ (coefficient k).PosSemidef := by
  intro h
  have hh := h.isHermitian.apply 0 1
  simp [coefficient] at hh
  apply hk
  linarith

theorem elliptic_quadratic_bounds_do_not_bound_original_entries :
    (∀ x : EuclideanSpace ℝ (Fin 2),
      (1 : ℝ)⁻¹ * ‖x‖ ^ 2 ≤ ∑ i, ∑ j, coefficient 7 i j * x i * x j ∧
      (∑ i, ∑ j, coefficient 7 i j * x i * x j) ≤ 1 * ‖x‖ ^ 2) ∧
      ¬ (coefficient 7).PosSemidef ∧ 1 < ‖coefficient 7‖ := by
  refine ⟨fun x => by rw [quadratic_identity]; norm_num, coefficient_not_posSemidef (by norm_num), ?_⟩
  have h := Matrix.norm_entry_le_entrywise_sup_norm (coefficient 7) (i := (0 : Fin 2)) (j := (1 : Fin 2))
  have h7 : (7 : ℝ) ≤ ‖coefficient 7‖ := by simpa [coefficient] using h
  linarith

end CNSCoefficientScopeAudit

namespace FunctionalInequalities.Analysis.LogRadialDriftPointFixture

theorem drift_point_geometry {ρ : ℝ} (hρ0 : 0 < ρ) (k : ℝ) :
    let zeta : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![ρ / (2 * Real.sqrt 2), ρ / (2 * Real.sqrt 2)]
    let b : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1]
    ‖zeta‖ = 1 ∧ zeta (Fin.last 1) = 0 ∧ b ≠ 0 ∧ ‖b‖ ≤ 2 ∧ 0 < x (Fin.last 1) ∧
      ((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2 = (ρ / 2) ^ 2 ∧
      Real.sqrt (((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2) = ρ / 2 ∧
      ∀ v : EuclideanSpace ℝ (Fin 2),
        1 * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ∧
          (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ≤ 1 * ‖v‖ ^ 2 := by
  intro zeta x b
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have ht : 0 < ρ / (2 * Real.sqrt 2) := by positivity
  have hz : ‖zeta‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [zeta, Fin.sum_univ_two]
  have hztan : zeta (Fin.last 1) = 0 := by simp [zeta]
  have hell : ∀ v : EuclideanSpace ℝ (Fin 2),
      1 * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ∧
        (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ≤ 1 * ‖v‖ ^ 2 := fun v => by
    rw [CNSCoefficientScopeAudit.quadratic_identity, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hb : ‖b‖ ≤ 2 := by
    rw [EuclideanSpace.norm_eq]
    simp [b, Fin.sum_univ_two]
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hb0 : b ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h0
    simp [b] at h1
  have hx : 0 < x (Fin.last 1) := by simpa [x] using ht
  have hS : ((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2 = (ρ / 2) ^ 2 := by
    simp [zeta, x, Fin.sum_univ_two]
    field_simp
    rw [hs2]
    ring
  refine ⟨hz, hztan, hb0, hb, hx, hS, ?_, hell⟩
  rw [hS, Real.sqrt_sq (by positivity)]

end FunctionalInequalities.Analysis.LogRadialDriftPointFixture
