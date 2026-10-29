import FunctionalInequalities.Analysis.BakryEmery.Curvature
import FunctionalInequalities.Analysis.Matrix.Positivity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Audit: finite-energy Brascamp–Lieb supports

Source: Letwin, arXiv:2607.24164v1, Lemma A.6 (supports only). A concrete client of the
inverse-quadratic Young inequality `inverse_quadratic_young` for a nonidentity diagonal matrix:
`H = diag(1, 2)` is shown positive definite, `H⁻¹ v` is computed from the actual inverse for
`v = (1, −1)`, and the theorem is invoked with `w = (2, 3)`, giving `−2 ≤ 47/2`. The axiom reports
also cover the compactly supported coercivity `compact_ordinary_diffusion_coercivity`. Not
Brascamp–Lieb or A.6.
-/

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped BigOperators Matrix ContDiff
open FunctionalInequalities.Analysis

namespace LetwinFiniteEnergyAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A concrete two-dimensional diagonal client of `inverse_quadratic_young`. -/
theorem inverse_quadratic_young_diag_client : (-2 : ℝ) ≤ 47 / 2 := by
  classical
  let H : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]
  let v : Fin 2 → ℝ := ![1, -1]
  let w : Fin 2 → ℝ := ![2, 3]
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [v] at h0
  have hw : w ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [w] at h0
  have hHermitian : H.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    change Hᵀ = H
    ext i j
    fin_cases i <;> fin_cases j <;> simp [H]
  have hposvec : ∀ ⦃x : Fin 2 → ℝ⦄, x ≠ 0 →
      0 < star x ⬝ᵥ (H *ᵥ x) := by
    intro x hx
    have hquad : star x ⬝ᵥ (H *ᵥ x) = x 0 ^ 2 + 2 * x 1 ^ 2 := by
      simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pow_two]
      ring
    rw [hquad]
    have hx0 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rcases hx0 with hx0 | hx1
    · nlinarith [sq_pos_of_ne_zero hx0, sq_nonneg (x 1)]
    · nlinarith [sq_nonneg (x 0), sq_pos_of_ne_zero hx1]
  have hH : H.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian hposvec
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hz : H *ᵥ (H⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet]
    simp
  have hinv_v : H⁻¹ *ᵥ v = ![1, -(1 / 2 : ℝ)] := by
    funext i
    fin_cases i
    · change (H⁻¹ *ᵥ v) 0 = 1
      have h := congrFun hz 0
      simpa [H, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
    · change (H⁻¹ *ᵥ v) 1 = -(1 / 2 : ℝ)
      have h := congrFun hz 1
      have h' : 2 * (H⁻¹ *ᵥ v) 1 = -1 := by
        simpa [H, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
      linarith
  have hyoung := inverse_quadratic_young H hH v w
  rw [hinv_v] at hyoung
  convert hyoung using 1 <;>
    norm_num [H, v, w, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end LetwinFiniteEnergyAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity
#print axioms FunctionalInequalities.Analysis.inverse_quadratic_young
#print axioms LetwinFiniteEnergyAudit.inverse_quadratic_young_diag_client
