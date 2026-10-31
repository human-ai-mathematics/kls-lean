module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Two orthogonal unit vectors

Ordinary real inner-product tools for the tangent-normal frame in CNS1984,
Lemma5.1 p386. Mathlib orthonormal inner sums and Bessel give the actual
norm and projection bounds. No finite dimension or completeness is required.
-/

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities.Analysis

private lemma orthogonal_pair_data {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {u w : G} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0) :
    Orthonormal ℝ (![u, w] : Fin 2 → G) := by
  constructor
  · intro i
    fin_cases i
    · exact hu
    · exact hw
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact huw
    · exact (real_inner_comm u w).trans huw
    · exact (hij rfl).elim

/-- The norm of a linear combination of an orthogonal unit pair. -/
theorem orthogonal_pair_norm_sq {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {u w : G} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0) (a b : ℝ) :
    ‖a • u + b • w‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h :=
    (orthogonal_pair_data hu hw huw).inner_sum (![a, b] : Fin 2 → ℝ) (![a, b] : Fin 2 → ℝ)
      Finset.univ
  simpa [Fin.sum_univ_two, real_inner_self_eq_norm_sq, pow_two] using h

/-- Bessel's inequality for the same orthogonal unit pair. -/
theorem orthogonal_pair_inner_sq_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {u w : G} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0) (x : G) :
    ⟪u, x⟫ ^ 2 + ⟪w, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := (orthogonal_pair_data hu hw huw).sum_inner_products_le x (s := Finset.univ)
  simpa [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using h

end FunctionalInequalities.Analysis
