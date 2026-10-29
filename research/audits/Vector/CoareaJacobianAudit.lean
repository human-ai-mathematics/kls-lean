import FunctionalInequalities.Analysis.Vector.Jacobian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the coarea Jacobian

`Analysis.coareaJacobian` is the linear-algebra layer of the codimension-`m` coarea program.
This client checks what it is and, above all, that it is **compatible with the scalar theory that
is already proved**: the coarea Jacobian of a real-valued differential is literally
`‖gradient u x‖`, the integrand of the scalar `C¹`, Lipschitz and locally Lipschitz coarea
formulas.  Nothing in the scalar chain is restated or weakened through it, and **no coarea formula
is proved here**.

Reported below: the defining identity `J² = det (L ∘ Lᵀ)` on the target, the gradient bridge, the
regular-set characterization `J ≠ 0 ↔ surjective differential`, and boundary cases (identity map,
zero map, subsingleton target).
-/

noncomputable section

open Set FunctionalInequalities FunctionalInequalities.Analysis

namespace CoareaJacobianAudit

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The defining identity, restated: the square is the determinant of `L ∘ Lᵀ` on the **target**,
so it is the `m × m` Gram determinant of the codimension-`m` coarea formula. -/
theorem defining_identity (L : V →L[ℝ] W) :
    0 ≤ coareaJacobian L ∧
      coareaJacobian L ^ 2 =
        LinearMap.det ((L : V →ₗ[ℝ] W) ∘ₗ LinearMap.adjoint (L : V →ₗ[ℝ] W)) :=
  ⟨coareaJacobian_nonneg L, coareaJacobian_sq L⟩

/-- **The compatibility that matters**: for a real-valued function the coarea Jacobian of the
differential is exactly the scalar integrand already used by the proved weighted coarea formula. -/
theorem scalar_case_is_gradient (u : V → ℝ) (x : V) :
    coareaJacobian (fderiv ℝ u x) = ‖gradient u x‖ :=
  coareaJacobian_fderiv u x

/-- The regular set of the codimension-`m` formula. -/
theorem regular_set (L : V →L[ℝ] W) :
    coareaJacobian L ≠ 0 ↔ Function.Surjective (L : V →ₗ[ℝ] W) :=
  coareaJacobian_ne_zero_iff L

/-- In the scalar case the regular set is the usual one: a nonzero differential. -/
theorem scalar_regular_set [Nontrivial V] (u : V → ℝ) (x : V) :
    ‖gradient u x‖ ≠ 0 ↔ Function.Surjective ((fderiv ℝ u x : V →L[ℝ] ℝ) : V →ₗ[ℝ] ℝ) := by
  rw [← coareaJacobian_fderiv u x]
  exact coareaJacobian_ne_zero_iff _

/-! ### Boundary cases -/

/-- The identity has coarea Jacobian one. -/
theorem identity_eq_one : coareaJacobian (ContinuousLinearMap.id ℝ V) = 1 := by
  simp [coareaJacobian]

/-- A subsingleton target makes every map surjective and the Jacobian one; dimension zero in the
target is inside the statement, not excluded by it. -/
theorem subsingleton_target [Subsingleton W] (L : V →L[ℝ] W) :
    coareaJacobian L = 1 :=
  LinearMap.normDet_of_subsingleton _

/-- A map into a nontrivial target that is not surjective has vanishing Jacobian. -/
theorem zero_map [Nontrivial W] : coareaJacobian (0 : V →L[ℝ] W) = 0 := by
  rw [coareaJacobian_eq_zero_iff]
  intro hsurj
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, hv⟩ := hsurj w
  exact hw hv.symm

/-- A concrete two-dimensional example: an orthogonal projection onto a line is a submersion, so it
sits in the regular set. -/
theorem euclidean_proj_regular :
    coareaJacobian (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) ≠ 0 := by
  rw [coareaJacobian_ne_zero_iff]
  intro t
  exact ⟨EuclideanSpace.single (0 : Fin 2) t, by simp⟩

end CoareaJacobianAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.coareaJacobian
#print axioms FunctionalInequalities.Analysis.coareaJacobian_nonneg
#print axioms FunctionalInequalities.Analysis.coareaJacobian_sq
#print axioms FunctionalInequalities.Analysis.adjoint_one
#print axioms FunctionalInequalities.Analysis.coareaJacobian_eq_norm_toDual_symm
#print axioms FunctionalInequalities.Analysis.coareaJacobian_fderiv
#print axioms FunctionalInequalities.Analysis.ker_adjoint
#print axioms FunctionalInequalities.Analysis.coareaJacobian_eq_zero_iff
#print axioms FunctionalInequalities.Analysis.coareaJacobian_ne_zero_iff
#print axioms CoareaJacobianAudit.defining_identity
#print axioms CoareaJacobianAudit.scalar_case_is_gradient
#print axioms CoareaJacobianAudit.regular_set
#print axioms CoareaJacobianAudit.scalar_regular_set
#print axioms CoareaJacobianAudit.identity_eq_one
#print axioms CoareaJacobianAudit.subsingleton_target
#print axioms CoareaJacobianAudit.zero_map
#print axioms CoareaJacobianAudit.euclidean_proj_regular
