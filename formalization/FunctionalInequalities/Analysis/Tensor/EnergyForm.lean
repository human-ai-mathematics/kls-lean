import FunctionalInequalities.Analysis.Tensor.SlotAction

/-!
# The energy form of a coordinate tensor

`energyForm A T = ⟨T, (A⁻¹)^{⊗r} T⟩` for an operator `A` and an order-`r` coordinate tensor `T` (BKL arXiv:2610.05474v1, p. 22,
`F(A, T)`), the standard matrix of an operator, `energyForm 1 T = |T|²`, and smoothness near invertible `A`. Proof bodies:
GPT (S-line sub-controller task S-3bF); statements by the S-line sub-controller; placement: Claude.
-/

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-- The matrix of an operator on `ℝⁿ` in the standard basis: `(stdMatrix H) i k = ⟪e_i, H e_k⟫`. -/
def stdMatrix (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫

/-- The energy form `F(A, T) = ⟨T, (A⁻¹)^{⊗r} T⟩ = Σ_{J,J'} T_J T_{J'} Π_s ⟪e_{J_s}, A⁻¹ e_{J'_s}⟫` of BKL
arXiv:2610.05474v1, p. 22 (`A⁻¹ = Ring.inverse A`, the canonical inverse of the operator algebra). -/
def energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : (Fin r → Fin n) → ℝ) : ℝ :=
  ∑ J : Fin r → Fin n, ∑ J' : Fin r → Fin n, T J * T J' *
    ∏ s, ⟪EuclideanSpace.basisFun (Fin n) ℝ (J s), Ring.inverse A (EuclideanSpace.basisFun (Fin n) ℝ (J' s))⟫

private lemma delta_product (J K : Fin r → Fin n) :
    (∏ s, if J s = K s then (1 : ℝ) else 0) =
      if J = K then 1 else 0 := by
  classical
  by_cases h : J = K
  · subst K
    simp
  · rw [if_neg h]
    have hex : ∃ s, J s ≠ K s := by
      by_contra hnone
      apply h
      funext s
      by_contra hs
      exact hnone ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)

/-- At `A = Id` the energy form is the Euclidean norm squared. -/
theorem energyForm_one (T : (Fin r → Fin n) → ℝ) : energyForm 1 T = inner T T := by
  classical
  simp only [energyForm, Ring.inverse_one, one_apply_eq_self,
    OrthonormalBasis.inner_eq_ite]
  simp_rw [delta_product]
  simp [inner, mul_ite]

/-- The energy form is `C²` near every `(A, T)` with `A` a unit. -/
theorem contDiffAt_energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsUnit A)
    (T : (Fin r → Fin n) → ℝ) :
    ContDiffAt ℝ 2 (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
      energyForm q.1 q.2) (A, T) := by
  classical
  have hinv : ContDiffAt ℝ 2 Ring.inverse A := by
    simpa only [hA.unit_spec] using contDiffAt_ringInverse ℝ hA.unit
  have hcoord (J : Fin r → Fin n) :
      ContDiffAt ℝ 2
        (fun q :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
            ((Fin r → Fin n) → ℝ) => q.2 J) (A, T) :=
    (ContinuousLinearMap.proj J :
      ((Fin r → Fin n) → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp
        (A, T) contDiffAt_snd
  unfold energyForm
  apply ContDiffAt.sum
  intro J _
  apply ContDiffAt.sum
  intro K _
  apply ContDiffAt.mul ((hcoord J).mul (hcoord K))
  apply contDiffAt_prod
  intro s _
  exact ContDiffAt.inner ℝ contDiffAt_const
    ((hinv.comp (A, T) contDiffAt_fst).clm_apply contDiffAt_const)

end FunctionalInequalities.Analysis.CoordinateTensor
