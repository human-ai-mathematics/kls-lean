module

public import FunctionalInequalities.Analysis.Operator.InverseSqrt
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Audit: the principal inverse square root

Clients of `Analysis/PrincipalInverseSqrt.lean`: the Mathlib matrix `CFC.sqrt` API facts the
construction relies on (square, positive self-adjoint branch, uniqueness; namespace
`PrincipalSqrtAPI`), the scalar operator `4·Id ↦ ½·Id` with the negative factor rejected, and the
nondiagonal consumer `B = [[2,1],[1,2]]`, `A = (B²)⁻¹`, `inverseSqrt A = B`, off-diagonal action
`1`, operator norm `> 1`. Local regularity clients (section `LocalLipschitz`): the canonical roots
`B = [[2,1],[1,2]]` and `T = diag(1,2)` of two operators do not commute, their Frobenius
difference squared is `3`, the squared-root difference has norm `7`, and the Sylvester estimate
gives `2‖B − T‖_F ≤ 7`; the empty-coordinate canonical coefficient is locally Lipschitz and zero.
No claim that these operators are covariances of a source law.
-/

@[expose] public section

noncomputable section
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace MatrixOrder

namespace PrincipalSqrtAPI
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem actual_matrix_square (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem actual_matrix_branch (A : Matrix n n ℝ) :
    IsSelfAdjoint (CFC.sqrt A) ∧ (CFC.sqrt A).PosSemidef :=
  ⟨IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A), Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)⟩

theorem actual_matrix_unique (A S : Matrix n n ℝ) (hS : S.PosSemidef) (hs : S * S = A) :
    CFC.sqrt A = S := CFC.sqrt_unique hs hS.nonneg
end PrincipalSqrtAPI

namespace ActualPrincipalSqrt
private def fourUnit : (ℝ →L[ℝ] ℝ)ˣ where
  val := (4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  inv := (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ
  val_inv := by apply ContinuousLinearMap.ext; intro x; norm_num [mul_apply_eq_comp]; ring
  inv_val := by apply ContinuousLinearMap.ext; intro x; norm_num [mul_apply_eq_comp]; ring

private theorem four_inverse :
    Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) =
      (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ := Ring.inverse_unit fourUnit

/-- An actual nonorthogonal scaling operator fixes the positive branch to +1/2. -/
theorem scale_four_root :
    inverseSqrt ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) =
      (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  apply inverseSqrt_unique _ _ fourUnit.isUnit
  · exact (ContinuousLinearMap.isPositive_iff' _).mpr
      ⟨by change IsSelfAdjoint ((1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)); simp [IsSelfAdjoint, star_smul],
        by intro x
           simp only [smul_apply, ContinuousLinearMap.id_apply,
             Real.inner_apply, smul_eq_mul]
           nlinarith [sq_nonneg x]⟩
  · change (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ *
      (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ =
      Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    rw [four_inverse]
    apply ContinuousLinearMap.ext
    intro x
    norm_num [mul_apply_eq_comp]; ring

theorem scale_four_action : inverseSqrt ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 3 = 3 / 2 := by
  rw [scale_four_root]
  norm_num

/-- The negative factor has the same Gram matrix, but cannot be the principal branch. -/
theorem negative_factor_rejected :
    (-(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) *
        (-(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).adjoint =
      Ring.inverse ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) ∧
    inverseSqrt ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) ≠
      -(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  constructor
  · rw [four_inverse]
    have hsa : (-(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).adjoint =
        -(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
      change IsSelfAdjoint (-(1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))
      simp [IsSelfAdjoint, star_smul]
    rw [hsa]
    apply ContinuousLinearMap.ext
    intro x
    norm_num [mul_apply_eq_comp]; ring
  · rw [scale_four_root]
    intro h
    have hh := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h
    norm_num at hh
end ActualPrincipalSqrt

namespace IndependentPrincipalRoot
abbrev E := EuclideanSpace ℝ (Fin 2)
def b : OrthonormalBasis (Fin 2) ℝ E := EuclideanSpace.basisFun (Fin 2) ℝ
def B : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
def A : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 9, -(4 / 9); -(4 / 9), 5 / 9]
def Bop : E →L[ℝ] E := operatorOfMatrix b B
def Aop : E →L[ℝ] E := operatorOfMatrix b A

theorem B_positive : B.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.conjTranspose_apply]
  · intro v
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial, B,
      Matrix.of_apply]
    norm_num
    nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0), sq_nonneg (v 1)]

theorem A_unit : IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  apply isUnit_iff_ne_zero.mpr
  norm_num [A, Matrix.det_fin_two]

theorem A_inverse : A⁻¹ = B * B := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two]

theorem Aop_unit : IsUnit Aop := by
  apply (operatorMatrix_isUnit_iff b Aop).mp
  simpa only [Aop, operatorMatrix_operatorOfMatrix] using A_unit

theorem principal_nondiagonal : inverseSqrt Aop = Bop := by
  apply inverseSqrt_unique Aop Bop Aop_unit
  · exact operatorOfMatrix_isPositive b B B_positive
  · apply operatorMatrix_injective b
    rw [operatorMatrix_mul, ← operatorMatrix_ringInverse b Aop Aop_unit]
    simp only [Aop, Bop, operatorMatrix_operatorOfMatrix, A_inverse]

theorem principal_actual_matrix : operatorMatrix b (inverseSqrt Aop) = !![2, 1; 1, 2] := by
  rw [principal_nondiagonal]
  exact operatorMatrix_operatorOfMatrix b B


theorem A_positive : A.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, Matrix.conjTranspose_apply]
  · intro v
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial, A,
      Matrix.of_apply]
    norm_num
    nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0 - v 1)]

theorem actual_nondiagonal_spec :
    (inverseSqrt Aop).IsPositive ∧ IsSelfAdjoint (inverseSqrt Aop) ∧
      inverseSqrt Aop * inverseSqrt Aop = Ring.inverse Aop ∧
      inverseSqrt Aop * (inverseSqrt Aop).adjoint = Ring.inverse Aop ∧
      Aop * (inverseSqrt Aop * (inverseSqrt Aop).adjoint) = 1 ∧
      (inverseSqrt Aop * (inverseSqrt Aop).adjoint) * Aop = 1 :=
  inverseSqrt_spec Aop (operatorOfMatrix_isPositive b A A_positive) Aop_unit


theorem principal_matrix_entry (i j : Fin 2) :
    ⟪b i, inverseSqrt Aop (b j)⟫ = B i j := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) principal_actual_matrix
  change LinearMap.toMatrixOrthonormal b (inverseSqrt Aop).toLinearMap i j = B i j at h
  rw [LinearMap.toMatrixOrthonormal_apply_apply] at h
  exact h

theorem actual_offdiagonal_action : ⟪b 1, inverseSqrt Aop (b 0)⟫ = 1 := by
  simpa [B] using principal_matrix_entry 1 0

theorem actual_principal_norm_gt_one : 1 < ‖inverseSqrt Aop‖ := by
  have hn : ‖b (0 : Fin 2)‖ = 1 := b.norm_eq_one 0
  have hquad : ⟪b 0, inverseSqrt Aop (b 0)⟫ = 2 := by
    simpa [B] using principal_matrix_entry 0 0
  have h := norm_inner_le_norm (𝕜 := ℝ) (b 0) (inverseSqrt Aop (b 0))
  rw [hquad, hn] at h
  norm_num at h
  have hop := (inverseSqrt Aop).le_opNorm (b 0)
  rw [hn, mul_one] at hop
  linarith
end IndependentPrincipalRoot

#print axioms FunctionalInequalities.Analysis.operatorMatrix_apply_eq_operatorEntry
#print axioms FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff
#print axioms FunctionalInequalities.Analysis.inner_self_pos_of_isPositive_of_isUnit
#print axioms FunctionalInequalities.Analysis.inverseSqrt_spec
#print axioms FunctionalInequalities.Analysis.inverseSqrt_unique
#print axioms FunctionalInequalities.Analysis.inverseSqrtIn_eq_of_basis
#print axioms PrincipalSqrtAPI.actual_matrix_unique
#print axioms ActualPrincipalSqrt.scale_four_root
#print axioms ActualPrincipalSqrt.negative_factor_rejected
#print axioms IndependentPrincipalRoot.principal_nondiagonal
#print axioms IndependentPrincipalRoot.actual_nondiagonal_spec
#print axioms IndependentPrincipalRoot.actual_offdiagonal_action
#print axioms IndependentPrincipalRoot.actual_principal_norm_gt_one

namespace ActualPrincipalRegularityClients
open Matrix
open scoped Matrix.Norms.L2Operator

abbrev E := EuclideanSpace ℝ (Fin 2)
def b : OrthonormalBasis (Fin 2) ℝ E := EuclideanSpace.basisFun (Fin 2) ℝ
def B : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]
def T : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]
def A : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 9, -(4 / 9); -(4 / 9), 5 / 9]
def C : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1 / 4]

theorem B_floor : QuadraticFloor B 1 := by
  intro v
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, B, Matrix.of_apply]
  norm_num
  nlinarith [sq_nonneg (v 0 + v 1)]

theorem T_floor : QuadraticFloor T 1 := by
  intro v
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, T, Matrix.of_apply]
  norm_num
  nlinarith [sq_nonneg (v 1)]

theorem roots_noncommute : B * T ≠ T * B := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [B, T, Matrix.mul_apply, Fin.sum_univ_two] at h01

private theorem B_positive : B.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.conjTranspose_apply]
  · intro v
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial, B,
      Matrix.of_apply]
    norm_num
    nlinarith [sq_nonneg (v 0 + v 1), sq_nonneg (v 0), sq_nonneg (v 1)]

private theorem T_positive : T.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [T, Matrix.conjTranspose_apply]
  · intro v
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, star_trivial, T,
      Matrix.of_apply]
    norm_num
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

private theorem A_unit : IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  apply isUnit_iff_ne_zero.mpr
  norm_num [A, Matrix.det_fin_two]

private theorem C_unit : IsUnit C := by
  apply (Matrix.isUnit_iff_isUnit_det C).mpr
  apply isUnit_iff_ne_zero.mpr
  norm_num [C, Matrix.det_fin_two]

private theorem A_inverse : A⁻¹ = B * B := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_two]

private theorem C_inverse : C⁻¹ = T * T := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [C, T, Matrix.mul_apply, Fin.sum_univ_two]

private theorem canonical_B : inverseSqrt (operatorOfMatrix b A) = operatorOfMatrix b B := by
  have hu : IsUnit (operatorOfMatrix b A) :=
    (operatorMatrix_isUnit_iff b _).mp
      (by simpa only [operatorMatrix_operatorOfMatrix] using A_unit)
  apply inverseSqrt_unique _ _ hu (operatorOfMatrix_isPositive b B B_positive)
  apply operatorMatrix_injective b
  rw [operatorMatrix_mul, ← operatorMatrix_ringInverse b _ hu]
  simp only [operatorMatrix_operatorOfMatrix, A_inverse]

private theorem canonical_T : inverseSqrt (operatorOfMatrix b C) = operatorOfMatrix b T := by
  have hu : IsUnit (operatorOfMatrix b C) :=
    (operatorMatrix_isUnit_iff b _).mp
      (by simpa only [operatorMatrix_operatorOfMatrix] using C_unit)
  apply inverseSqrt_unique _ _ hu (operatorOfMatrix_isPositive b T T_positive)
  apply operatorMatrix_injective b
  rw [operatorMatrix_mul, ← operatorMatrix_ringInverse b _ hu]
  simp only [operatorMatrix_operatorOfMatrix, C_inverse]

/-- The two canonical roots do not commute. -/
theorem actual_canonical_noncommute :
    inverseSqrt (operatorOfMatrix b A) * inverseSqrt (operatorOfMatrix b C) ≠
      inverseSqrt (operatorOfMatrix b C) * inverseSqrt (operatorOfMatrix b A) := by
  rw [canonical_B, canonical_T]
  intro h
  apply roots_noncommute
  have hm := congrArg (operatorMatrix b) h
  simpa only [operatorMatrix_mul, operatorMatrix_operatorOfMatrix] using hm

/-- The Sylvester estimate on the canonical roots: `2‖B − T‖_F ≤ ‖B² − T²‖_F = 7`. -/
theorem actual_canonical_bound :
    2 *
        ‖matrixEntries
            (operatorMatrix b (inverseSqrt (operatorOfMatrix b A)) -
              operatorMatrix b (inverseSqrt (operatorOfMatrix b C)))‖ ≤
      7 := by
  rw [canonical_B, canonical_T, operatorMatrix_operatorOfMatrix,
    operatorMatrix_operatorOfMatrix]
  have hs : ∀ i j, T i j = T j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [T]
  have h := root_difference_bound B T B_floor T_floor hs
  have hn : ‖matrixEntries (B * B - T * T)‖ = 7 := by
    have hsq : ‖matrixEntries (B * B - T * T)‖ ^ 2 = 49 := by
      rw [matrixEntries_norm_sq]
      norm_num [B, T, Matrix.mul_apply, Fin.sum_univ_two]
    nlinarith [norm_nonneg (matrixEntries (B * B - T * T))]
  norm_num [hn] at h ⊢
  exact h

theorem actual_canonical_difference_nonzero :
    ‖matrixEntries (operatorMatrix b (inverseSqrt (operatorOfMatrix b A)) -
      operatorMatrix b (inverseSqrt (operatorOfMatrix b C)))‖ ^ 2 = 3 := by
  rw [canonical_B, canonical_T, operatorMatrix_operatorOfMatrix, operatorMatrix_operatorOfMatrix,
    matrixEntries_norm_sq]
  norm_num [B, T, Fin.sum_univ_two]

/-- The empty-coordinate canonical coefficient is locally Lipschitz and equals zero. -/
theorem actual_rank0_canonical :
    LocallyLipschitz (fun _ : ℝ => inverseSqrt (1 : EuclideanSpace ℝ (Fin 0) →L[ℝ]
      EuclideanSpace ℝ (Fin 0))) ∧
    inverseSqrt (1 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) = 0 := by
  constructor
  · apply locallyLipschitz_inverseSqrt_of_contDiff_ringInverse (fun _ : ℝ => 1)
    · intro p
      simp only [Ring.inverse_one]
      exact ContinuousLinearMap.isPositive_one
    · intro p
      exact isUnit_one
    · exact contDiff_const
  · exact Subsingleton.elim _ _

end ActualPrincipalRegularityClients

#print axioms FunctionalInequalities.Analysis.sylvester_coercivity
#print axioms FunctionalInequalities.Analysis.root_difference_le_div
#print axioms FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef
#print axioms FunctionalInequalities.Analysis.quadraticFloor_of_close
#print axioms FunctionalInequalities.Analysis.locallyLipschitz_matrixEntries_sqrt
#print axioms FunctionalInequalities.Analysis.locallyLipschitz_inverseSqrt_of_contDiff_ringInverse
#print axioms ActualPrincipalRegularityClients.roots_noncommute
#print axioms ActualPrincipalRegularityClients.actual_canonical_noncommute
#print axioms ActualPrincipalRegularityClients.actual_canonical_bound
#print axioms ActualPrincipalRegularityClients.actual_canonical_difference_nonzero
#print axioms ActualPrincipalRegularityClients.actual_rank0_canonical

namespace IndependentRootSandwich
/-! `σ A σ = 1` (`Analysis/PrincipalInverseSqrt.lean`): consumers in dimensions `2` and `0` with
`A = 1`. -/
theorem actual_identity :
    inverseSqrt (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) *
    1 * inverseSqrt 1 = 1 :=
  inverseSqrt_mul_mul_inverseSqrt 1 ContinuousLinearMap.isPositive_one isUnit_one

theorem empty :
    inverseSqrt (1 : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0)) *
    1 * inverseSqrt 1 = 1 :=
  inverseSqrt_mul_mul_inverseSqrt 1 ContinuousLinearMap.isPositive_one isUnit_one
end IndependentRootSandwich

#print axioms FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt
#print axioms IndependentRootSandwich.actual_identity
#print axioms IndependentRootSandwich.empty
