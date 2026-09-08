import FunctionalInequalities.Probability.Covariance
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Square roots of positive semidefinite operators and of the covariance

Source: Blueprint `thm:affine-covariance-relaxation-closed`, the passage from the covariance
`Σ` to the operator `Σ^{1/2} ∇` of `lem:covariance-core-closure`. Read
`exists_norm_sq_eq_inner_of_isSymmetric` and `Covariance.exists_sqrt`.

On a finite-dimensional real inner product space every symmetric operator `T` with
`⟪T v, v⟫ ≥ 0` has a continuous linear `B` with `⟪T v, v⟫ = ‖B v‖²` for all `v`: take the
orthonormal eigenbasis of `T` and scale each eigenvector by the square root of its (nonnegative)
eigenvalue. The covariance operator of any Borel measure is such a `T`, so the weighted gradient
`B ∘ ∇` of `lem:covariance-core-closure` realizes the covariance energy `∫ ⟪Σ ∇g, ∇g⟫ dν`.

Only the existence of `B` is claimed; `B` is not asserted to be symmetric, unique or positive, and
no functional-calculus square root is introduced. The zero-dimensional space is included with
`B = 0`.
-/

noncomputable section

open InnerProductSpace

namespace FunctionalInequalities

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A symmetric operator with nonnegative quadratic form has a continuous linear square root in
the sense `⟪T v, v⟫ = ‖B v‖²`. -/
theorem exists_norm_sq_eq_inner_of_isSymmetric (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, 0 ≤ inner ℝ (T v) v) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (T v) v = ‖B v‖ ^ 2 := by
  set e := hT.eigenvectorBasis rfl with he
  set lam := hT.eigenvalues rfl with hlam
  have hTe : ∀ i, T (e i) = lam i • e i := fun i ↦ hT.apply_eigenvectorBasis rfl i
  have hlam_nonneg : ∀ i, 0 ≤ lam i := by
    intro i
    have h2 := hpos (e i)
    rw [hTe i, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.1 i] at h2
    simpa using h2
  -- `B v = ∑ i, √(lam i) * ⟪e i, v⟫ • e i`
  let B : V →L[ℝ] V := ∑ i, Real.sqrt (lam i) • (innerSL ℝ (e i)).smulRight (e i)
  refine ⟨B, fun v ↦ ?_⟩
  have hB : B v = ∑ i, (Real.sqrt (lam i) * inner ℝ (e i) v) • e i := by
    simp only [B, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul]
    rfl
  -- `T v = ∑ i, lam i * ⟪e i, v⟫ • e i`
  have hTv : T v = ∑ i, (lam i * inner ℝ (e i) v) • e i := by
    conv_lhs => rw [← e.sum_repr' v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hTe i, smul_smul, mul_comm]
  have hinner : inner ℝ (T v) v = ∑ i, lam i * inner ℝ (e i) v ^ 2 := by
    rw [hTv, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, sq, mul_assoc]
  have hnorm : ‖B v‖ ^ 2 = ∑ i, (Real.sqrt (lam i) * inner ℝ (e i) v) ^ 2 := by
    rw [hB, ← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, e.orthonormal.inner_right_fintype, sq]
  rw [hinner, hnorm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, Real.sq_sqrt (hlam_nonneg i)]

namespace Covariance

variable [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

/-- The covariance operator of any Borel measure has a square root `B` with
`⟪Σ v, v⟫ = ‖B v‖²`, including the zero operator of laws without second moment and the
zero-dimensional space. -/
theorem exists_sqrt (μ : MeasureTheory.Measure V) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (operator μ v) v = ‖B v‖ ^ 2 := by
  refine exists_norm_sq_eq_inner_of_isSymmetric (operator μ) ?_ ?_
  · intro x y
    calc inner ℝ (operator μ x) y = ProbabilityTheory.covarianceBilin μ x y := operator_inner μ x y
      _ = ProbabilityTheory.covarianceBilin μ y x := ProbabilityTheory.covarianceBilin_comm x y
      _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
      _ = inner ℝ x (operator μ y) := real_inner_comm _ _
  · intro v
    rw [operator_inner]
    exact ProbabilityTheory.covarianceBilin_self_nonneg v

end Covariance

end FunctionalInequalities
