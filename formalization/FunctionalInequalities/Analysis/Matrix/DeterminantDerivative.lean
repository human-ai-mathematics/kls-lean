import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Matrix.PosDef

/-!
# Derivative of the determinant and of the log-determinant (Jacobi's formula)

The determinant of a real square matrix is a continuous multilinear map of its rows; its derivative
in a direction `N` is the sum of row replacements and, for invertible `M`, equals `det M · tr(M⁻¹ N)`.
Hence `D(log det)(M)[N] = tr(M⁻¹ N)`, also along a differentiable matrix-valued map.
-/

noncomputable section
open scoped Matrix.Norms.Elementwise

namespace FunctionalInequalities.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def detML : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by
      change Continuous (fun M : ι → ι → ℝ => (Matrix.of M).det)
      simp only [Matrix.det_apply, Matrix.of_apply]
      fun_prop }

/-- The determinant is differentiable (it is a continuous multilinear map of the rows). -/
theorem differentiableAt_det (M : Matrix ι ι ℝ) : DifferentiableAt ℝ Matrix.det M :=
  (detML.hasFDerivAt (fun i => M i)).differentiableAt

/-- The derivative of the determinant is the sum of row replacements. -/
theorem fderiv_det_eq_sum_updateRow (M N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M N = ∑ i, (M.updateRow i (N i)).det := by
  change fderiv ℝ (detML : (ι → ι → ℝ) → ℝ) (fun i => M i) (fun i => N i) = _
  rw [(detML.hasFDerivAt (fun i => M i)).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- **Jacobi's formula**: `D(det)(M)[N] = det M · tr(M⁻¹ N)` for invertible `M` and any direction `N`. -/
theorem fderiv_det_eq_det_mul_trace (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N) := by
  have hNM : (N * M⁻¹) * M = N := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
  have hrow (i : ι) : N i = ∑ j, (N * M⁻¹) i j • M j := by
    calc
      N i = ((N * M⁻¹) * M) i := congrArg (fun Q : Matrix ι ι ℝ => Q i) hNM.symm
      _ = _ := by
        ext k
        simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_det_eq_sum_updateRow]
  calc
    (∑ i, (M.updateRow i (N i)).det) = ∑ i, (N * M⁻¹) i i * M.det := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hrow, Matrix.det_updateRow_sum]
      rfl
    _ = Matrix.trace (N * M⁻¹) * M.det := by
      rw [Matrix.trace, Finset.sum_mul]
      rfl
    _ = M.det * Matrix.trace (M⁻¹ * N) := by
      rw [Matrix.trace_mul_comm]
      ring

/-- `D(log det)(M)[N] = tr(M⁻¹ N)` for `det M ≠ 0`. -/
theorem fderiv_logDet_apply (M N : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M N = Matrix.trace (M⁻¹ * N) := by
  have hd := (differentiableAt_det M).hasFDerivAt.log hM
  calc
    fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M N =
        M.det⁻¹ * fderiv ℝ Matrix.det M N := by
      have h := congrArg (fun L : Matrix ι ι ℝ →L[ℝ] ℝ => L N) hd.fderiv
      exact h.trans rfl
    _ = Matrix.trace (M⁻¹ * N) := by
      rw [fderiv_det_eq_det_mul_trace M N (isUnit_iff_ne_zero.mpr hM)]
      rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

theorem differentiableAt_logDet (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    DifferentiableAt ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M :=
  ((differentiableAt_det M).hasFDerivAt.log hM).differentiableAt

/-- Chain rule: `D(log det ∘ M)(x)[v] = tr(M(x)⁻¹ DM(x)[v])`. -/
theorem fderiv_logDet_comp_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : G → Matrix ι ι ℝ} {x : G} (hM : DifferentiableAt ℝ M x) (hdet : (M x).det ≠ 0) (v : G) :
    fderiv ℝ (fun y => Real.log (M y).det) x v = Matrix.trace ((M x)⁻¹ * fderiv ℝ M x v) := by
  have hc : fderiv ℝ (fun y => Real.log (M y).det) x =
      fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) (M x) ∘L fderiv ℝ M x :=
    fderiv_comp x (differentiableAt_logDet (M x) hdet) hM
  rw [hc, ContinuousLinearMap.comp_apply, fderiv_logDet_apply (M x) _ hdet]

end FunctionalInequalities.Analysis


section DeterminantPolynomialIdentification

open scoped BigOperators Matrix.Norms.Elementwise

namespace FunctionalInequalities.Analysis

section FiniteIndex

variable {ι : Type*}
variable [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]

/-- Derivative of the finite determinant polynomial along a scalar affine path.
No outer matrix chain rule, invertibility, or nonempty-index assumption. -/
private theorem deriv_det_add_smul_zero
    (A N : Matrix ι ι ℝ) :
    deriv (fun t : ℝ => Matrix.det (A + t • N)) 0 =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j := by
  have hentry (σ : Equiv.Perm ι) (i : ι) :
      HasDerivAt (fun t : ℝ => A (σ i) i + t * N (σ i) i)
        (N (σ i) i) 0 := by
    simpa only [id_eq, one_mul] using
      HasDerivAt.const_add (A (σ i) i)
        ((hasDerivAt_id (0 : ℝ)).mul_const (N (σ i) i))
  have hprod (σ : Equiv.Perm ι) :
      HasDerivAt
        (fun t : ℝ => ∏ i : ι, (A (σ i) i + t * N (σ i) i))
        (∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j) 0 := by
    simpa only [zero_mul, add_zero, smul_eq_mul, mul_comm] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ)
        (fun i _ => hentry σ i))
  have hpoly :
      HasDerivAt (fun t : ℝ => Matrix.det (A + t • N))
        (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : ι, N (σ i) i *
            ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j) 0 := by
    simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact HasDerivAt.fun_sum
      (fun σ _ =>
        HasDerivAt.const_mul ((Equiv.Perm.sign σ : ℤ) : ℝ) (hprod σ))
  exact hpoly.deriv


/-- The signed permutation-polynomial determinant density is its existing
outer matrix derivative, including singular and empty matrices. -/
theorem fderiv_det_eq_sum_permutation
    (A N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det A N =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, N (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A (σ j) j := by
  have hd : DifferentiableAt ℝ Matrix.det (A + (0 : ℝ) • N) := by
    simpa only [zero_smul, add_zero] using differentiableAt_det A
  calc
    fderiv ℝ Matrix.det A N =
        deriv (fun t : ℝ => Matrix.det (A + t • N)) 0 := by
      simpa only [zero_smul, add_zero] using! hd.deriv_comp_add_smul.symm
    _ = _ := deriv_det_add_smul_zero A N

end FiniteIndex


end FunctionalInequalities.Analysis

end DeterminantPolynomialIdentification

/-! ## Smoothness of the log-determinant -/

noncomputable section LogDetSmoothness

namespace FunctionalInequalities.Analysis

section LogDetContDiff

open scoped Matrix.Norms.Elementwise ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant is a polynomial in the entries, hence `C^k` for every `k`. -/
private theorem contDiff_det {k : ℕ∞ω} :
    ContDiff ℝ k (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change ContDiff ℝ k (fun M : Matrix ι ι ℝ => M.det)
  simp only [Matrix.det_apply]
  fun_prop

/-- `M ↦ log det M` is `C^k` (every `k`, including `ω`) at each matrix with nonzero determinant. This is smoothness of the
matrix function only; nothing is claimed about a matrix field. -/
theorem contDiffAt_log_det {k : ℕ∞ω} {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    ContDiffAt ℝ k (fun M : Matrix ι ι ℝ => Real.log M.det) A :=
  contDiff_det.contDiffAt.log hA

/-- `M ↦ log det M` is `C^k` at each positive definite matrix. -/
theorem contDiffAt_log_det_of_posDef {k : ℕ∞ω} {A : Matrix ι ι ℝ}
    (hA : A.PosDef) :
    ContDiffAt ℝ k (fun M : Matrix ι ι ℝ => Real.log M.det) A :=
  contDiffAt_log_det hA.det_pos.ne'

end LogDetContDiff

end FunctionalInequalities.Analysis

end LogDetSmoothness
