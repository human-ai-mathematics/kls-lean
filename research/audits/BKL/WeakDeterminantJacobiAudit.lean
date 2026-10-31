module

public import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
public import FunctionalInequalities.Analysis.Matrix.WeakDerivative
public import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative

@[expose] public section

noncomputable section
open MeasureTheory Set Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
open FunctionalInequalities FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
namespace WeakDeterminantJacobiAudit

/-- Actual normalized source-law determinant polynomial and its first weak
derivative; no smoothness of the raw Hessian or given derivative tensor. -/
theorem produced_normalized_weak_determinant_jacobi {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :

    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n, T x k (σ i) i *
              ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n, T x k (σ i) i *
              ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n, T x k (σ i) i *
              ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
            (hessianMatrix u x).det *
              ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace := by
  classical
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, hG,
      _hF, _hw, hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, ?_⟩
  intro k
  have hbound (r s : Fin n) : MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  have hp := hasWeakDerivAlong_det_of_locally_memLp_two
    (A := fun x => hessianMatrix u x)
    (DA := fun x => Matrix.of fun i j => T x k i j)
    (fun i j => (hT k i j).1) hbound (fun i j => (hT k i j).2)
  refine ⟨hp.1, hp.2, ?_⟩
  filter_upwards [hdata] with x hx
  have hunit : IsUnit (hessianMatrix u x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hx.1.det_pos)
  calc
    (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : Fin n, T x k (σ i) i *
          ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
        fderiv ℝ Matrix.det (hessianMatrix u x) (Matrix.of fun i j => T x k i j) :=
      (fderiv_det_eq_sum_permutation (hessianMatrix u x) (Matrix.of fun i j => T x k i j)).symm
    _ = (hessianMatrix u x).det *
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace :=
      fderiv_det_eq_det_mul_trace _ _ hunit

/-- A singular singleton matrix still has a nonzero determinant differential
in a nonzero direction; invertibility cannot be used for the generic identity. -/
theorem singular_singleton_direction (N : Matrix (Fin 1) (Fin 1) ℝ) :
    fderiv ℝ Matrix.det (0 : Matrix (Fin 1) (Fin 1) ℝ) N = N 0 0 := by
  simpa using fderiv_det_eq_sum_permutation (0 : Matrix (Fin 1) (Fin 1) ℝ) N

/-- The empty matrix case is retained. -/
theorem empty_matrix_direction :
    fderiv ℝ Matrix.det (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 = 0 := by
  exact (fderiv_det_eq_sum_permutation (0 : Matrix (Fin 0) (Fin 0) ℝ) 0).trans (by simp)

end WeakDeterminantJacobiAudit
