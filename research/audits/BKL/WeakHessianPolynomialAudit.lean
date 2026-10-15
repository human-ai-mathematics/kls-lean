import FunctionalInequalities.Analysis.Matrix.WeakDerivative
import FunctionalInequalities.KLS.CEK.MomentRegularity

/-!
# Genuine weak Hessian polynomial clients

Actual normalized regular source-law determinants, adjugate entries and trace
quadratics consume the produced Hessian/tensor and the generic weak matrix API.
Empty products, zero matrix size and singleton cofactors retain their scopes.
These clients do not establish a generator identity, trace estimate or constant 8.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped ContDiff Topology
open FunctionalInequalities FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein

namespace WeakHessianPolynomialAudit

namespace Scalar
/-- Empty products genuinely yield constant one and zero weak derivative,
even in dimension zero. -/
theorem empty_product_dimension_zero :
    HasWeakDerivAlong (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ))
      (fun _ => 0) 0 ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin 0)), IsCompact S →
      MemLp (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin 0))).restrict S) := by
  simpa only [Finset.prod_empty, Finset.sum_empty] using
    (hasWeakDerivAlong_finsetProd_of_locally_memLp_two
      (f := fun (_ : ℕ) (_ : EuclideanSpace ℝ (Fin 0)) => (0 : ℝ))
      (df := fun _ _ => (0 : ℝ)) (v := 0) (∅ : Finset ℕ)
      (by simp) (by simp) (by simp))


end Scalar

namespace Determinant

/-- Actual normalized source-law adjugate entries acquire weak derivatives
locally in L2 from the produced tensor, without smoothness of H. -/
theorem produced_normalized_weak_cofactors {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ)

    : ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k i j : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).adjugate i j) g
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, hG,
      _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, hnorm, hmap, ?_⟩
  intro k i j
  have hbound (r s : Fin n) : MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  let A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (hessianMatrix u x).updateRow j (Pi.single i 1)
  let DA : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
    fun x => (Matrix.of fun r s => T x k r s).updateRow j (fun _ => 0)
  have hA (r s : Fin n) : HasWeakDerivAlong (fun x => A x r s)
      (fun x => DA x r s) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    by_cases hr : r = j
    · subst r
      simpa [A, DA, Matrix.updateRow_apply] using
        (hasWeakDerivAlong_of_contDiff
          (f := fun _ : EuclideanSpace ℝ (Fin n) => (Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          contDiff_const (EuclideanSpace.basisFun (Fin n) ℝ k))
    · simpa [A, DA, Matrix.updateRow_apply, hr] using (hT k r s).1
  have hAb (r s : Fin n) : MemLp (fun x => A x r s) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    by_cases hr : r = j
    · subst r
      simpa [A, Matrix.updateRow_apply] using
        (memLp_top_const ((Pi.single i (1 : ℝ) : Fin n → ℝ) s)
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    · simpa [A, Matrix.updateRow_apply, hr] using hbound r s
  have hDA2 (r s : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
      MemLp (fun x => DA x r s) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    by_cases hr : r = j
    · subst r
      simp [DA, Matrix.updateRow_apply]
    · simpa [DA, Matrix.updateRow_apply, hr] using (hT k r s).2 S hS
  have hp := hasWeakDerivAlong_det_of_locally_memLp_two hA hAb hDA2
  refine ⟨_, ?_, hp.2⟩
  simpa only [Matrix.adjugate_apply] using hp.1

/-- In the singleton matrix case the cofactor is exactly one, with zero
weak derivative; no regularity of u is needed. -/
theorem singleton_hessian_cofactor
    (u : EuclideanSpace ℝ (Fin 1) → ℝ)
    (v : EuclideanSpace ℝ (Fin 1)) :
    HasWeakDerivAlong (fun x => (hessianMatrix u x).adjugate 0 0)
      (fun _ => 0) v := by
  simpa [Matrix.adjugate_fin_one] using
    (hasWeakDerivAlong_of_contDiff
      (f := fun _ : EuclideanSpace ℝ (Fin 1) => (1 : ℝ)) contDiff_const v)

/-- Actual normalized source-law determinant polynomial and its first weak
derivative; no smoothness of the raw Hessian or given derivative tensor. -/
theorem produced_normalized_weak_determinant {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ)

    : ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
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
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n, T x k (σ i) i *
              ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  classical
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, hG,
      _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, ?_⟩
  intro k
  have hbound (r s : Fin n) : MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  exact hasWeakDerivAlong_det_of_locally_memLp_two
    (A := fun x => hessianMatrix u x)
    (DA := fun x => Matrix.of fun i j => T x k i j)
    (fun i j => (hT k i j).1) hbound (fun i j => (hT k i j).2)


end Determinant

namespace Trace

/-- Actual normalized source-law trace polynomial and first weak directional
derivative, without symmetry/PSD of B or smoothness of the raw Hessian. -/
theorem produced_normalized_weak_trace_quadratic {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ)

    (B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong
          (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => 2 * (B * hessianMatrix u x * B * (Matrix.of fun i j => T x k i j)).trace) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, hG,
      _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, ?_⟩
  intro k
  have hbound (r s : Fin n) : MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  exact hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two B
    (A := fun x => hessianMatrix u x)
    (DA := fun x => Matrix.of fun i j => T x k i j)
    (fun i j => (hT k i j).1) hbound (fun i j => (hT k i j).2)

/-- Zero matrix size is retained independently of the ambient dimension. -/
theorem zero_matrix_size {d : ℕ} (v : EuclideanSpace ℝ (Fin d))
    (A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin 0) (Fin 0) ℝ)
    (B : Matrix (Fin 0) (Fin 0) ℝ) :
    HasWeakDerivAlong (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))
      (fun _ => 0) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  have h := hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two B
    (A := A) (DA := DA) (v := v)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa [Matrix.trace] using h


end Trace

end WeakHessianPolynomialAudit

#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul
#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two
#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two
#print axioms FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two
#print axioms WeakHessianPolynomialAudit.Scalar.empty_product_dimension_zero
#print axioms WeakHessianPolynomialAudit.Determinant.produced_normalized_weak_cofactors
#print axioms WeakHessianPolynomialAudit.Determinant.singleton_hessian_cofactor
#print axioms WeakHessianPolynomialAudit.Determinant.produced_normalized_weak_determinant
#print axioms WeakHessianPolynomialAudit.Trace.produced_normalized_weak_trace_quadratic
#print axioms WeakHessianPolynomialAudit.Trace.zero_matrix_size
