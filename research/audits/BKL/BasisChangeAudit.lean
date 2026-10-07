import FunctionalInequalities.Analysis.Tensor.BasisChange

/-!
# Audit: basis independence of the Hilbert–Schmidt norm of coefficient arrays

Supporting result for the coordinate tensors of Bizeul–Klartag–Lehec (arXiv:2610.05474v1,
Section 2), discharged by `Analysis/Tensor/BasisChange.lean`:

* `norm_coordTensor_eq`: for any two orthonormal bases `b`, `b'` of a real inner product space,
  `‖coordTensor b Φ‖ = ‖coordTensor b' Φ‖`;
* `std_eq_basisFun`: the consumer on `ℝⁿ`, comparing `stdOrthonormalBasis` with the standard
  coordinate basis `EuclideanSpace.basisFun`.

This is a supporting lemma; it does not state or prove any theorem of the paper.
-/

noncomputable section

open FunctionalInequalities.Analysis.Tensor

namespace BKLBasisChangeAudit

/-- The Hilbert–Schmidt norm of the coefficient array does not depend on the orthonormal
basis. -/
theorem norm_coordTensor_eq :
    ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n n' k : ℕ}
      (b : OrthonormalBasis (Fin n) ℝ E) (b' : OrthonormalBasis (Fin n') ℝ E)
      (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ),
      ‖coordTensor b Φ‖ = ‖coordTensor b' Φ‖ :=
  fun b b' Φ => FunctionalInequalities.Analysis.Tensor.norm_coordTensor_eq b b' Φ

/-- Consumer on `ℝⁿ`: `stdOrthonormalBasis` and the coordinate basis give the same norm. -/
theorem std_eq_basisFun {n k : ℕ}
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ) :
    ‖coordTensor ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))).reindex
        (finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))) Φ‖ =
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) Φ‖ :=
  FunctionalInequalities.Analysis.Tensor.norm_coordTensor_eq _ _ Φ

/-- The unreindexed `stdOrthonormalBasis` (indexed by `Fin (finrank ℝ ℝⁿ)`) also gives the same
norm as the coordinate basis. -/
theorem std_eq_basisFun' {n k : ℕ}
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ) :
    ‖coordTensor (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) Φ‖ =
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) Φ‖ :=
  FunctionalInequalities.Analysis.Tensor.norm_coordTensor_eq _ _ Φ

end BKLBasisChangeAudit

#print axioms FunctionalInequalities.Analysis.Tensor.norm_coordTensor_eq
#print axioms FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq
#print axioms BKLBasisChangeAudit.norm_coordTensor_eq
#print axioms BKLBasisChangeAudit.std_eq_basisFun
#print axioms BKLBasisChangeAudit.std_eq_basisFun'
