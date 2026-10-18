import FunctionalInequalities.Analysis.Convex.HessianIncrement
import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Mollification
import FunctionalInequalities.Analysis.WeakDerivative.Approximation

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/-- **The Hessian of the `C^{1,1}` Monge–Ampère solution is in `H¹_loc`** (weak Letwin route; KLS500
`weak_moment_exists_third_tensor`): every entry of `∇²u` has a weak derivative along every coordinate direction, locally in
`L²`. -/
theorem exists_weak_third_derivative {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ, ∀ k i j,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  have hex : ∀ k i j : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) g
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp g 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro k i j
    refine exists_hasWeakDerivAlong_of_forall_cutoff
      (fun S hS => memLp_hessianMatrix_entry_of_isCompact hG i j hS)
      (EuclideanSpace.basisFun (Fin n) ℝ k) ?_
    intro χ hχ hχc
    obtain ⟨C, _hC, hdiff⟩ :=
      exists_hessian_cutoff_sq_difference_bound
        hu hconv hG hV hVc hF hK hdata hw hχ hχc i j
        (EuclideanSpace.basisFun (Fin n) ℝ k)
    exact exists_hasWeakDerivAlong_of_sq_difference_le
      (memLp_cutoff_mul_hessianMatrix_entry hG i j hχ.continuous hχc)
      (EuclideanSpace.basisFun (Fin n) ℝ k) (C := C) hdiff
  refine ⟨fun x k i j => Classical.choose (hex k i j) x, ?_⟩
  intro k i j
  exact Classical.choose_spec (hex k i j)

end FunctionalInequalities.Analysis
