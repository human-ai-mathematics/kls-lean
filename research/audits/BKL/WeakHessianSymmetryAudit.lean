module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates
public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
namespace CodexN11eClient
theorem exact_frozen_statement {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ k i j, HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by
  exact ae_weak_third_derivative_symm hu hG hT

theorem reverse_slots {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ k i j, HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x j i k := by
  filter_upwards [ae_weak_third_derivative_symm hu hG hT] with x hx
  intro k i j
  calc
    T x k i j = T x i k j := (hx k i j).1
    _ = T x i j k := (hx i k j).2
    _ = T x j i k := (hx i j k).1
#print axioms FunctionalInequalities.Analysis.ae_weak_third_derivative_symm
#print axioms exact_frozen_statement
#print axioms reverse_slots
end CodexN11eClient
