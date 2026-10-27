import FunctionalInequalities.Analysis.Operator.InverseSqrt

/-! Operator perturbation clients below the BKL compact reduction. -/
set_option autoImplicit false
open FunctionalInequalities Filter Topology
open scoped RealInnerProductSpace
namespace SourceLayout

theorem positive_square_root_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S Q : E →L[ℝ] E} (hS : S.IsPositive) (hQ : S * S = Q) : ‖S - 1‖ ≤ ‖Q - 1‖ :=
  Analysis.norm_sub_one_le_of_isPositive_mul_self hS hQ

theorem inverse_sqrt_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] {S : ℕ → E →L[ℝ] E}
    (hS : Tendsto S atTop (𝓝 1))
    (hp : ∀ᶠ j in atTop, (S j).IsPositive) (hu : ∀ᶠ j in atTop, IsUnit (S j)) :
    Tendsto (fun j => Analysis.inverseSqrt (S j)) atTop (𝓝 1) :=
  Analysis.tendsto_inverseSqrt_one hS hp hu

#print axioms SourceLayout.positive_square_root_bound
#print axioms SourceLayout.inverse_sqrt_limit
end SourceLayout
