import FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion

/-! The shared field estimate is available before the final Taylor criterion. -/
set_option autoImplicit false
open FunctionalInequalities MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.PoissonIterate
namespace SourceLayout

theorem taylor_field {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] {ν : ProbabilityMeasure V} {R : ℝ} {d : ℕ}
    (h : ∀ g : Lp ℝ 2 (ν : Measure V),
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑g) d)‖ ≤ R ^ d * ‖g‖)
    {k : ℕ} (u : Field ν k) :
    ‖taylorField d u‖ ^ 2 ≤ R ^ (2 * d) * normSq u :=
  norm_taylorField_sq_le h u

#print axioms SourceLayout.taylor_field
end SourceLayout
