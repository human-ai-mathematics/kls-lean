import FunctionalInequalities.Analysis.Convex.Quadratic

/-! A classical all-order client of the quadratic module, without the viscosity or Dirichlet
chain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open FunctionalInequalities.Analysis
open scoped ContDiff

namespace SourceLayout

/-- A single polynomial interface handles higher regularity, including the empty finite index. -/
theorem quadratic_four {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    ContDiff ℝ 4 (quadraticAt A x₀ b c) :=
  contDiff_quadraticAt_all A x₀ b c

#print axioms SourceLayout.quadratic_four

end SourceLayout
