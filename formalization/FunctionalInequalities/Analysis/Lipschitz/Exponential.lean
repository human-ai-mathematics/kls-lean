import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace FunctionalInequalities.Analysis

/-- The scalar exponential is Lipschitz on the half-line (-∞, C]; no lower
bound is required, and the threshold may be negative. -/
theorem lipschitzOnWith_exp_Iic (C : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp C)) Real.exp (Set.Iic C) := by
  refine (convex_Iic C).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) ?_
  intro x hx
  apply NNReal.coe_le_coe.mp
  change ‖Real.exp x‖ ≤ (Real.toNNReal (Real.exp C) : ℝ)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
    Real.coe_toNNReal _ (Real.exp_pos C).le]
  exact Real.exp_le_exp.mpr hx

end FunctionalInequalities.Analysis
