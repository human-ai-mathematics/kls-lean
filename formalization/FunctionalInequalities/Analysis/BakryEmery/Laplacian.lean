import FunctionalInequalities.Analysis.BakryEmery.Calculus
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The weighted Laplacian

The classical diffusion expression, continuity, compact support and finite-measure Lp membership.
No integration-by-parts or closed-generator identification is assumed.
-/

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The weighted Laplacian `ℒ f = Δ f - ⟪∇U, ∇f⟫` of the potential `U`, as a pointwise
differential expression on classical functions. It is the diffusion-generator convention: the
nonnegative operator of the heat semigroup is `-ℒ`. -/
def weightedLaplacian (U f : E → ℝ) (x : E) : ℝ :=
  Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫

theorem weightedLaplacian_apply (U f : E → ℝ) (x : E) :
    weightedLaplacian U f x = Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫ := rfl

/-- The weighted Laplacian of a `C²` function for a `C¹` potential is continuous. -/
theorem continuous_weightedLaplacian {U f : E → ℝ} (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 2 f) :
    Continuous (weightedLaplacian U f) :=
  (continuous_laplacian hf).sub
    ((continuous_gradient hU).inner (continuous_gradient (hf.of_le (by norm_num))))

/-- The weighted Laplacian of a compactly supported function has compact support. -/
theorem hasCompactSupport_weightedLaplacian (U : E → ℝ) {f : E → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (weightedLaplacian U f) := by
  refine (hasCompactSupport_laplacian hfc).sub ?_
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [h0]

section Integrable

variable [MeasurableSpace E] [BorelSpace E]

/-- The weighted Laplacian of a `C²` compactly supported function lies in every `L^p` of a finite
measure; the potential need only be `C¹`. -/
theorem memLp_weightedLaplacian {μ : Measure E} [IsFiniteMeasure μ] {U f : E → ℝ}
    (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (p : ENNReal) :
    MemLp (weightedLaplacian U f) p μ :=
  (continuous_weightedLaplacian hU hf).memLp_of_hasCompactSupport
    (hasCompactSupport_weightedLaplacian U hfc)

end Integrable

end FunctionalInequalities.Analysis.BakryEmery
