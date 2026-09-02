import FunctionalInequalities.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Geometry and admissible sections of a Hilbert product

The product norm is the L2 norm on `WithLp 2 (E × F)`. Integrability of sections is asserted
almost everywhere, as required by Fubini.
These are draft statements awaiting human review and a separate proof phase.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare

/-- The product law transported to the Hilbert product. -/
def prodMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) : Measure (WithLp 2 (E × F)) :=
  (μ.prod ν).map (WithLp.toLp 2)

instance prodMeasure_isProbabilityMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (prodMeasure μ ν) := sorry

section Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem contDiff_section_left {f : WithLp 2 (E × F) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (y : F) :
    ContDiff ℝ ⊤ (fun x ↦ f (WithLp.toLp 2 (x, y))) := sorry

omit [CompleteSpace E] [CompleteSpace F] in
theorem contDiff_section_right {f : WithLp 2 (E × F) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (x : E) :
    ContDiff ℝ ⊤ (fun y ↦ f (WithLp.toLp 2 (x, y))) := sorry

theorem gradient_section_left {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x =
      (gradient f (WithLp.toLp 2 (x, y))).fst := sorry

theorem gradient_section_right {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y =
      (gradient f (WithLp.toLp 2 (x, y))).snd := sorry

/-- The exact sum of squared partial gradients for the Hilbert product norm. -/
theorem norm_gradient_sq_prod {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    ‖gradient f (WithLp.toLp 2 (x, y))‖ ^ 2 =
      ‖gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x‖ ^ 2 +
      ‖gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y‖ ^ 2 := sorry

end Geometry

end FunctionalInequalities.Poincare
