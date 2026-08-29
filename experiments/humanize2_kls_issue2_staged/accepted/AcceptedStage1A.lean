import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.Variance

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

structure IsAdmissible (μ : Measure E) (f : E → ℝ) : Prop where
  smooth' : ContDiff ℝ ⊤ f
  memLp_two : MemLp f 2 μ
  energy_integrable : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ

def dirichletEnergy (μ : Measure E) (f : E → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

def HasPoincare (μ : Measure E) (C : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    0 ≤ C ∧
      ∀ f : E → ℝ, IsAdmissible μ f → variance f μ ≤ C * dirichletEnergy μ f

end Issue2Autoformalization.Stage1A
