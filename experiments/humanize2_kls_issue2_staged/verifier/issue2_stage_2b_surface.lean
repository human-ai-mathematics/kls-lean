import CandidateStage2B

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (v : E) :
    dirichletEnergy μ (linearTest v) = ‖v‖ ^ 2 :=
  dirichletEnergy_linearTest μ v

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E}
    (hprob : IsProbabilityMeasure μ) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    IsAdmissible μ (linearTest v) :=
  isAdmissible_linearTest hprob hμ v

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (hP : HasPoincare μ C) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    variance (linearTest v) μ ≤ C * ‖v‖ ^ 2 :=
  variance_linearTest_le hP hμ v

end Issue2Autoformalization.Stage1A
