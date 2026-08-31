import CandidateStage2A

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) :
    linearTest v = fun x ↦ inner ℝ v x :=
  linearTest_eq_inner v

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v x : E) :
    linearTest v x = inner ℝ v x :=
  linearTest_apply v x

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v x : E) :
    linearTest v x = inner ℝ v x := by
  simp

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v x : E) : HasGradientAt (linearTest v) v x :=
  hasGradientAt_linearTest v x

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v x : E) : gradient (linearTest v) x = v :=
  gradient_linearTest v x

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v x : E) : gradient (linearTest v) x = v := by
  simp

end Issue2Autoformalization.Stage1A
