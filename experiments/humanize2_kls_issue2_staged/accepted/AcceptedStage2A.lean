import AcceptedStage1B

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linearTest (v : E) : E → ℝ := fun x ↦ inner ℝ v x

@[simp]
theorem linearTest_apply (v x : E) : linearTest v x = inner ℝ v x := by
  rfl

theorem linearTest_eq_inner (v : E) : linearTest v = fun x ↦ inner ℝ v x := by
  rfl

variable [CompleteSpace E]

theorem hasGradientAt_linearTest (v x : E) : HasGradientAt (linearTest v) v x := by
  change HasFDerivAt (fun y : E ↦ inner ℝ v y) (InnerProductSpace.toDual ℝ E v) x
  exact (InnerProductSpace.toDual ℝ E v).hasFDerivAt

@[simp]
theorem gradient_linearTest (v x : E) : gradient (linearTest v) x = v := by
  exact (hasGradientAt_linearTest v x).gradient

end Issue2Autoformalization.Stage1A
