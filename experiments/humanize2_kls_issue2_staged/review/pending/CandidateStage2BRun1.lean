import AcceptedStage2A

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

theorem dirichletEnergy_linearTest (μ : Measure E) [IsProbabilityMeasure μ] (v : E) :
    dirichletEnergy μ (linearTest v) = ‖v‖ ^ 2 := by
  simp [dirichletEnergy]

theorem isAdmissible_linearTest {μ : Measure E} (hprob : IsProbabilityMeasure μ)
    (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    IsAdmissible μ (linearTest v) := by
  let _ := hprob
  refine ⟨?_, ?_, ?_⟩
  · exact (InnerProductSpace.toDual ℝ E v).contDiff
  · change MemLp (fun x : E ↦ inner ℝ v x) 2 μ
    exact hμ.const_inner v
  · simp

theorem variance_linearTest_le {μ : Measure E} {C : ℝ}
    (hP : HasPoincare μ C) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    variance (linearTest v) μ ≤ C * ‖v‖ ^ 2 := by
  let _ := hP.isProbabilityMeasure
  rw [← dirichletEnergy_linearTest μ v]
  exact hP.variance_le (isAdmissible_linearTest hP.isProbabilityMeasure hμ v)

end Issue2Autoformalization.Stage1A
