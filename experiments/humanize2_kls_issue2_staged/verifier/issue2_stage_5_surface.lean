import CandidateStage5

noncomputable section

open MeasureTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

example (μ : Measure E) [FiniteDimensional ℝ E] [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ :=
  linearTestLower μ hμ

example (μ : Measure E) [FiniteDimensional ℝ E] [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) :
    (∀ ⦃f : E → ℝ⦄, IsAdmissible μ f →
      poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ) ∧
      lambdaMaxCovariance μ ≤ optimalPoincareConstant μ :=
  linearTestLowerCertificate μ hμ

example {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ :=
  euclideanLinearTestLower μ hμ

end Issue2Autoformalization.Stage1A
