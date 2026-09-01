import CandidateStage4B

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

example [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) :
    Module.End.HasEigenvalue (centeredCovarianceOperator μ).toLinearMap
      (covarianceRayleighMax μ) :=
  centeredCovarianceOperator_hasEigenvalue_iSup μ

example (μ : Measure E) : ENNReal :=
  lambdaMaxCovariance μ

example (μ : Measure E) :
    (lambdaMaxCovariance μ).toReal = covarianceRayleighMax μ :=
  lambdaMaxCovariance_toReal μ

example [Subsingleton E] (μ : Measure E) :
    lambdaMaxCovariance μ = 0 :=
  lambdaMaxCovariance_eq_zero_of_subsingleton μ

example (μ : Measure E) :
    lambdaMaxCovariance μ ≤ ENNReal.ofReal ‖centeredCovarianceOperator μ‖ :=
  lambdaMaxCovariance_le_operatorNorm μ

example (μ : Measure E) : lambdaMaxCovariance μ ≠ ⊤ :=
  lambdaMaxCovariance_ne_top μ

example {μ : Measure E} {C : ℝ}
    (hP : HasPoincare μ C) (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ ENNReal.ofReal C :=
  lambdaMaxCovariance_le hP hμ

example {μ : Measure E} (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ :=
  lambdaMaxCovariance_le_optimal hμ

end Issue2Autoformalization.Stage1A
