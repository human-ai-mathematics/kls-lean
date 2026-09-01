import CandidateStage4A

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

example (μ : Measure E) : E →L[ℝ] E :=
  centeredCovarianceOperator μ

example (μ : Measure E) (x y : E) :
    inner ℝ (centeredCovarianceOperator μ x) y = covarianceBilin μ x y :=
  centeredCovarianceOperator_inner μ x y

example (μ : Measure E) (x y : E) :
    inner ℝ (centeredCovarianceOperator μ x) y = covarianceBilin μ x y := by
  simp

example (μ : Measure E) :
    (centeredCovarianceOperator μ).toLinearMap.IsSymmetric :=
  centeredCovarianceOperator_isSymmetric μ

example (μ : Measure E) (x : E) :
    0 ≤ inner ℝ (centeredCovarianceOperator μ x) x :=
  centeredCovarianceOperator_self_nonneg μ x

example {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (x : E) :
    inner ℝ (centeredCovarianceOperator μ x) x = variance (linearTest x) μ :=
  centeredCovarianceOperator_self_eq_variance hμ x

example (μ : Measure E) : ℝ :=
  covarianceRayleighMax μ

example (μ : Measure E) :
    covarianceRayleighMax μ =
      ⨆ v : Metric.sphere (0 : E) 1, covarianceBilin μ v v :=
  covarianceRayleighMax_eq_iSup_covariance_sphere μ

example (μ : Measure E) : 0 ≤ covarianceRayleighMax μ :=
  covarianceRayleighMax_nonneg μ

end Issue2Autoformalization.Stage1A
