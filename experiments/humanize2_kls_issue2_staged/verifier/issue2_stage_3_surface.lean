import CandidateStage3

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) : ENNReal :=
  poincareRayleighQuotient μ f

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {μ : Measure E} {f : E → ℝ} (hf : IsAdmissible μ f) :
    poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ :=
  poincareRayleighQuotient_le_optimal hf

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {μ : Measure E} {f : E → ℝ}
    (henergy : 0 < dirichletEnergy μ f) :
    poincareRayleighQuotient μ f =
      ENNReal.ofReal (variance f μ / dirichletEnergy μ f) :=
  poincareRayleighQuotient_eq_of_pos henergy

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {μ : Measure E} {f : E → ℝ}
    (hvariance : 0 < variance f μ) (henergy : dirichletEnergy μ f = 0) :
    poincareRayleighQuotient μ f = ⊤ :=
  poincareRayleighQuotient_eq_top_of_energy_eq_zero hvariance henergy

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {μ : Measure E} {f : E → ℝ}
    (hf : IsAdmissible μ f) (henergy : 0 < dirichletEnergy μ f) :
    ENNReal.ofReal (variance f μ / dirichletEnergy μ f) ≤
      optimalPoincareConstant μ :=
  admissibleRayleighQuotient_le_optimal hf henergy

end Issue2Autoformalization.Stage1A
