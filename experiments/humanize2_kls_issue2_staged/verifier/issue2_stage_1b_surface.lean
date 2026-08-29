import CandidateStage1B

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    0 ≤ dirichletEnergy μ f :=
  dirichletEnergy_nonneg μ f

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ :=
  norm_fderiv_eq_norm_gradient f x

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    dirichletEnergy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
  dirichletEnergy_eq_fderiv μ f

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) : IsProbabilityMeasure μ :=
  h.isProbabilityMeasure

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) : 0 ≤ C :=
  h.constant_nonneg

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) {f : E → ℝ} (hf : IsAdmissible μ f) :
    variance f μ ≤ C * dirichletEnergy μ f :=
  h.variance_le hf

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C C' : ℝ}
    (h : HasPoincare μ C) (hCC' : C ≤ C') : HasPoincare μ C' :=
  h.mono hCC'

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] (μ : Measure E) :
    optimalPoincareConstant μ =
      ⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, (C.1 : ENNReal) :=
  rfl

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≤ (C : ENNReal) :=
  optimalPoincareConstant_le hC

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, HasPoincare μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ optimalPoincareConstant μ :=
  le_optimalPoincareConstant hL

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E}
    (h : ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ = ⊤ :=
  optimalPoincareConstant_eq_top_of_no_finite h

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≠ ⊤ :=
  optimalPoincareConstant_ne_top_of_hasPoincare hC

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} :
    optimalPoincareConstant μ = ⊤ ↔
      ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ) :=
  optimalPoincareConstant_eq_top_iff

end Issue2Autoformalization.Stage1A
