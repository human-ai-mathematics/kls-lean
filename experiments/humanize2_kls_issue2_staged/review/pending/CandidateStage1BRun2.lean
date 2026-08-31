import AcceptedStage1A

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem dirichletEnergy_nonneg [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    0 ≤ dirichletEnergy μ f := by
  exact integral_nonneg fun x ↦ sq_nonneg ‖gradient f x‖

theorem norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  rw [gradient]
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map (fderiv ℝ f x) |>.symm

theorem dirichletEnergy_eq_fderiv [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    dirichletEnergy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  simp_rw [dirichletEnergy, norm_fderiv_eq_norm_gradient]

namespace HasPoincare

theorem isProbabilityMeasure [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) :
    IsProbabilityMeasure μ :=
  h.1

theorem constant_nonneg [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) :
    0 ≤ C :=
  h.2.1

theorem variance_le [MeasurableSpace E] {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) {f : E → ℝ} (hf : IsAdmissible μ f) :
    variance f μ ≤ C * dirichletEnergy μ f :=
  h.2.2 f hf

theorem mono [MeasurableSpace E] {μ : Measure E} {C C' : ℝ}
    (h : HasPoincare μ C) (hCC' : C ≤ C') :
    HasPoincare μ C' := by
  refine ⟨h.1, h.2.1.trans hCC', ?_⟩
  intro f hf
  exact (h.2.2 f hf).trans
    (mul_le_mul_of_nonneg_right hCC' (dirichletEnergy_nonneg μ f))

end HasPoincare

variable [MeasurableSpace E]

def optimalPoincareConstant (μ : Measure E) : ENNReal :=
  ⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, (C.1 : ENNReal)

theorem optimalPoincareConstant_le {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≤ (C : ENNReal) := by
  exact iInf_le (fun C : {C : NNReal // HasPoincare μ (C : ℝ)} ↦ (C.1 : ENNReal)) ⟨C, hC⟩

theorem le_optimalPoincareConstant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, HasPoincare μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ optimalPoincareConstant μ := by
  exact le_iInf fun C ↦ hL C.1 C.2

theorem optimalPoincareConstant_eq_top_of_no_finite {μ : Measure E}
    (h : ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ = ⊤ := by
  apply top_unique
  exact le_iInf fun C ↦ (h C.1 C.2).elim

theorem optimalPoincareConstant_ne_top_of_hasPoincare {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≠ ⊤ := by
  intro htop
  have hle : (⊤ : ENNReal) ≤ (C : ENNReal) := by
    simpa [htop] using optimalPoincareConstant_le hC
  simpa using hle

theorem optimalPoincareConstant_eq_top_iff {μ : Measure E} :
    optimalPoincareConstant μ = ⊤ ↔
      ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ) := by
  constructor
  · intro htop C hC
    exact optimalPoincareConstant_ne_top_of_hasPoincare hC htop
  · exact optimalPoincareConstant_eq_top_of_no_finite

end Issue2Autoformalization.Stage1A
