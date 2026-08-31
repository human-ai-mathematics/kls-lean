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
  rw [gradient, LinearIsometryEquiv.norm_map]

theorem dirichletEnergy_eq_fderiv [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    dirichletEnergy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_fderiv_eq_norm_gradient]

variable [MeasurableSpace E]

namespace HasPoincare

theorem isProbabilityMeasure {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) : IsProbabilityMeasure μ :=
  h.1

theorem constant_nonneg {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) : 0 ≤ C :=
  h.2.1

theorem variance_le {μ : Measure E} {C : ℝ}
    (h : HasPoincare μ C) {f : E → ℝ} (hf : IsAdmissible μ f) :
    variance f μ ≤ C * dirichletEnergy μ f :=
  h.2.2 f hf

theorem mono {μ : Measure E} {C C' : ℝ}
    (h : HasPoincare μ C) (hCC' : C ≤ C') : HasPoincare μ C' := by
  refine ⟨h.isProbabilityMeasure, h.constant_nonneg.trans hCC', ?_⟩
  intro f hf
  exact (h.variance_le hf).trans
    (mul_le_mul_of_nonneg_right hCC' (dirichletEnergy_nonneg μ f))

end HasPoincare

def optimalPoincareConstant (μ : Measure E) : ENNReal :=
  ⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, (C.1 : ENNReal)

theorem optimalPoincareConstant_le {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl

theorem le_optimalPoincareConstant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, HasPoincare μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ optimalPoincareConstant μ := by
  exact le_iInf fun C ↦ hL C.1 C.2

theorem optimalPoincareConstant_eq_top_of_no_finite {μ : Measure E}
    (h : ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ = ⊤ := by
  apply top_unique
  refine le_iInf fun C ↦ ?_
  exact (h C.1 C.2).elim

theorem optimalPoincareConstant_ne_top_of_hasPoincare {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≠ ⊤ := by
  intro htop
  have hle : (⊤ : ENNReal) ≤ (C : ENNReal) := by
    rw [← htop]
    exact optimalPoincareConstant_le hC
  exact (not_le_of_gt ENNReal.coe_lt_top) hle

theorem optimalPoincareConstant_eq_top_iff {μ : Measure E} :
    optimalPoincareConstant μ = ⊤ ↔
      ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ) := by
  constructor
  · intro htop C hC
    exact optimalPoincareConstant_ne_top_of_hasPoincare hC htop
  · exact optimalPoincareConstant_eq_top_of_no_finite

end Issue2Autoformalization.Stage1A
