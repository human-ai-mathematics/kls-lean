import AcceptedStage2B

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

def poincareRayleighQuotient (μ : Measure E) (f : E → ℝ) : ENNReal :=
  ENNReal.ofReal (variance f μ) / ENNReal.ofReal (dirichletEnergy μ f)

theorem poincareRayleighQuotient_le_optimal {μ : Measure E} {f : E → ℝ}
    (hf : IsAdmissible μ f) :
    poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ := by
  apply le_optimalPoincareConstant
  intro C hC
  by_cases henergy : dirichletEnergy μ f = 0
  · have hvariance : variance f μ ≤ 0 := by
      simpa [henergy] using hC.variance_le hf
    simp [poincareRayleighQuotient, henergy, ENNReal.ofReal_eq_zero.mpr hvariance]
  · have henergy_pos : 0 < dirichletEnergy μ f :=
      lt_of_le_of_ne (dirichletEnergy_nonneg μ f) (Ne.symm henergy)
    have hquotient : variance f μ / dirichletEnergy μ f ≤ (C : ℝ) :=
      (div_le_iff₀ henergy_pos).2 (hC.variance_le hf)
    rw [poincareRayleighQuotient, ← ENNReal.ofReal_div_of_pos henergy_pos]
    simpa using ENNReal.ofReal_le_ofReal hquotient

theorem poincareRayleighQuotient_eq_of_pos {μ : Measure E} {f : E → ℝ}
    (henergy : 0 < dirichletEnergy μ f) :
    poincareRayleighQuotient μ f =
      ENNReal.ofReal (variance f μ / dirichletEnergy μ f) := by
  exact (ENNReal.ofReal_div_of_pos henergy).symm

theorem poincareRayleighQuotient_eq_top_of_energy_eq_zero {μ : Measure E} {f : E → ℝ}
    (hvariance : 0 < variance f μ) (henergy : dirichletEnergy μ f = 0) :
    poincareRayleighQuotient μ f = ⊤ := by
  have hnum : ENNReal.ofReal (variance f μ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hvariance)
  rw [poincareRayleighQuotient, henergy]
  simpa only [ENNReal.ofReal_zero] using ENNReal.div_zero hnum

theorem admissibleRayleighQuotient_le_optimal {μ : Measure E} {f : E → ℝ}
    (hf : IsAdmissible μ f) (henergy : 0 < dirichletEnergy μ f) :
    ENNReal.ofReal (variance f μ / dirichletEnergy μ f) ≤
      optimalPoincareConstant μ := by
  rw [← poincareRayleighQuotient_eq_of_pos henergy]
  exact poincareRayleighQuotient_le_optimal hf

end Issue2Autoformalization.Stage1A
