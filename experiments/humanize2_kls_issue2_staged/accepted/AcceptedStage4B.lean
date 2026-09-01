import AcceptedStage4A

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

theorem centeredCovarianceOperator_hasEigenvalue_iSup
    [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) :
    Module.End.HasEigenvalue (centeredCovarianceOperator μ).toLinearMap
      (covarianceRayleighMax μ) := by
  exact
    (centeredCovarianceOperator_isSymmetric μ).hasEigenvalue_iSup_of_finiteDimensional

def lambdaMaxCovariance (μ : Measure E) : ENNReal :=
  ENNReal.ofReal (covarianceRayleighMax μ)

@[simp]
theorem lambdaMaxCovariance_toReal (μ : Measure E) :
    (lambdaMaxCovariance μ).toReal = covarianceRayleighMax μ := by
  simp [lambdaMaxCovariance, covarianceRayleighMax_nonneg]

theorem lambdaMaxCovariance_eq_zero_of_subsingleton [Subsingleton E] (μ : Measure E) :
    lambdaMaxCovariance μ = 0 := by
  let _ : IsEmpty {x : E // x ≠ 0} :=
    ⟨fun x ↦ x.property (Subsingleton.elim (x : E) (0 : E))⟩
  simp [lambdaMaxCovariance, covarianceRayleighMax, Real.iSup_of_isEmpty]

theorem lambdaMaxCovariance_le_operatorNorm (μ : Measure E) :
    lambdaMaxCovariance μ ≤ ENNReal.ofReal ‖centeredCovarianceOperator μ‖ := by
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nonempty {x : E // x ≠ 0}
  · let _ : Nonempty {x : E // x ≠ 0} := hE
    rw [covarianceRayleighMax]
    refine ciSup_le fun x ↦ ?_
    exact (le_abs_self _).trans
      ((centeredCovarianceOperator μ).rayleighQuotient_le_norm x)
  · let _ : IsEmpty {x : E // x ≠ 0} := ⟨fun x ↦ hE ⟨x⟩⟩
    rw [covarianceRayleighMax, Real.iSup_of_isEmpty]
    exact norm_nonneg _

theorem lambdaMaxCovariance_ne_top (μ : Measure E) :
    lambdaMaxCovariance μ ≠ ⊤ := by
  simp [lambdaMaxCovariance]

theorem lambdaMaxCovariance_le {μ : Measure E} {C : ℝ}
    (hP : HasPoincare μ C) (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ ENNReal.ofReal C := by
  apply ENNReal.ofReal_le_ofReal
  let _ := hP.isProbabilityMeasure
  by_cases hE : Nonempty {x : E // x ≠ 0}
  · let _ : Nonempty {x : E // x ≠ 0} := hE
    rw [covarianceRayleighMax]
    refine ciSup_le fun x ↦ ?_
    have hxnorm : 0 < ‖(x : E)‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr x.property)
    apply (div_le_iff₀ hxnorm).2
    change inner ℝ (centeredCovarianceOperator μ (x : E)) (x : E) ≤ C * ‖(x : E)‖ ^ 2
    rw [centeredCovarianceOperator_self_eq_variance hμ]
    exact variance_linearTest_le hP hμ x
  · let _ : IsEmpty {x : E // x ≠ 0} := ⟨fun x ↦ hE ⟨x⟩⟩
    rw [covarianceRayleighMax, Real.iSup_of_isEmpty]
    exact hP.constant_nonneg

theorem lambdaMaxCovariance_le_optimal {μ : Measure E}
    (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ := by
  apply le_optimalPoincareConstant
  intro C hC
  simpa using lambdaMaxCovariance_le hC hμ

end Issue2Autoformalization.Stage1A
