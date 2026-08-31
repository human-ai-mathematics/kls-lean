import FunctionalInequalities.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Linear tests and covariance for Poincaré inequalities

This module proves the reusable fixed-constant linear-test inequality and connects it to the
centered covariance operator.  The real `covarianceRayleighMax` is the supremum of that operator's
Rayleigh quotient, and `lambdaMaxCovariance` is its nonnegative `ENNReal` representation.  In a
nontrivial finite-dimensional space the same real supremum is an actual eigenvalue; in the
zero-dimensional space the empty supremum, and hence `lambdaMaxCovariance`, is `0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities

section LinearTestGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear Poincaré test in direction `v`. -/
def linearTest (v : E) : E → ℝ := fun x ↦ inner ℝ v x

@[simp]
theorem linearTest_apply (v x : E) : linearTest v x = inner ℝ v x :=
  rfl

theorem linearTest_eq_inner (v : E) : linearTest v = fun x ↦ inner ℝ v x :=
  rfl

end LinearTestGeometry

section LinearTestAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- The canonical gradient of `x ↦ inner ℝ v x` is the constant vector `v`. -/
theorem hasGradientAt_linearTest (v x : E) : HasGradientAt (linearTest v) v x := by
  change HasFDerivAt (linearTest v) (InnerProductSpace.toDual ℝ E v) x
  convert (innerSL ℝ v).hasFDerivAt using 1 <;> ext <;> rfl

omit [MeasurableSpace E] in
@[simp]
theorem gradient_linearTest (v x : E) : gradient (linearTest v) x = v :=
  (hasGradientAt_linearTest v x).gradient

/-- Under probability normalization, the linear test has Dirichlet energy `‖v‖²`. -/
theorem dirichletEnergy_linearTest (μ : Measure E) [IsProbabilityMeasure μ] (v : E) :
    dirichletEnergy μ (linearTest v) = ‖v‖ ^ 2 := by
  simp [dirichletEnergy]

/-- A finite second moment of the identity makes every linear projection admissible. -/
theorem isAdmissible_linearTest {μ : Measure E} (hprob : IsProbabilityMeasure μ)
    (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    IsAdmissible μ (linearTest v) := by
  let _ := hprob
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ ⊤ (fun x ↦ inner ℝ v x)
    exact (innerSL ℝ v).contDiff
  · change MemLp (fun x ↦ inner ℝ v x) 2 μ
    simpa only [id_eq, innerSL_apply_apply] using
      hμ.continuousLinearMap_comp (innerSL ℝ v)
  · simp

/-- The fixed-constant linear-test bound. -/
theorem variance_linearTest_le {μ : Measure E} {C : ℝ}
    (hP : HasPoincare μ C) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    variance (linearTest v) μ ≤ C * ‖v‖ ^ 2 := by
  let _ := hP.isProbabilityMeasure
  simpa [dirichletEnergy_linearTest] using
    hP.variance_le (isAdmissible_linearTest hP.isProbabilityMeasure hμ v)

/-- The extended Rayleigh quotient.  Using `ENNReal` before division gives the intended boundary
semantics: positive variance divided by zero energy is `⊤`, while `0 / 0 = 0`. -/
def poincareRayleighQuotient (μ : Measure E) (f : E → ℝ) : ENNReal :=
  ENNReal.ofReal (variance f μ) / ENNReal.ofReal (dirichletEnergy μ f)

/-- Every admissible test has extended Rayleigh quotient below the extended optimal Poincaré
constant, including the zero-energy and no-finite-constant cases. -/
theorem poincareRayleighQuotient_le_optimal {μ : Measure E} {f : E → ℝ}
    (hf : IsAdmissible μ f) :
    poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ := by
  apply le_optimalPoincareConstant
  intro C hC
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.zero_le_coe)]
  exact ENNReal.ofReal_le_ofReal (hC.variance_le hf)

/-- At positive energy, the extended quotient agrees with the ordinary real quotient. -/
theorem poincareRayleighQuotient_eq_of_pos {μ : Measure E} {f : E → ℝ}
    (henergy : 0 < dirichletEnergy μ f) :
    poincareRayleighQuotient μ f =
      ENNReal.ofReal (variance f μ / dirichletEnergy μ f) := by
  rw [poincareRayleighQuotient, ENNReal.ofReal_div_of_pos henergy]

/-- Positive variance and zero energy produce an infinite extended Rayleigh quotient. -/
theorem poincareRayleighQuotient_eq_top_of_energy_eq_zero {μ : Measure E} {f : E → ℝ}
    (hvariance : 0 < variance f μ) (henergy : dirichletEnergy μ f = 0) :
    poincareRayleighQuotient μ f = ⊤ := by
  rw [poincareRayleighQuotient, henergy, ENNReal.ofReal_zero]
  exact ENNReal.div_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hvariance))

/-- Positive-energy specialization in the real-quotient notation used by the manuscript. -/
theorem admissibleRayleighQuotient_le_optimal {μ : Measure E} {f : E → ℝ}
    (hf : IsAdmissible μ f) (henergy : 0 < dirichletEnergy μ f) :
    ENNReal.ofReal (variance f μ / dirichletEnergy μ f) ≤
      optimalPoincareConstant μ := by
  rw [← poincareRayleighQuotient_eq_of_pos henergy]
  exact poincareRayleighQuotient_le_optimal hf

end LinearTestAnalysis

section CenteredCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The centered covariance operator obtained from Mathlib's centered covariance bilinear form
by Riesz representation.  This deliberately does not use Mathlib's uncentered
`ProbabilityTheory.covarianceOperator`. -/
def centeredCovarianceOperator (μ : Measure E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)

@[simp]
theorem centeredCovarianceOperator_inner (μ : Measure E) (x y : E) :
    inner ℝ (centeredCovarianceOperator μ x) y = covarianceBilin μ x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (covarianceBilin μ) x y

theorem centeredCovarianceOperator_isSymmetric (μ : Measure E) :
    (centeredCovarianceOperator μ).toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ (centeredCovarianceOperator μ x) y = covarianceBilin μ x y :=
      centeredCovarianceOperator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = inner ℝ (centeredCovarianceOperator μ y) x :=
      (centeredCovarianceOperator_inner μ y x).symm
    _ = inner ℝ x (centeredCovarianceOperator μ y) := real_inner_comm _ _

theorem centeredCovarianceOperator_self_nonneg (μ : Measure E) (x : E) :
    0 ≤ inner ℝ (centeredCovarianceOperator μ x) x := by
  rw [centeredCovarianceOperator_inner]
  exact covarianceBilin_self_nonneg x

/-- The covariance quadratic form is the variance of the corresponding linear projection. -/
theorem centeredCovarianceOperator_self_eq_variance {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (x : E) :
    inner ℝ (centeredCovarianceOperator μ x) x = variance (linearTest x) μ := by
  rw [centeredCovarianceOperator_inner, covarianceBilin_self hμ, linearTest_eq_inner]

/-- The real supremum of the centered covariance operator's Rayleigh quotient over nonzero
vectors. -/
def covarianceRayleighMax (μ : Measure E) : ℝ :=
  ⨆ x : {x : E // x ≠ 0},
    (centeredCovarianceOperator μ).rayleighQuotient x

/-- Unit-vector formulation used in the natural-language proof: the supremal operator Rayleigh
quotient is the supremum of the centered covariance quadratic form on the unit sphere. -/
theorem covarianceRayleighMax_eq_iSup_covariance_sphere (μ : Measure E) :
    covarianceRayleighMax μ =
      ⨆ v : Metric.sphere (0 : E) 1, covarianceBilin μ v v := by
  rw [covarianceRayleighMax,
    (centeredCovarianceOperator μ).iSup_rayleigh_eq_iSup_rayleigh_sphere zero_lt_one]
  congr 1
  funext v
  have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, centeredCovarianceOperator_inner, hvnorm]

/-- Positivity of the covariance form makes its supremal Rayleigh quotient nonnegative, including
the zero-dimensional empty-supremum case. -/
theorem covarianceRayleighMax_nonneg (μ : Measure E) :
    0 ≤ covarianceRayleighMax μ := by
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hbdd : BddAbove
        (Set.range fun x : {x : E // x ≠ 0} ↦
          (centeredCovarianceOperator μ).rayleighQuotient x) := by
      refine ⟨‖centeredCovarianceOperator μ‖, ?_⟩
      rintro y ⟨v, rfl⟩
      exact (le_abs_self _).trans
        ((centeredCovarianceOperator μ).rayleighQuotient_le_norm v)
    apply le_ciSup_of_le hbdd ⟨x, hx⟩
    change 0 ≤ inner ℝ (centeredCovarianceOperator μ x) x / ‖x‖ ^ 2
    exact div_nonneg (centeredCovarianceOperator_self_nonneg μ x) (sq_nonneg _)
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [covarianceRayleighMax, Real.iSup_of_isEmpty]

/-- In a nontrivial finite-dimensional space, `covarianceRayleighMax` is an actual eigenvalue of
the centered covariance operator. -/
theorem centeredCovarianceOperator_hasEigenvalue_iSup
    [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) :
    Module.End.HasEigenvalue (centeredCovarianceOperator μ).toLinearMap
      (covarianceRayleighMax μ) := by
  exact (centeredCovarianceOperator_isSymmetric μ).hasEigenvalue_iSup_of_finiteDimensional

/-- The largest centered-covariance Rayleigh value, represented in `ENNReal`.

On a nontrivial finite-dimensional space the real value inside `ENNReal.ofReal` is the usual
largest covariance eigenvalue by the Rayleigh--Ritz theorem above.  If `E` is zero-dimensional,
the indexing type of nonzero vectors is empty and this value is `0`. -/
def lambdaMaxCovariance (μ : Measure E) : ENNReal :=
  ENNReal.ofReal (covarianceRayleighMax μ)

@[simp]
theorem lambdaMaxCovariance_toReal (μ : Measure E) :
    (lambdaMaxCovariance μ).toReal = covarianceRayleighMax μ := by
  simp [lambdaMaxCovariance, covarianceRayleighMax_nonneg μ]

theorem lambdaMaxCovariance_eq_zero_of_subsingleton [Subsingleton E] (μ : Measure E) :
    lambdaMaxCovariance μ = 0 := by
  let _ : IsEmpty {x : E // x ≠ 0} :=
    ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
  rw [lambdaMaxCovariance, covarianceRayleighMax, Real.iSup_of_isEmpty]
  exact ENNReal.ofReal_zero

/-- The Rayleigh maximum is finite because the centered covariance form has a bounded Riesz
operator. -/
theorem lambdaMaxCovariance_le_operatorNorm (μ : Measure E) :
    lambdaMaxCovariance μ ≤ ENNReal.ofReal ‖centeredCovarianceOperator μ‖ := by
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    let _ : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
    refine ciSup_le fun x ↦ ?_
    exact (le_abs_self _).trans
      ((centeredCovarianceOperator μ).rayleighQuotient_le_norm x)
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [covarianceRayleighMax, Real.iSup_of_isEmpty]
    exact norm_nonneg _

theorem lambdaMaxCovariance_ne_top (μ : Measure E) :
    lambdaMaxCovariance μ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lambdaMaxCovariance_le_operatorNorm μ)

/-- A fixed Poincaré constant bounds the largest covariance Rayleigh value. -/
theorem lambdaMaxCovariance_le {μ : Measure E} {C : ℝ}
    (hP : HasPoincare μ C) (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ ENNReal.ofReal C := by
  let _ := hP.isProbabilityMeasure
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    let _ : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
    refine ciSup_le fun v ↦ ?_
    have hv := variance_linearTest_le hP hμ (v : E)
    have hvnorm : 0 < ‖(v : E)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr v.property)
    apply (div_le_iff₀ hvnorm).2
    change inner ℝ (centeredCovarianceOperator μ (v : E)) v ≤ C * ‖(v : E)‖ ^ 2
    rw [centeredCovarianceOperator_self_eq_variance hμ]
    simpa only [mul_comm] using hv
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [covarianceRayleighMax, Real.iSup_of_isEmpty]
    exact hP.constant_nonneg

/-- The linear-test lower bound for the extended optimal Poincaré constant. -/
theorem lambdaMaxCovariance_le_optimal {μ : Measure E}
    (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMaxCovariance μ ≤ optimalPoincareConstant μ := by
  apply le_optimalPoincareConstant
  intro C hC
  simpa only [ENNReal.ofReal_coe_nnreal] using lambdaMaxCovariance_le hC hμ

end CenteredCovariance

end FunctionalInequalities
