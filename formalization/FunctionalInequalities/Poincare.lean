import FunctionalInequalities.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# The linear-test lower bound (`KLS.pdf`, Remark 3.8)

The reference observes that every test function gives the lower bound
`C_P ≥ Var_P(f) / E_P ‖∇f‖²`, and that the linear choice `f(x) = ⟪v, x⟫` gives
`C_P ≥ λ_max(Cov_P)`.  This module formalizes those two claims for the explicit test core of
Definition 2.1 and measures with the moments needed to define covariance.

The covariance is centered.  Its real Rayleigh supremum is represented by
`Covariance.lambdaMax` in `ENNReal`; in a nontrivial finite-dimensional space it is the usual
largest covariance eigenvalue, while in dimension zero the empty supremum is defined to be `0`.
The mode-indicator observation in Remark 3.8, the Gaussian upper bound in Family 4.1, and all
log-Sobolev and transportation-cost statements are outside this module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities

namespace Poincare

section LinearTestGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The test `f(x) = ⟪v, x⟫` used in `KLS.pdf`, Remark 3.8 and Family 4.1. -/
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

/-- The reference calculation `E_P ‖∇f‖² = ‖v‖²` for `f(x) = ⟪v, x⟫`. -/
theorem energy_linearTest (μ : Measure E) [IsProbabilityMeasure μ] (v : E) :
    energy μ (linearTest v) = ‖v‖ ^ 2 := by
  simp [energy]

/-- A finite second moment makes every linear projection an admissible Definition 2.1 test. -/
theorem linearTest_admissible {μ : Measure E} (hprob : IsProbabilityMeasure μ)
    (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    Admissible μ (linearTest v) := by
  let _ := hprob
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ ⊤ (fun x ↦ inner ℝ v x)
    exact (innerSL ℝ v).contDiff
  · change MemLp (fun x ↦ inner ℝ v x) 2 μ
    simpa only [id_eq, innerSL_apply_apply] using
      hμ.continuousLinearMap_comp (innerSL ℝ v)
  · simp

/-- The fixed-constant form of the linear-test calculation:
`Var_μ(⟪v, ·⟫) ≤ C ‖v‖²`. -/
theorem variance_linearTest_le {μ : Measure E} {C : ℝ}
    (hP : Holds μ C) (hμ : MemLp (id : E → E) 2 μ) (v : E) :
    variance (linearTest v) μ ≤ C * ‖v‖ ^ 2 := by
  let _ := hP.probability
  simpa [energy_linearTest] using
    hP.variance_le (linearTest_admissible hP.probability hμ v)

/-- The Rayleigh quotient `Var_P(f) / E_P ‖∇f‖²` from Remark 3.8, extended to `ENNReal`.
Converting numerator and denominator before division makes positive variance over zero energy
equal to `⊤`, while `0 / 0 = 0`. -/
def rayleigh (μ : Measure E) (f : E → ℝ) : ENNReal :=
  ENNReal.ofReal (variance f μ) / ENNReal.ofReal (energy μ f)

/-- Formal version of the first sentence of Remark 3.8: every admissible test gives a lower bound
on the optimal Poincaré constant.  The `ENNReal` statement also covers zero energy and the case
where no finite Poincaré constant exists. -/
theorem rayleigh_le_constant {μ : Measure E} {f : E → ℝ}
    (hf : Admissible μ f) :
    rayleigh μ f ≤ constant μ := by
  apply le_constant
  intro C hC
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.zero_le_coe)]
  exact ENNReal.ofReal_le_ofReal (hC.variance_le hf)

/-- At positive energy, the extended quotient agrees with the ordinary real quotient. -/
theorem rayleigh_eq_of_energy_pos {μ : Measure E} {f : E → ℝ}
    (henergy : 0 < energy μ f) :
    rayleigh μ f = ENNReal.ofReal (variance f μ / energy μ f) := by
  rw [rayleigh, ENNReal.ofReal_div_of_pos henergy]

/-- Positive variance and zero energy produce an infinite extended Rayleigh quotient. -/
theorem rayleigh_eq_top_of_energy_zero {μ : Measure E} {f : E → ℝ}
    (hvariance : 0 < variance f μ) (henergy : energy μ f = 0) :
    rayleigh μ f = ⊤ := by
  rw [rayleigh, henergy, ENNReal.ofReal_zero]
  exact ENNReal.div_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hvariance))

/-- The positive-energy specialization in the exact real-quotient notation of Remark 3.8. -/
theorem realRayleigh_le_constant {μ : Measure E} {f : E → ℝ}
    (hf : Admissible μ f) (henergy : 0 < energy μ f) :
    ENNReal.ofReal (variance f μ / energy μ f) ≤ constant μ := by
  rw [← rayleigh_eq_of_energy_pos henergy]
  exact rayleigh_le_constant hf

end LinearTestAnalysis

end Poincare

namespace Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The centered `Cov_P` in Remark 3.8, obtained from Mathlib's centered covariance bilinear form
by Riesz representation.  This deliberately does not use Mathlib's uncentered
`ProbabilityTheory.covarianceOperator`. -/
def operator (μ : Measure E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)

@[simp]
theorem operator_inner (μ : Measure E) (x y : E) :
    inner ℝ (operator μ x) y = covarianceBilin μ x y := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (covarianceBilin μ) x y

theorem operator_isSymmetric (μ : Measure E) :
    (operator μ).toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ (operator μ x) y = covarianceBilin μ x y := operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = inner ℝ (operator μ y) x := (operator_inner μ y x).symm
    _ = inner ℝ x (operator μ y) := real_inner_comm _ _

theorem operator_self_nonneg (μ : Measure E) (x : E) :
    0 ≤ inner ℝ (operator μ x) x := by
  rw [operator_inner]
  exact covarianceBilin_self_nonneg x

/-- The reference identity `Var_P(⟪v, ·⟫) = ⟪Cov_P v, v⟫`. -/
theorem operator_self_eq_variance {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (x : E) :
    inner ℝ (operator μ x) x = variance (Poincare.linearTest x) μ := by
  rw [operator_inner, covarianceBilin_self hμ, Poincare.linearTest_eq_inner]

/-- The real supremum of the centered covariance operator's Rayleigh quotient over nonzero
vectors. -/
def rayleighMax (μ : Measure E) : ℝ :=
  ⨆ x : {x : E // x ≠ 0}, (operator μ).rayleighQuotient x

/-- Unit-vector formulation used in the natural-language proof: the supremal operator Rayleigh
quotient is the supremum of the centered covariance quadratic form on the unit sphere. -/
theorem rayleighMax_eq_iSup_sphere (μ : Measure E) :
    rayleighMax μ = ⨆ v : Metric.sphere (0 : E) 1, covarianceBilin μ v v := by
  rw [rayleighMax, (operator μ).iSup_rayleigh_eq_iSup_rayleigh_sphere zero_lt_one]
  congr 1
  funext v
  have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  simp [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, operator_inner, hvnorm]

/-- Positivity of the covariance form makes its supremal Rayleigh quotient nonnegative, including
the zero-dimensional empty-supremum case. -/
theorem rayleighMax_nonneg (μ : Measure E) :
    0 ≤ rayleighMax μ := by
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hbdd : BddAbove
        (Set.range fun x : {x : E // x ≠ 0} ↦ (operator μ).rayleighQuotient x) := by
      refine ⟨‖operator μ‖, ?_⟩
      rintro y ⟨v, rfl⟩
      exact (le_abs_self _).trans ((operator μ).rayleighQuotient_le_norm v)
    apply le_ciSup_of_le hbdd ⟨x, hx⟩
    change 0 ≤ inner ℝ (operator μ x) x / ‖x‖ ^ 2
    exact div_nonneg (operator_self_nonneg μ x) (sq_nonneg _)
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [rayleighMax, Real.iSup_of_isEmpty]

/-- In a nontrivial finite-dimensional space, `rayleighMax` is an actual eigenvalue of the
centered covariance operator. -/
theorem operator_hasEigenvalue_rayleighMax
    [FiniteDimensional ℝ E] [Nontrivial E] (μ : Measure E) :
    Module.End.HasEigenvalue (operator μ).toLinearMap (rayleighMax μ) := by
  exact (operator_isSymmetric μ).hasEigenvalue_iSup_of_finiteDimensional

/-- The quantity denoted `λ_max(Cov_P)` in Remark 3.8, represented in `ENNReal`.

On a nontrivial finite-dimensional space the real value inside `ENNReal.ofReal` is the usual
largest covariance eigenvalue by the Rayleigh--Ritz theorem above.  If `E` is zero-dimensional,
the indexing type of nonzero vectors is empty and this value is `0`. -/
def lambdaMax (μ : Measure E) : ENNReal :=
  ENNReal.ofReal (rayleighMax μ)

@[simp]
theorem lambdaMax_toReal (μ : Measure E) :
    (lambdaMax μ).toReal = rayleighMax μ := by
  simp [lambdaMax, rayleighMax_nonneg μ]

theorem lambdaMax_eq_zero_of_subsingleton [Subsingleton E] (μ : Measure E) :
    lambdaMax μ = 0 := by
  let _ : IsEmpty {x : E // x ≠ 0} :=
    ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
  rw [lambdaMax, rayleighMax, Real.iSup_of_isEmpty]
  exact ENNReal.ofReal_zero

/-- The Rayleigh maximum is finite because the centered covariance form has a bounded Riesz
operator. -/
theorem lambdaMax_le_norm (μ : Measure E) :
    lambdaMax μ ≤ ENNReal.ofReal ‖operator μ‖ := by
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    let _ : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
    refine ciSup_le fun x ↦ ?_
    exact (le_abs_self _).trans ((operator μ).rayleighQuotient_le_norm x)
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [rayleighMax, Real.iSup_of_isEmpty]
    exact norm_nonneg _

theorem lambdaMax_ne_top (μ : Measure E) :
    lambdaMax μ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lambdaMax_le_norm μ)

/-- Linear tests yield `λ_max(Cov_P) ≤ C` for every finite valid Poincaré constant `C`. -/
theorem lambdaMax_le {μ : Measure E} {C : ℝ}
    (hP : Poincare.Holds μ C) (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMax μ ≤ ENNReal.ofReal C := by
  let _ := hP.probability
  apply ENNReal.ofReal_le_ofReal
  by_cases hE : Nontrivial E
  · let _ := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    let _ : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
    refine ciSup_le fun v ↦ ?_
    have hv := Poincare.variance_linearTest_le hP hμ (v : E)
    have hvnorm : 0 < ‖(v : E)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr v.property)
    apply (div_le_iff₀ hvnorm).2
    change inner ℝ (operator μ (v : E)) v ≤ C * ‖(v : E)‖ ^ 2
    rw [operator_self_eq_variance hμ]
    simpa only [mul_comm] using hv
  · have _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    let _ : IsEmpty {x : E // x ≠ 0} :=
      ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    rw [rayleighMax, Real.iSup_of_isEmpty]
    exact hP.constant_nonneg

/-- Formal version of the linear half of Remark 3.8:
`λ_max(Cov_P) ≤ C_P` for the optimal extended Poincaré constant. -/
theorem lambdaMax_le_constant {μ : Measure E}
    (hμ : MemLp (id : E → E) 2 μ) :
    lambdaMax μ ≤ Poincare.constant μ := by
  apply Poincare.le_constant
  intro C hC
  simpa only [ENNReal.ofReal_coe_nnreal] using lambdaMax_le hC hμ

end Covariance

end FunctionalInequalities
