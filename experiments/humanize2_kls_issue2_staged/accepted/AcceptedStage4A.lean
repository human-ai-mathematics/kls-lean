import AcceptedStage3
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Issue2Autoformalization.Stage1A

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

def centeredCovarianceOperator (μ : Measure E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin μ)

@[simp]
theorem centeredCovarianceOperator_inner (μ : Measure E) (x y : E) :
    inner ℝ (centeredCovarianceOperator μ x) y = covarianceBilin μ x y := by
  simp [centeredCovarianceOperator]

theorem centeredCovarianceOperator_isSymmetric (μ : Measure E) :
    (centeredCovarianceOperator μ).toLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ ((centeredCovarianceOperator μ) x) y = covarianceBilin μ x y :=
      centeredCovarianceOperator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = inner ℝ ((centeredCovarianceOperator μ) y) x :=
      (centeredCovarianceOperator_inner μ y x).symm
    _ = inner ℝ x ((centeredCovarianceOperator μ) y) := real_inner_comm _ _

theorem centeredCovarianceOperator_self_nonneg (μ : Measure E) (x : E) :
    0 ≤ inner ℝ (centeredCovarianceOperator μ x) x := by
  rw [centeredCovarianceOperator_inner]
  exact covarianceBilin_self_nonneg (μ := μ) x

theorem centeredCovarianceOperator_self_eq_variance {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : MemLp (id : E → E) 2 μ) (x : E) :
    inner ℝ (centeredCovarianceOperator μ x) x = variance (linearTest x) μ := by
  rw [centeredCovarianceOperator_inner]
  rw [covarianceBilin_apply]
  have hid : Integrable (id : E → E) μ := hμ.integrable (by norm_num)
  have hmean : inner ℝ x (∫ z : E, id z ∂μ) = ∫ z : E, linearTest x z ∂μ := by
    change (InnerProductSpace.toDual ℝ E x) (∫ z : E, id z ∂μ) =
      ∫ z : E, (InnerProductSpace.toDual ℝ E x) (id z) ∂μ
    exact ((InnerProductSpace.toDual ℝ E x).integral_comp_comm hid).symm
  have hmean' : inner ℝ x (∫ z : E, z ∂μ) = ∫ z : E, inner ℝ x z ∂μ := by
    simpa [linearTest] using hmean
  change (∫ z : E, inner ℝ x (z - ∫ z : E, id z ∂μ) *
    inner ℝ x (z - ∫ z : E, id z ∂μ) ∂μ) =
      variance (fun z : E ↦ inner ℝ x (id z)) μ
  rw [← covariance_self (hμ.const_inner x).aestronglyMeasurable.aemeasurable]
  rw [covariance]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [inner_sub_right, id_eq, hmean']
  exact hμ

def covarianceRayleighMax (μ : Measure E) : ℝ :=
  ⨆ x : {x : E // x ≠ 0},
    (centeredCovarianceOperator μ).rayleighQuotient x

theorem covarianceRayleighMax_eq_iSup_covariance_sphere (μ : Measure E) :
    covarianceRayleighMax μ =
      ⨆ v : Metric.sphere (0 : E) 1, covarianceBilin μ v v := by
  change sSup (Set.range (fun x : {x : E // x ≠ 0} ↦
    (centeredCovarianceOperator μ).rayleighQuotient x)) =
      sSup (Set.range (fun v : Metric.sphere (0 : E) 1 ↦ covarianceBilin μ v v))
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    have hxnorm : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.property
    let v : E := ‖(x : E)‖⁻¹ • (x : E)
    have hvnorm : ‖v‖ = 1 := by
      simp [v, norm_smul, hxnorm]
    refine ⟨⟨v, ?_⟩, ?_⟩
    · change dist v 0 = 1
      rw [dist_zero_right]
      exact hvnorm
    · have hop : (centeredCovarianceOperator μ).reApplyInnerSelf (x : E) =
          covarianceBilin μ x x := by
        change inner ℝ (centeredCovarianceOperator μ x) x = covarianceBilin μ x x
        exact centeredCovarianceOperator_inner μ x x
      simp [ContinuousLinearMap.rayleighQuotient, v, hop, div_eq_mul_inv, pow_two]
      ring
  · rintro ⟨v, rfl⟩
    have hvnorm : ‖(v : E)‖ = 1 := by
      have hvdist := v.property
      change dist (v : E) 0 = 1 at hvdist
      rw [dist_zero_right] at hvdist
      exact hvdist
    have hvne : (v : E) ≠ 0 := by
      intro hv
      simp [hv] at hvnorm
    refine ⟨⟨v, hvne⟩, ?_⟩
    have hop : (centeredCovarianceOperator μ).reApplyInnerSelf (v : E) =
        covarianceBilin μ v v := by
      change inner ℝ (centeredCovarianceOperator μ v) v = covarianceBilin μ v v
      exact centeredCovarianceOperator_inner μ v v
    simp [ContinuousLinearMap.rayleighQuotient, hvnorm, hop]

theorem covarianceRayleighMax_nonneg (μ : Measure E) :
    0 ≤ covarianceRayleighMax μ := by
  by_cases hE : Nonempty {x : E // x ≠ 0}
  · let x := hE.some
    have hbound : BddAbove (Set.range (fun x : {x : E // x ≠ 0} ↦
        (centeredCovarianceOperator μ).rayleighQuotient x)) := by
      refine ⟨‖centeredCovarianceOperator μ‖, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact (le_abs_self _).trans
        ((centeredCovarianceOperator μ).rayleighQuotient_le_norm y)
    refine le_trans ?_ (le_ciSup hbound x)
    exact div_nonneg (centeredCovarianceOperator_self_nonneg μ x) (sq_nonneg ‖(x : E)‖)
  · have : IsEmpty {x : E // x ≠ 0} := ⟨fun x ↦ hE ⟨x⟩⟩
    rw [covarianceRayleighMax, Real.iSup_of_isEmpty]

end Issue2Autoformalization.Stage1A
