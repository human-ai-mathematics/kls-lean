module

public import FunctionalInequalities.Probability.Covariance.CauchySchwarz
public import FunctionalInequalities.Probability.Covariance.Whitening
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Audit: covariance Cauchy–Schwarz and whitened-statistic variance (supports of the BKL (68)
noise estimate)

Clients of `Probability/Covariance/CauchySchwarz.lean`
(`Probability.covariance_sq_le_variance_mul_variance`) and `Probability/Covariance/Whitening.lean`
section `WhitenedStatistic` (`Covariance.variance_inner_eq_of_sandwich`). Consumers: the normalized
two-atom law `(δ₋₂ + δ₂)/2` with the statistic `3x + 5` (covariance `12`, variances `4` and `36`,
so the Cauchy–Schwarz bound is tight), the constant statistic for the zero-variance branch, the
actual covariance operator `4·Id` with the self-adjoint `S = Id/2` and its derived sandwich, and
the rank-zero Dirac model where the operator ring has `0 = 1`. No posterior, root construction or
stochastic statement is involved; the sandwich is derived, not assumed.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace IndependentCovarianceSupports
open FunctionalInequalities

def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac (-2) + (1 / 2 : ENNReal) • Measure.dirac 2, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

theorem integral_μ (f : ℝ → ℝ) :
    (∫ x, f x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * f (-2) + (1 / 2 : ℝ) * f 2 := by
  have h0 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (-2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac (-2) +
    (1 / 2 : ENNReal) • Measure.dirac 2)) = _
  rw [integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  norm_num

theorem support_subset : (μ : Measure ℝ).support ⊆ ({(-2 : ℝ), 2} : Set ℝ) := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  change ((1 / 2 : ENNReal) • Measure.dirac (-2 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) ({(-2 : ℝ), 2} : Set ℝ)ᶜ = 0
  simp

theorem id_memLp : MemLp (id : ℝ → ℝ) 2 (μ : Measure ℝ) := by
  apply MemLp.of_bound continuous_id.aestronglyMeasurable 2
  filter_upwards [(μ : Measure ℝ).support_mem_ae] with x hx
  rcases support_subset hx with hx | hx
  · subst x
    norm_num
  · simp only [Set.mem_singleton_iff] at hx
    subst x
    norm_num

def Y (x : ℝ) : ℝ := 3 * x + 5

theorem Y_memLp : MemLp Y 2 (μ : Measure ℝ) :=
  (id_memLp.const_mul 3).add (memLp_const 5)

theorem covariance_values : covariance id id (μ : Measure ℝ) = 4 ∧
    covariance id Y (μ : Measure ℝ) = 12 := by
  constructor
  · rw [covariance_eq_sub id_memLp id_memLp]
    simp only [integral_μ, id_eq]
    norm_num
  · rw [covariance_eq_sub id_memLp Y_memLp]
    simp only [integral_μ, id_eq, Y]
    norm_num [Y]

theorem variance_values : variance id (μ : Measure ℝ) = 4 ∧
    variance Y (μ : Measure ℝ) = 36 := by
  constructor
  · have he : covariance id id (μ : Measure ℝ) = variance id (μ : Measure ℝ) :=
      covariance_self id_memLp.aestronglyMeasurable.aemeasurable
    rw [← he]
    exact covariance_values.1
  · rw [← covariance_self Y_memLp.aestronglyMeasurable.aemeasurable,
      covariance_eq_sub Y_memLp Y_memLp]
    simp only [integral_μ, Y]
    norm_num [Y]

/-- Tight nonconstant Cauchy-Schwarz consumer: 12^2 = 4*36. -/
theorem actual_NB1_nonzero : covariance id Y (μ : Measure ℝ) ^ 2 ≤
    variance id (μ : Measure ℝ) * variance Y (μ : Measure ℝ) :=
  Probability.covariance_sq_le_variance_mul_variance id_memLp Y_memLp

/-- The actual zero-variance-X branch is in scope. -/
theorem actual_NB1_zero_variance :
    variance (fun _ : ℝ => (7 : ℝ)) (μ : Measure ℝ) = 0 ∧
      covariance (fun _ : ℝ => (7 : ℝ)) Y (μ : Measure ℝ) ^ 2 ≤
        variance (fun _ : ℝ => (7 : ℝ)) (μ : Measure ℝ) * variance Y (μ : Measure ℝ) := by
  constructor
  · rw [←
      covariance_self
        (memLp_const (7 : ℝ) (p := 2) (μ := (μ : Measure ℝ))).aestronglyMeasurable.aemeasurable]
    rw [covariance_eq_sub (memLp_const 7) (memLp_const 7)]
    simp only [integral_μ]
    norm_num
  · exact Probability.covariance_sq_le_variance_mul_variance (memLp_const 7) Y_memLp

theorem covariance_operator_actual : Covariance.operator (μ : Measure ℝ) =
    (4 : ℝ) • (1 : ℝ →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Covariance.operator_inner, covarianceBilin_real, variance_values.1]
  simp only [smul_apply, one_apply_eq_self, Real.inner_apply]
  ring

def S : ℝ →L[ℝ] ℝ := (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)

theorem S_selfAdjoint : IsSelfAdjoint S := by
  change star S = S
  simp [S]

theorem actual_sandwich : S * Covariance.operator (μ : Measure ℝ) * S = 1 := by
  rw [covariance_operator_actual]
  apply ContinuousLinearMap.ext
  intro x
  simp only [S, mul_apply_eq_comp, smul_apply, one_apply_eq_self]
  ring

/-- The covariance operator and sandwich were actually derived from the finite law. -/
theorem actual_NB3 (h : ℝ) : variance (fun x => ⟪S h, x⟫) (μ : Measure ℝ) = ‖h‖ ^ 2 :=
  Covariance.variance_inner_eq_of_sandwich (μ : Measure ℝ) id_memLp S S_selfAdjoint
    actual_sandwich h

abbrev Ezero := EuclideanSpace ℝ (Fin 0)

theorem zero_id_memLp : MemLp (id : Ezero → Ezero) 2 (Measure.dirac (0 : Ezero)) := by
  have he : (id : Ezero → Ezero) = fun _ => (0 : Ezero) := by
    funext x
    exact Subsingleton.elim _ _
  rw [he]
  exact memLp_const 0

/-- Rank-zero operator ring has 0=1, so the real conditional sandwich endpoint applies. -/
theorem actual_NB3_rank_zero (h : Ezero) :
    variance (fun x : Ezero => ⟪(0 : Ezero →L[ℝ] Ezero) h, x⟫)
      (Measure.dirac (0 : Ezero)) = ‖h‖ ^ 2 := by
  have hs : IsSelfAdjoint (0 : Ezero →L[ℝ] Ezero) := by
    change star (0 : Ezero →L[ℝ] Ezero) = 0
    simp
  have hh : (0 : Ezero →L[ℝ] Ezero) *
      Covariance.operator (Measure.dirac (0 : Ezero)) * 0 = 1 := Subsingleton.elim _ _
  exact Covariance.variance_inner_eq_of_sandwich (Measure.dirac (0 : Ezero))
    zero_id_memLp 0 hs hh h

#print axioms integral_μ
#print axioms support_subset
#print axioms id_memLp
#print axioms Y_memLp
#print axioms covariance_values
#print axioms variance_values
#print axioms actual_NB1_nonzero
#print axioms actual_NB1_zero_variance
#print axioms covariance_operator_actual
#print axioms S_selfAdjoint
#print axioms actual_sandwich
#print axioms actual_NB3
#print axioms zero_id_memLp
#print axioms actual_NB3_rank_zero
#print axioms μ
#print axioms Y
#print axioms S
#print axioms Ezero
end IndependentCovarianceSupports
