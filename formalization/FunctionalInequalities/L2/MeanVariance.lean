import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

/-!
# Mean and variance in real `L²`

This module packages constant functions, the mean, centering, and variance directly in real
`L²` over a `ProbabilityMeasure`. The variance is `NNReal`-valued by construction: it is the
square of the norm of the centered element. Basic identities are stated without choosing
pointwise representatives.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.L2

variable {α : Type*} [MeasurableSpace α]

/-- The element of real `L²(μ)` represented almost everywhere by the constant `c`. -/
def const (μ : ProbabilityMeasure α) (c : ℝ) : Lp ℝ 2 (μ : Measure α) :=
  Lp.const 2 (μ : Measure α) c

/-- The `L²` constant has the expected pointwise representative almost everywhere. -/
theorem const_coeFn (μ : ProbabilityMeasure α) (c : ℝ) :
    const μ c =ᵐ[(μ : Measure α)] fun _ ↦ c := by
  change Lp.const 2 (μ : Measure α) c =ᵐ[(μ : Measure α)] Function.const α c
  exact Lp.coeFn_const 2 (μ : Measure α) c

/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))

/-- Embedding constants into `L²` preserves addition. -/
@[simp]
theorem const_add (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c + d) = const μ c + const μ d :=
  map_add (Lp.const 2 (μ : Measure α)) c d

/-- Embedding constants into real `L²` preserves scalar multiplication. -/
@[simp]
theorem const_smul (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c * d) = c • const μ d := by
  exact (Lp.constₗ 2 (μ : Measure α) ℝ).map_smul c d

/-- The mean of `f ∈ L²(μ)` is its real inner product with the constant one. -/
def mean (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) : ℝ :=
  inner ℝ f (const μ 1)

/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]

/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp

/-- The mean of zero is zero. -/
@[simp]
theorem mean_zero (μ : ProbabilityMeasure α) : mean μ 0 = 0 := by
  simp [mean]

/-- The mean preserves addition. -/
@[simp]
theorem mean_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f + g) = mean μ f + mean μ g := by
  rw [mean, inner_add_left]
  rfl

/-- The mean preserves real scalar multiplication. -/
@[simp]
theorem mean_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (c • f) = c * mean μ f := by
  rw [mean, inner_smul_left]
  rfl

/-- The mean preserves negation. -/
@[simp]
theorem mean_neg (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (-f) = -mean μ f := by
  simp [mean]

/-- The mean preserves subtraction. -/
@[simp]
theorem mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl

/-- Centering subtracts the constant `L²` element whose value is the mean. -/
def center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    Lp ℝ 2 (μ : Measure α) :=
  f - const μ (mean μ f)

/-- The centered representative is pointwise `f - mean μ f` almost everywhere. -/
theorem center_coeFn (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ f =ᵐ[(μ : Measure α)] fun x ↦ f x - mean μ f := by
  exact (Lp.coeFn_sub f (const μ (mean μ f))).trans
    (ae_eq_rfl.sub (const_coeFn μ (mean μ f)))

/-- Centering the zero element gives zero. -/
@[simp]
theorem center_zero (μ : ProbabilityMeasure α) : center μ 0 = 0 := by
  simp [center]

/-- Every constant `L²` element centers to zero. -/
@[simp]
theorem center_const (μ : ProbabilityMeasure α) (c : ℝ) : center μ (const μ c) = 0 := by
  simp [center]

/-- Centering preserves addition. -/
@[simp]
theorem center_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    center μ (f + g) = center μ f + center μ g := by
  simp only [center, mean_add, const_add]
  abel

/-- Centering commutes with real scalar multiplication. -/
@[simp]
theorem center_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (c • f) = c • center μ f := by
  simp only [center, mean_smul, const_smul, smul_sub]

/-- Adding a constant `L²` element does not change the centered part. -/
@[simp]
theorem center_add_const (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) (c : ℝ) :
    center μ (f + const μ c) = center μ f := by
  rw [center_add, center_const, add_zero]

/-- Adding a constant on the left does not change the centered part. -/
@[simp]
theorem center_const_add (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (const μ c + f) = center μ f := by
  rw [center_add, center_const, zero_add]

/-- A centered `L²` element has mean zero. -/
@[simp]
theorem mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]

/-- Centering is idempotent. -/
@[simp]
theorem center_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (center μ f) = center μ f := by
  simp [center]

/-- The variance of `f ∈ L²(μ)` is the squared `L²` norm of its centered part. -/
def variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) : NNReal :=
  ‖center μ f‖₊ ^ 2

/-- The mean is continuous in the real `L²` topology. -/
theorem continuous_mean (μ : ProbabilityMeasure α) : Continuous (mean μ) :=
  continuous_id.inner continuous_const

/-- Subtracting the mean is continuous in the real `L²` topology. -/
theorem continuous_center (μ : ProbabilityMeasure α) : Continuous (center μ) := by
  apply (continuous_id.sub ((continuous_mean μ).smul continuous_const) :
    Continuous (fun f : Lp ℝ 2 (μ : Measure α) ↦ f - mean μ f • const μ 1)).congr
  intro f
  simp only [center, ← const_smul, mul_one]
  rfl

/-- Variance is continuous in `L²`, including at constant functions. -/
theorem continuous_variance (μ : ProbabilityMeasure α) : Continuous (variance μ) :=
  (continuous_center μ).nnnorm.pow 2

/-- Coercing the `NNReal` variance to `ℝ` gives the squared norm of the centered part. -/
@[simp, norm_cast]
theorem coe_variance (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ‖center μ f‖ ^ 2 := by
  rfl

/-- Variance is nonnegative after coercion to the reals. -/
theorem variance_nonneg (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    0 ≤ (variance μ f : ℝ) :=
  NNReal.zero_le_coe

/-- The zero element has zero variance. -/
@[simp]
theorem variance_zero (μ : ProbabilityMeasure α) : variance μ 0 = 0 := by
  simp [variance]

/-- Every constant `L²` element has zero variance. -/
@[simp]
theorem variance_const (μ : ProbabilityMeasure α) (c : ℝ) : variance μ (const μ c) = 0 := by
  simp [variance]

/-- Adding a constant `L²` element does not change variance. -/
@[simp]
theorem variance_add_const (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) (c : ℝ) :
    variance μ (f + const μ c) = variance μ f := by
  simp [variance]

/-- Adding a constant on the left does not change variance. -/
@[simp]
theorem variance_const_add (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ (const μ c + f) = variance μ f := by
  simp [variance]

/-- Centering does not change variance. -/
@[simp]
theorem variance_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ (center μ f) = variance μ f := by
  simp [variance]

/-- Variance vanishes exactly when the element equals its mean as a constant `L²` element. -/
theorem variance_eq_zero_iff (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ f = 0 ↔ f = const μ (mean μ f) := by
  simp [variance, center, sub_eq_zero]

/-- Scaling an `L²` element scales its variance by the squared nonnegative norm of the scalar. -/
theorem variance_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    variance μ (c • f) = ‖c‖₊ ^ 2 * variance μ f := by
  rw [variance, center_smul, nnnorm_smul, mul_pow]
  rfl

/-- On a subsingleton carrier every `L²` element is a constant element, hence has zero variance.
The probability law forces the carrier to be nonempty. -/
theorem variance_eq_zero_of_subsingleton [Subsingleton α] (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) : variance μ f = 0 := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (μ : Measure α)
  have hf : f = const μ (f x₀) := by
    apply Lp.ext
    filter_upwards [const_coeFn μ (f x₀)] with x hx
    rw [hx]
    exact congrArg f (Subsingleton.elim x x₀)
  rw [hf, variance_const]

/-- The intrinsic `L²` variance agrees, after coercion, with Mathlib's variance of the
representative supplied by the `Lp` element. -/
theorem coe_variance_eq_pointwise (μ : ProbabilityMeasure α)
    (f : Lp ℝ 2 (μ : Measure α)) :
    (variance μ f : ℝ) = ProbabilityTheory.variance f (μ : Measure α) := by
  rw [coe_variance, ← real_inner_self_eq_norm_sq (center μ f),
    MeasureTheory.L2.inner_def,
    ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  apply integral_congr_ae
  filter_upwards [center_coeFn μ f] with x hx
  rw [hx, mean_eq_integral]
  simp [Real.norm_eq_abs]

/-- Taking the mean commutes with embedding a pointwise square-integrable function into `L²`. -/
theorem mean_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    mean μ (hf.toLp f) = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean_eq_integral]
  exact integral_congr_ae hf.coeFn_toLp

/-- The `NNReal` variance of a pointwise square-integrable function is Mathlib's real variance
converted to `NNReal`; no information is lost because pointwise variance is nonnegative. -/
theorem variance_toLp (μ : ProbabilityMeasure α) {f : α → ℝ}
    (hf : MemLp f 2 (μ : Measure α)) :
    variance μ (hf.toLp f) =
      (ProbabilityTheory.variance f (μ : Measure α)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg f (μ : Measure α))]
  exact (coe_variance_eq_pointwise μ (hf.toLp f)).trans
    (ProbabilityTheory.variance_congr hf.coeFn_toLp)

end FunctionalInequalities.L2

namespace FunctionalInequalities.L2

section NormSquare

variable {V : Type*} [MeasurableSpace V]

/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

end NormSquare

end FunctionalInequalities.L2
