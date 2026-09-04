import FunctionalInequalities.Poincare.Gaussian.Real

/-!
# Lean certificate for `lem:poincare-gaussian-one-dimensional`

Status: proved / checked_by: lean. This entry point packages the two accepted conclusions in one
named certificate and retains checks of the supporting interfaces and concrete applications.
The imported mathematical declarations are fully proved and proof-placeholder-free.

Source: the one-dimensional Poincaré component of the
[Gaussian covariance family](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37).
The unchanged normalization comes from
[Definition 2.1](https://github.com/numina-functional-inequalities/kls-exploration/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25).
Arbitrary means, zero variance, the smooth L² finite-energy domain and the direct density
proof route are explicit local specifications. Each library declaration records its own source.

Read the certificate and two main interfaces first, then their density and interval/Tonelli
obligations. The applications below illustrate variance normalization and the Dirac boundary.
The certificate directly combines the reusable theorems without duplicating their proofs.
-/

set_option pp.universes true
set_option pp.funBinderTypes true
set_option format.width 100

open MeasureTheory ProbabilityTheory FunctionalInequalities

namespace Solutions.LemPoincareGaussianOneDimensional

/-! ## Certificate and main interfaces: valid constant and optimal constant -/

/-- The accepted one-dimensional Gaussian Poincaré claim: the variance is both a valid and the
optimal constant for every real mean and every nonnegative variance, including the Dirac case. -/
theorem certificate (m : ℝ) (v : NNReal) :
    Poincare.Holds (gaussianReal m v) (v : ℝ) ∧
      Poincare.constant (gaussianReal m v) = (v : ENNReal) := by
  exact ⟨Poincare.holds_gaussianReal m v, Poincare.constant_gaussianReal m v⟩

#check @certificate

#check @FunctionalInequalities.Poincare.holds_gaussianReal
#check @FunctionalInequalities.Poincare.constant_gaussianReal

/-! ## Density calculus and integrability interfaces -/

#check @FunctionalInequalities.Poincare.hasDerivAt_gaussianPDFReal
#check @FunctionalInequalities.Poincare.tendsto_gaussianPDFReal_atTop
#check @FunctionalInequalities.Poincare.tendsto_gaussianPDFReal_atBot
#check @FunctionalInequalities.Poincare.integrable_centered_gaussianPDFReal
#check @FunctionalInequalities.Poincare.integral_Ioi_centered_gaussianPDFReal
#check @FunctionalInequalities.Poincare.integral_Iio_centered_gaussianPDFReal
#check @FunctionalInequalities.Poincare.integrable_gaussianReal_iff

/-! ## Interval, Tonelli, admissibility and sharpness interfaces -/

#check @FunctionalInequalities.Poincare.interval_sq_sub_le_integral_sq_deriv
#check @FunctionalInequalities.Poincare.Admissible.variance_le_integral_sq_sub
#check @FunctionalInequalities.Poincare.Admissible.integrable_gaussianPDFReal_mul_sq_sub
#check @FunctionalInequalities.Poincare.Admissible.integrable_gaussianPDFReal_mul_sq_deriv
#check @FunctionalInequalities.Poincare.lintegral_gaussian_right_triangle
#check @FunctionalInequalities.Poincare.lintegral_gaussian_left_triangle
#check @FunctionalInequalities.Poincare.Admissible.integral_Ioi_sq_sub_gaussian_le
#check @FunctionalInequalities.Poincare.Admissible.integral_Iio_sq_sub_gaussian_le
#check @FunctionalInequalities.Poincare.Admissible.integral_sq_sub_gaussian_le
#check @FunctionalInequalities.Poincare.holds_gaussianReal_zero
#check @FunctionalInequalities.Poincare.Holds.gaussianReal_variance_le

/-! ## Typed applications of the proved interfaces -/

-- Standard Gaussian: variance one means Poincaré constant one.
#check (Poincare.holds_gaussianReal 0 1 : Poincare.Holds (gaussianReal 0 1) 1)
#check (Poincare.constant_gaussianReal 0 1 : Poincare.constant (gaussianReal 0 1) = 1)

-- Mean three, variance four: the constant is four, not the standard deviation two.
#check (Poincare.holds_gaussianReal 3 4 : Poincare.Holds (gaussianReal 3 4) 4)
#check (Poincare.constant_gaussianReal 3 4 : Poincare.constant (gaussianReal 3 4) = 4)

-- Zero variance is allowed for every mean in the same two main interfaces.
#check (fun (m : ℝ) ↦
  (Poincare.holds_gaussianReal m 0 : Poincare.Holds (gaussianReal m 0) 0))
#check (fun (m : ℝ) ↦
  (Poincare.constant_gaussianReal m 0 : Poincare.constant (gaussianReal m 0) = 0))

-- The existing Mathlib identity explains the law used in those boundary applications.
#check (fun (m : ℝ) ↦ (gaussianReal_zero_var m : gaussianReal m 0 = Measure.dirac m))

/-! ## Exact node proposition -/

#check (∀ (m : ℝ) (v : NNReal),
  Poincare.Holds (gaussianReal m v) (v : ℝ) ∧
    Poincare.constant (gaussianReal m v) = (v : ENNReal) : Prop)

end Solutions.LemPoincareGaussianOneDimensional
