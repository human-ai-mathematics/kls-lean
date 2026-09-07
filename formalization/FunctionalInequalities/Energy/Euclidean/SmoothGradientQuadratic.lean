import FunctionalInequalities.Energy.Euclidean.SmoothGradient
import FunctionalInequalities.Energy.QuadraticPreEnergy
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quadratic laws for the smooth-gradient pre-energy

The smooth-gradient tests are stable under the elementary real vector-space operations. Their
realizations in `L²(μ)` respect those operations, and their finite gradient energy satisfies
real quadratic homogeneity and the parallelogram identity.

Addition and subtraction use the Borel structure on the ambient Hilbert space. This hypothesis
is needed to turn continuity of the gradient into the measurability required by the integrability
argument. No closedness or density statement is made here.
-/

noncomputable section

open InnerProductSpace MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

namespace SmoothGradientTest

variable {mu : ProbabilityMeasure E}

/-- The gradient of a sum is the sum of the gradients. -/
theorem gradient_add (f g : SmoothGradientTest mu) (x : E) :
    gradient (f.toFun + g.toFun) x = gradient f.toFun x + gradient g.toFun x := by
  apply (toDual ℝ E).injective
  simpa only [toDual_gradient, map_add] using
    fderiv_add ((f.contDiff.differentiable (by simp)) x)
      ((g.contDiff.differentiable (by simp)) x)

/-- The gradient of a negated test is the negated gradient. -/
theorem gradient_neg (f : SmoothGradientTest mu) (x : E) :
    gradient (-f.toFun) x = -gradient f.toFun x := by
  apply (toDual ℝ E).injective
  simp only [toDual_gradient, map_neg, fderiv_neg]

/-- The gradient of a difference is the difference of the gradients. -/
theorem gradient_sub (f g : SmoothGradientTest mu) (x : E) :
    gradient (f.toFun - g.toFun) x = gradient f.toFun x - gradient g.toFun x := by
  apply (toDual ℝ E).injective
  simpa only [toDual_gradient, map_sub] using
    fderiv_sub ((f.contDiff.differentiable (by simp)) x)
      ((g.contDiff.differentiable (by simp)) x)

/-- The gradient commutes with real scalar multiplication. -/
theorem gradient_smul (c : ℝ) (f : SmoothGradientTest mu) (x : E) :
    gradient (c • f.toFun) x = c • gradient f.toFun x := by
  apply (toDual ℝ E).injective
  simpa only [toDual_gradient, map_smul] using
    fderiv_const_smul ((f.contDiff.differentiable (by simp)) x) c

omit [MeasurableSpace E] in
private theorem continuous_gradient_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (gradient f) := by
  change Continuous (fun x ↦ (toDual ℝ E).symm (fderiv ℝ f x))
  exact (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by simp))

private theorem gradientSq_add_integrable [BorelSpace E]
    (f g : SmoothGradientTest mu) :
    Integrable (fun x ↦ ‖gradient (f.toFun + g.toFun) x‖ ^ 2) (mu : Measure E) := by
  refine ((f.gradient_sq_integrable.add g.gradient_sq_integrable).const_mul 2).mono' ?_ ?_
  · exact
      ((continuous_gradient_of_contDiff (f.contDiff.add g.contDiff)).norm.pow 2)
        |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), gradient_add]
    change ‖gradient f.toFun x + gradient g.toFun x‖ ^ 2 ≤
      2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2)
    calc
      ‖gradient f.toFun x + gradient g.toFun x‖ ^ 2 ≤
          (‖gradient f.toFun x‖ + ‖gradient g.toFun x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_add_le _ _)
      _ ≤ 2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2) := add_sq_le

private theorem gradientSq_sub_integrable [BorelSpace E]
    (f g : SmoothGradientTest mu) :
    Integrable (fun x ↦ ‖gradient (f.toFun - g.toFun) x‖ ^ 2) (mu : Measure E) := by
  refine ((f.gradient_sq_integrable.add g.gradient_sq_integrable).const_mul 2).mono' ?_ ?_
  · exact
      ((continuous_gradient_of_contDiff (f.contDiff.sub g.contDiff)).norm.pow 2)
        |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), gradient_sub]
    change ‖gradient f.toFun x - gradient g.toFun x‖ ^ 2 ≤
      2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2)
    calc
      ‖gradient f.toFun x - gradient g.toFun x‖ ^ 2 ≤
          (‖gradient f.toFun x‖ + ‖gradient g.toFun x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_sub_le _ _)
      _ ≤ 2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2) := add_sq_le

/-- The zero smooth-gradient test. -/
def zero (mu : ProbabilityMeasure E) : SmoothGradientTest mu where
  toFun := 0
  contDiff := contDiff_const
  memLp_two := MemLp.zero
  gradient_sq_integrable := by
    change Integrable (fun x ↦ ‖gradient (fun _ : E ↦ (0 : ℝ)) x‖ ^ 2) (mu : Measure E)
    have hzero : (fun x ↦ ‖gradient (fun _ : E ↦ (0 : ℝ)) x‖ ^ 2) = (0 : E → ℝ) := by
      funext x
      simp only [gradient_fun_const, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Pi.zero_apply]
    rw [hzero]
    exact integrable_zero E ℝ (mu : Measure E)

/-- The sum of two smooth-gradient tests. -/
def add [BorelSpace E] (f g : SmoothGradientTest mu) : SmoothGradientTest mu where
  toFun := f.toFun + g.toFun
  contDiff := f.contDiff.add g.contDiff
  memLp_two := f.memLp_two.add g.memLp_two
  gradient_sq_integrable := gradientSq_add_integrable f g

/-- The additive inverse of a smooth-gradient test. -/
def neg (f : SmoothGradientTest mu) : SmoothGradientTest mu where
  toFun := -f.toFun
  contDiff := f.contDiff.neg
  memLp_two := f.memLp_two.neg
  gradient_sq_integrable := by
    simpa only [gradient_neg, norm_neg] using f.gradient_sq_integrable

/-- The difference of two smooth-gradient tests. -/
def sub [BorelSpace E] (f g : SmoothGradientTest mu) : SmoothGradientTest mu where
  toFun := f.toFun - g.toFun
  contDiff := f.contDiff.sub g.contDiff
  memLp_two := f.memLp_two.sub g.memLp_two
  gradient_sq_integrable := gradientSq_sub_integrable f g

/-- Real scalar multiplication of a smooth-gradient test. -/
def smul (c : ℝ) (f : SmoothGradientTest mu) : SmoothGradientTest mu where
  toFun := c • f.toFun
  contDiff := f.contDiff.const_smul c
  memLp_two := f.memLp_two.const_smul c
  gradient_sq_integrable := by
    simpa only [gradient_smul, norm_smul, mul_pow] using
      f.gradient_sq_integrable.const_mul (‖c‖ ^ 2)

/-- Smooth-gradient tests are determined by their underlying functions. -/
@[ext]
theorem ext {f g : SmoothGradientTest mu} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The underlying-function map on smooth-gradient tests is injective. -/
theorem toFun_injective : Function.Injective
    (SmoothGradientTest.toFun : SmoothGradientTest mu → E → ℝ) :=
  fun _ _ ↦ ext

instance : Zero (SmoothGradientTest mu) :=
  ⟨zero mu⟩

instance [BorelSpace E] : Add (SmoothGradientTest mu) :=
  ⟨add⟩

instance : Neg (SmoothGradientTest mu) :=
  ⟨neg⟩

instance [BorelSpace E] : Sub (SmoothGradientTest mu) :=
  ⟨sub⟩

instance [BorelSpace E] : SMul ℕ (SmoothGradientTest mu) :=
  ⟨fun n f ↦ smul (n : ℝ) f⟩

instance [BorelSpace E] : SMul ℤ (SmoothGradientTest mu) :=
  ⟨fun n f ↦ smul (n : ℝ) f⟩

instance : SMul ℝ (SmoothGradientTest mu) :=
  ⟨smul⟩

instance instAddCommGroup [BorelSpace E] : AddCommGroup (SmoothGradientTest mu) :=
  Function.Injective.addCommGroup SmoothGradientTest.toFun toFun_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun f n ↦ by
      funext x
      change (n : ℝ) * f.toFun x = n • f.toFun x
      simp)
    (fun f n ↦ by
      funext x
      change (n : ℝ) * f.toFun x = n • f.toFun x
      simp)

/-- The underlying-function map as an additive homomorphism. -/
def toFunAddMonoidHom [BorelSpace E] : SmoothGradientTest mu →+ E → ℝ where
  toFun := SmoothGradientTest.toFun
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule [BorelSpace E] : Module ℝ (SmoothGradientTest mu) :=
  Function.Injective.module ℝ toFunAddMonoidHom toFun_injective (fun _ _ ↦ rfl)

/-- The zero test realizes the zero element of `L²(μ)`. -/
@[simp]
theorem toL2_zero (mu : ProbabilityMeasure E) :
    (0 : SmoothGradientTest mu).toL2 = 0 := by
  change (zero mu).toL2 = 0
  simpa only [toL2, zero] using
    (MemLp.zero (p := (2 : ENNReal)) (μ := (mu : Measure E)) (ε := ℝ)).toLp_zero

/-- Realization in `L²(μ)` preserves addition. -/
@[simp]
theorem toL2_add [BorelSpace E] (f g : SmoothGradientTest mu) :
    (f + g).toL2 = f.toL2 + g.toL2 := by
  change (add f g).toL2 = f.toL2 + g.toL2
  simpa only [toL2, add] using f.memLp_two.toLp_add g.memLp_two

/-- Realization in `L²(μ)` preserves additive inverses. -/
@[simp]
theorem toL2_neg (f : SmoothGradientTest mu) :
    (-f).toL2 = -f.toL2 := by
  change (neg f).toL2 = -f.toL2
  simpa only [toL2, neg] using f.memLp_two.toLp_neg

/-- Realization in `L²(μ)` preserves subtraction. -/
@[simp]
theorem toL2_sub [BorelSpace E] (f g : SmoothGradientTest mu) :
    (f - g).toL2 = f.toL2 - g.toL2 := by
  change (sub f g).toL2 = f.toL2 - g.toL2
  simpa only [toL2, sub] using f.memLp_two.toLp_sub g.memLp_two

/-- Realization in `L²(μ)` preserves real scalar multiplication. -/
@[simp]
theorem toL2_smul (c : ℝ) (f : SmoothGradientTest mu) :
    (c • f).toL2 = c • f.toL2 := by
  change (smul c f).toL2 = c • f.toL2
  simpa only [toL2, smul] using f.memLp_two.toLp_const_smul c

/-- The zero test has zero gradient energy. -/
@[simp]
theorem gradientEnergy_zero (mu : ProbabilityMeasure E) :
    (0 : SmoothGradientTest mu).gradientEnergy = 0 := by
  change (zero mu).gradientEnergy = 0
  apply NNReal.eq
  change ∫ x, ‖gradient (fun _ : E ↦ (0 : ℝ)) x‖ ^ 2 ∂(mu : Measure E) = 0
  simp only [gradient_fun_const, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, integral_zero]

/-- Gradient energy is homogeneous of degree two under real scaling. -/
theorem gradientEnergy_smul (c : ℝ) (f : SmoothGradientTest mu) :
    (c • f).gradientEnergy = ‖c‖₊ ^ 2 * f.gradientEnergy := by
  change (smul c f).gradientEnergy = ‖c‖₊ ^ 2 * f.gradientEnergy
  apply NNReal.eq
  simp only [coe_gradientEnergy, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, smul,
    gradient_smul, norm_smul, mul_pow, integral_const_mul]

/-- Gradient energy satisfies the parallelogram identity on smooth tests. -/
theorem gradientEnergy_parallelogram [BorelSpace E] (f g : SmoothGradientTest mu) :
    (f + g).gradientEnergy + (f - g).gradientEnergy =
      2 * f.gradientEnergy + 2 * g.gradientEnergy := by
  change
    (add f g).gradientEnergy + (sub f g).gradientEnergy =
      2 * f.gradientEnergy + 2 * g.gradientEnergy
  apply NNReal.eq
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, coe_gradientEnergy]
  change
    (∫ x, ‖gradient (f.toFun + g.toFun) x‖ ^ 2 ∂(mu : Measure E)) +
        ∫ x, ‖gradient (f.toFun - g.toFun) x‖ ^ 2 ∂(mu : Measure E) =
      2 * (∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(mu : Measure E)) +
        2 * ∫ x, ‖gradient g.toFun x‖ ^ 2 ∂(mu : Measure E)
  rw [← integral_add (gradientSq_add_integrable f g) (gradientSq_sub_integrable f g)]
  conv_lhs =>
    enter [2, x]
    rw [gradient_add, gradient_sub, parallelogram_law_with_norm ℝ]
  rw [integral_const_mul, integral_add f.gradient_sq_integrable g.gradient_sq_integrable]
  ring

end SmoothGradientTest

private instance smoothGradientPreEnergyTestAddCommGroup
    (mu : ProbabilityMeasure E) [FiniteDimensional ℝ E] [BorelSpace E]
    [SecondCountableTopology E] : AddCommGroup (smoothGradientPreEnergy mu).Test := by
  change AddCommGroup (SmoothGradientTest mu)
  infer_instance

private instance smoothGradientPreEnergyTestModule
    (mu : ProbabilityMeasure E) [FiniteDimensional ℝ E] [BorelSpace E]
    [SecondCountableTopology E] : Module ℝ (smoothGradientPreEnergy mu).Test := by
  change Module ℝ (SmoothGradientTest mu)
  infer_instance

/-- The smooth-gradient pre-energy is a quadratic finite pre-energy.

This result concerns only the concrete smooth tests. It does not assert that the sequential
relaxation is closed quadratic, or that relaxation agrees with the original energy on tests.
-/
theorem smoothGradientPreEnergy_quadratic (mu : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] :
    (smoothGradientPreEnergy mu).Quadratic where
  map_zero := by
    change (SmoothGradientTest.zero mu).toL2 = 0
    exact SmoothGradientTest.toL2_zero mu
  map_add f g := by
    change (SmoothGradientTest.add f g).toL2 = f.toL2 + g.toL2
    exact SmoothGradientTest.toL2_add f g
  map_smul c f := by
    change (SmoothGradientTest.smul c f).toL2 = c • f.toL2
    exact SmoothGradientTest.toL2_smul c f
  energy_zero := by
    change (SmoothGradientTest.zero mu).gradientEnergy = 0
    exact SmoothGradientTest.gradientEnergy_zero mu
  energy_smul c f := by
    change (SmoothGradientTest.smul c f).gradientEnergy = ‖c‖₊ ^ 2 * f.gradientEnergy
    exact SmoothGradientTest.gradientEnergy_smul c f
  parallelogram f g := by
    change
      (SmoothGradientTest.add f g).gradientEnergy +
          (SmoothGradientTest.sub f g).gradientEnergy =
        2 * f.gradientEnergy + 2 * g.gradientEnergy
    exact SmoothGradientTest.gradientEnergy_parallelogram f g

end FunctionalInequalities.Energy.Euclidean
