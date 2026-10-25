import FunctionalInequalities.Energy.SmoothGradient.Quadratic
import FunctionalInequalities.Energy.Form.Core
import FunctionalInequalities.Poincare.SmoothTest.Basic
import FunctionalInequalities.Probability.AffineSupport
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Ambient raw gradient energy sees normal derivatives

Source: Blueprint `obs:normal-direction-raw-energy`. Read `normalCoordinate`,
`normalCoordinate_ae_eq_zero`, `smoothTest_energy_normalCoordinate`, `Test.normalCoordinate`,
`Test.toL2_normalCoordinate` and `not_respectsAmbientFibers`.

Let the affine support `A = a + V` of `μ` be a proper affine subspace and let `n ∈ V^⊥` be a
unit vector. The coordinate `u x = ⟪n, x - a⟫` vanishes on `A`, hence is `0` in `L²(μ)`, while its
ambient gradient is the constant vector `n`, so its raw smooth-gradient energy is `1`. Consequently
the ambient smooth-gradient pre-energy does not respect realization fibers whenever the direction
space of the affine support is proper: raw ambient energy depends on the extension of a test
away from the affine support, even when the intrinsic law has a regular density.

This is an obstruction, not a ledger node: it records why the raw/core agreement question must be
posed intrinsically (or must quotient out normal derivatives) on proper affine supports.
-/

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ContDiff

namespace FunctionalInequalities.Energy.SmoothGradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The coordinate along a vector `n`, measured from the chosen support point. -/
def normalCoordinate (μ : ProbabilityMeasure E) (n : E) (x : E) : ℝ :=
  inner ℝ n (x - Probability.supportPoint μ)

variable (μ : ProbabilityMeasure E) (n : E)

omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem contDiff_normalCoordinate : ContDiff ℝ ∞ (normalCoordinate μ n) :=
  contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)

section NormalCoordinates

omit [BorelSpace E] [FiniteDimensional ℝ E]
/-- The coordinate has Fréchet derivative the dual of `n`. -/
theorem hasFDerivAt_normalCoordinate (x : E) :
    HasFDerivAt (normalCoordinate μ n) (toDual ℝ E n) x := by
  have h1 : HasFDerivAt (fun y : E ↦ y - Probability.supportPoint μ)
      (ContinuousLinearMap.id ℝ E) x := (hasFDerivAt_id x).sub_const _
  exact ((toDual ℝ E n).hasFDerivAt.comp x h1).congr_fderiv (ContinuousLinearMap.comp_id _)

/-- The gradient of the coordinate is the constant vector `n`. -/
theorem gradient_normalCoordinate (x : E) : gradient (normalCoordinate μ n) x = n := by
  apply (toDual ℝ E).injective
  rw [toDual_gradient, (hasFDerivAt_normalCoordinate μ n x).fderiv]

end NormalCoordinates

omit [CompleteSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The coordinate vanishes `μ`-almost everywhere when `n` is orthogonal to the direction of the
affine support. -/
theorem normalCoordinate_ae_eq_zero (hn : n ∈ (Probability.affineSupport μ).directionᗮ) :
    normalCoordinate μ n =ᵐ[(μ : Measure E)] 0 := by
  filter_upwards [Probability.ae_mem_affineSupport μ] with x hx
  show inner ℝ n (x - Probability.supportPoint μ) = 0
  rw [real_inner_comm]
  have ha : Probability.supportPoint μ ∈ Probability.affineSupport μ :=
    Probability.support_subset_affineSupport μ (Probability.supportPoint_mem_support μ)
  have hv : x - Probability.supportPoint μ ∈ (Probability.affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hx ha
  exact (Submodule.mem_orthogonal _ n).mp hn _ hv

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The raw smooth-test energy of the coordinate is `‖n‖²`. -/
theorem smoothTest_energy_normalCoordinate :
    Poincare.SmoothTest.energy (μ : Measure E) (normalCoordinate μ n) = ‖n‖ ^ 2 := by
  unfold Poincare.SmoothTest.energy
  simp [gradient_normalCoordinate]

/-- The coordinate as a smooth-gradient test: smooth, `L²` (it is almost everywhere zero), with
constant gradient. -/
def Test.normalCoordinate (hn : n ∈ (Probability.affineSupport μ).directionᗮ) : Test μ where
  toFun := SmoothGradient.normalCoordinate μ n
  contDiff := contDiff_normalCoordinate μ n
  memLp_two := MemLp.ae_eq (normalCoordinate_ae_eq_zero μ n hn).symm MemLp.zero
  gradient_sq_integrable := by
    simp only [gradient_normalCoordinate]
    exact integrable_const _

section NormalCoordinateTests

omit [BorelSpace E] [FiniteDimensional ℝ E]
/-- The `L²` class of the coordinate is zero. -/
theorem Test.toL2_normalCoordinate (hn : n ∈ (Probability.affineSupport μ).directionᗮ) :
    (Test.normalCoordinate μ n hn).toL2 = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact (Test.normalCoordinate μ n hn).toL2_coeFn.trans (normalCoordinate_ae_eq_zero μ n hn)

/-- The smooth-gradient energy of the coordinate is `‖n‖²`. -/
theorem Test.energy_normalCoordinate (hn : n ∈ (Probability.affineSupport μ).directionᗮ) :
    ((Test.normalCoordinate μ n hn).energy : ℝ) = ‖n‖ ^ 2 := by
  rw [Test.coe_energy]
  simp only [Test.normalCoordinate, gradient_normalCoordinate]
  simp

end NormalCoordinateTests

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A proper direction space has a unit normal vector. -/
theorem exists_unit_normal (h : (Probability.affineSupport μ).direction ≠ ⊤) :
    ∃ n : E, ‖n‖ = 1 ∧ n ∈ (Probability.affineSupport μ).directionᗮ := by
  have hne : (Probability.affineSupport μ).directionᗮ ≠ ⊥ := by
    intro hbot
    exact h (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨‖v‖⁻¹ • v, ?_, Submodule.smul_mem _ _ hv⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]

omit [BorelSpace E] in
/-- Blueprint `obs:normal-direction-raw-energy`: on a proper affine support there is a smooth
test that is zero in `L²(μ)` but has raw energy `1`. -/
theorem exists_test_toL2_eq_zero_energy_eq_one
    (h : (Probability.affineSupport μ).direction ≠ ⊤) :
    ∃ f : Test μ, f.toL2 = 0 ∧ (f.energy : ℝ) = 1 ∧
      Poincare.SmoothTest.energy (μ : Measure E) f.toFun = 1 := by
  obtain ⟨n, hn1, hn⟩ := exists_unit_normal μ h
  refine ⟨Test.normalCoordinate μ n hn, Test.toL2_normalCoordinate μ n hn, ?_, ?_⟩
  · rw [Test.energy_normalCoordinate, hn1, one_pow]
  · change Poincare.SmoothTest.energy (μ : Measure E) (normalCoordinate μ n) = 1
    rw [smoothTest_energy_normalCoordinate, hn1, one_pow]

/-- The ambient smooth-gradient pre-energy does not respect realization fibers on a proper affine
support: the zero test and the normal coordinate have the same `L²` class and energies `0` and
`1`. -/
theorem not_respectsAmbientFibers (h : (Probability.affineSupport μ).direction ≠ ⊤) :
    ¬ (preEnergy μ).RespectsAmbientFibers := by
  intro hres
  obtain ⟨f, hf0, hf1, -⟩ := exists_test_toL2_eq_zero_energy_eq_one μ h
  have hzero : (Test.zero μ).toL2 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    exact (Test.zero μ).toL2_coeFn
  have := hres f (Test.zero μ) (by rw [preEnergy_toAmbient, preEnergy_toAmbient, hf0, hzero])
  have hz : ((Test.zero μ).energy : ℝ) = 0 := by
    rw [Test.coe_energy]
    simp only [Test.zero]
    rw [show (0 : E → ℝ) = fun _ ↦ (0 : ℝ) from rfl, gradient_fun_const']
    simp
  have : ((preEnergy μ).energy f : ℝ) = ((preEnergy μ).energy (Test.zero μ) : ℝ) := by
    rw [this]
  rw [preEnergy_energy, preEnergy_energy, hf1, hz] at this
  exact one_ne_zero this

end FunctionalInequalities.Energy.SmoothGradient
