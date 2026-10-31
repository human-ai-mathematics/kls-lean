module

public import FunctionalInequalities.Probability.Gaussian.CharacteristicFunction
public import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
public import FunctionalInequalities.Poincare.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Smooth-test Poincaré inequality for the standard multivariate Gaussian

The standard Gaussian is the orthonormal image of the finite product of
one-dimensional standard Gaussians. The empty product covers dimension zero.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare.SmoothTest

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

section GaussianConstants

omit [SecondCountableTopology V]
/-- Every finite-dimensional standard Gaussian satisfies the smooth-test
Poincaré inequality with constant one, including dimension zero. -/
theorem holds_stdGaussian : Holds (stdGaussian V) 1 := by
  let ι := Fin (Module.finrank ℝ V)
  let E : ι → Type := fun _ => ℝ
  let μ : ∀ i : ι, Measure (E i) := fun _ => gaussianReal 0 1
  have hpi : Holds (piMeasure μ) 1 := by
    have h := Holds.pi (μ := μ) (C := fun _ => (1 : NNReal))
      (fun _ => holds_gaussianReal 0 1)
    apply h.mono
    exact_mod_cast (Finset.sup_le fun _ _ => le_refl (1 : NNReal))
  have heuc : Holds (stdGaussian (EuclideanSpace ℝ ι)) 1 := by
    simpa only [piMeasure, μ, E, map_pi_eq_stdGaussian] using hpi
  let e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] V := (stdOrthonormalBasis ℝ V).repr.symm
  have hmap := (holds_map_linearIsometryEquiv_iff e
    (stdGaussian (EuclideanSpace ℝ ι))).mpr heuc
  rw [stdGaussian_map e] at hmap
  exact hmap

/-- A scalar image of the standard Gaussian has constant at most the
squared scale, including zero scale and dimension zero. -/
theorem holds_stdGaussian_map_smul (r : ℝ) :
    Holds ((stdGaussian V).map (fun x : V => r • x)) (r ^ 2) := by
  simpa only [mul_one] using (holds_stdGaussian (V := V)).map_smul r

/-- The radial Gaussian law has smooth-test Poincaré constant `1/(2s)`, including dimension zero. -/
theorem holds_gaussianLaw {s : ℝ} (hs : 0 < s) :
    Holds (Probability.Gaussian.law (V := V) s) (1 / (2 * s)) := by
  rw [Probability.Gaussian.law_eq_scaled_stdGaussian hs]
  have h := Poincare.SmoothTest.holds_stdGaussian_map_smul (V := V)
    (Real.sqrt (2 * s))⁻¹
  have hsq : (Real.sqrt (2 * s))⁻¹ ^ 2 = 1 / (2 * s) := by
    rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * s)]
    ring
  rwa [hsq] at h


end GaussianConstants

end FunctionalInequalities.Poincare.SmoothTest
