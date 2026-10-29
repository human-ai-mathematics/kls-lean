import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
import FunctionalInequalities.Analysis.Cutoff.Profile
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: Letwin Lemma A.4 operator continuity

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17): `Lχ_R` is measurable, hence in `L¹(ν)`
once dominated. Actual clients of `continuous_hessianInverseOperator`, every premise derived here:
- `continuous_profile_generator`: the generator of the actual rescaled profile `η((φ − c)/R)` is
  continuous, for every real `c`, `R` (the profile is smooth);
- `integrable_generator_mul_of_hasCompactSupport`: `L f · g` is integrable for continuous compactly
  supported `g` and any measure finite on compacts (the cutoff-product integrability used by
  Lemma A.5);
- `continuous_generator_self`: `L φ` itself is continuous (the self-generator of the energy
  identity).
These are not the Lemma A.4 producer or a source-law client.
-/

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace A4OperatorContinuityClient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The generator of the actual rescaled profile `η((φ − c)/R)` is continuous. -/
theorem continuous_profile_generator {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hRange : Set.range (gradient φ) ⊆ U) (c R : ℝ) :
    Continuous (hessianInverseOperator φ V (fun y => Real.smoothTransition (2 - (φ y - c) / R))) := by
  have hη := smoothTransition_two_sub_cutoff.1
  have hf : ContDiff ℝ 2 (fun y => Real.smoothTransition (2 - (φ y - c) / R)) :=
    (hη.of_le (WithTop.coe_le_coe.mpr le_top)).comp
      (((hφ.of_le (WithTop.coe_le_coe.mpr le_top)).sub contDiff_const).div_const R)
  exact continuous_hessianInverseOperator hφ hPD hU hV hRange hf

/-- `L f · g` is integrable for continuous compactly supported `g` (any measure finite on compacts). -/
theorem integrable_generator_mul_of_hasCompactSupport [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] {φ V f g : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hf : ContDiff ℝ 2 f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => hessianInverseOperator φ V f x * g x) μ :=
  ((continuous_hessianInverseOperator hφ hPD hU hV hRange hf).mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- `L φ` itself is continuous. -/
theorem continuous_generator_self {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hRange : Set.range (gradient φ) ⊆ U) :
    Continuous (hessianInverseOperator φ V φ) :=
  continuous_hessianInverseOperator hφ hPD hU hV hRange (hφ.of_le (WithTop.coe_le_coe.mpr le_top))

end A4OperatorContinuityClient

#print axioms FunctionalInequalities.Analysis.BakryEmery.continuous_hessianInverseOperator
#print axioms A4OperatorContinuityClient.continuous_profile_generator
#print axioms A4OperatorContinuityClient.integrable_generator_mul_of_hasCompactSupport
#print axioms A4OperatorContinuityClient.continuous_generator_self
