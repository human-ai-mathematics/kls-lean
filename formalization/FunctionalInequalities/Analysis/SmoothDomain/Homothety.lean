module

public import FunctionalInequalities.Analysis.SmoothDomain.Basic

/-! # Weighted surface integrals under homotheties

The normalized measure scales on every measurable piece, not only on the full boundary.
No finiteness of the measure or integrability of the weight is assumed. -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace FunctionalInequalities.KLS
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Pushforward by the inverse dilation, for the normalized surface measure. -/
theorem map_inv_homothety_surfaceMeasure (a : V) {c : ℝ} (hc : c ≠ 0) :
    Measure.map (AffineMap.homothety a c⁻¹) (surfaceMeasure V) =
      (‖c‖₊ ^ ((Module.finrank ℝ V - 1 : ℕ) : ℝ) : ℝ≥0) • surfaceMeasure V := by
  unfold surfaceMeasure hausdorffNormalized
  rw [Measure.map_smul _ (AffineMap.homothety_continuous a c⁻¹).aemeasurable,
    map_homothety_hausdorffMeasure (by positivity) a (inv_ne_zero hc),
    nnnorm_inv, inv_inv, smul_comm]

/-- Change of variables on any measurable set for normalized surface measure. -/
theorem setLIntegral_image_homothety_surfaceMeasure (a : V) {c : ℝ} (hc : c ≠ 0) {S : Set V}
    (hS : MeasurableSet S) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q in AffineMap.homothety a c '' S, f q ∂(surfaceMeasure V) =
      (‖c‖₊ ^ ((Module.finrank ℝ V - 1 : ℕ) : ℝ) : ℝ≥0) •
        ∫⁻ y in S, f (AffineMap.homothety a c y) ∂(surfaceMeasure V) := by
  have h :=
    setLIntegral_map (μ := surfaceMeasure V) hS
      (hf.comp (AffineMap.homothety_continuous a c).measurable)
      (AffineMap.homothety_continuous a c⁻¹).measurable
  rw [map_inv_homothety_surfaceMeasure a hc, setLIntegral_smul_measure] at h
  have heq : AffineMap.homothety a c⁻¹ ⁻¹' S = AffineMap.homothety a c '' S :=
    ((SmoothDomain.homothetyHomeomorph a hc).image_eq_preimage_symm S).symm
  rw [heq] at h
  simpa only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, add_sub_cancel_right, one_smul,
    sub_add_cancel] using h.symm

namespace SmoothDomain
/--
Weighted boundary change of variables; the exponent uses natural subtraction in dimension zero. -/
theorem setLIntegral_frontier_homothety (U : SmoothDomain V) (a : V) {c : ℝ} (hc : c ≠ 0)
    {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q in frontier (U.homothety a hc).carrier, f q ∂(surfaceMeasure V) =
      (‖c‖₊ ^ ((Module.finrank ℝ V - 1 : ℕ) : ℝ) : ℝ≥0) •
        ∫⁻ y in frontier U.carrier, f (AffineMap.homothety a c y) ∂(surfaceMeasure V) := by
  rw [U.frontier_homothety]
  exact setLIntegral_image_homothety_surfaceMeasure a hc isClosed_frontier.measurableSet hf
end SmoothDomain
end FunctionalInequalities.KLS
