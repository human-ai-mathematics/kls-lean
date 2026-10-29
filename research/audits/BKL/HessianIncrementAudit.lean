import FunctionalInequalities.Analysis.Convex.SecondOrder.HessianIncrement
import Lean
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-! Audit client for the integrated Hessian-increment energy support of the weak Letwin route
(Letwin arXiv:2607.24164v1, toward Theorem 2.5): centered second-difference regularity and bounds
(`Analysis/Convex/SecondOrder/Difference.lean`), total coordinate Hessian-entry measurability and
the Lipschitz-gradient entry bound (`Probability/Stein/HessianKernel.lean`), weak generator
integrability (`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`) and the weighted
increment integrability with the original integrated energy estimate
(`Analysis/Convex/SecondOrder/HessianIncrement.lean`). Each section restates the exact library
statement and consumes it in an actual client, including the integrable uniform
difference-quotient bound. Canonical imports only. -/

noncomputable section

section CenteredDifferenceRegularity

open MeasureTheory
open FunctionalInequalities.Probability.Stein FunctionalInequalities.Analysis
open scoped RealInnerProductSpace

namespace HessianIncrementAudit.CenteredDifferenceRegularity

theorem exact_statement {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) ∧
      LipschitzWith (4 * G)
        (gradient (fun x => u (x + h) + u (x - h) - 2 * u x)) := by
  exact centeredDifference_contDiff_lipschitz_gradient hu hG h

theorem actual_centered_difference_generator_symmetry {n : ℕ}
    {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) {LF : NNReal}
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) :
    ∫ x, η x * (((hessianMatrix u x)⁻¹ *
          hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x).trace -
        fderiv ℝ V (gradient u x)
          (gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
    ∫ x, (u (x + h) + u (x - h) - 2 * u x) *
        (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨hw, hGw⟩ := centeredDifference_contDiff_lipschitz_gradient hu hG h
  exact (integral_mul_generator_eq_neg_energy hu hG hV hF hdet hw hGw hη hηc).trans
    (integral_mul_generator_eq_neg_energy' hu hG hV hF hdet hw hGw hη hηc).symm

end HessianIncrementAudit.CenteredDifferenceRegularity

end CenteredDifferenceRegularity

section CenteredDifferenceBounds

open Set
open FunctionalInequalities.Analysis

namespace HessianIncrementAudit.CenteredDifferenceBounds

theorem weighted_scalar_upper {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
    {D : ℝ} (h : EuclideanSpace ℝ (Fin n))
    (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (a : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∀ x, (u (x + h) + u (x - h) - 2 * u x) * a x ≤
      (D * ‖h‖ ^ 2) * |a x| := by
  have hb := centeredDifference_nonneg_le hconv h hw
  intro x
  exact (mul_le_mul_of_nonneg_left (le_abs_self (a x)) (hb.1 x).1).trans
    (mul_le_mul_of_nonneg_right (hb.1 x).2 (abs_nonneg (a x)))

end HessianIncrementAudit.CenteredDifferenceBounds

end CenteredDifferenceBounds

section HessianEntryBounds

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

namespace HessianIncrementAudit.HessianEntryBounds

theorem inverse_times_test_hessian_integrable {n : ℕ}
    {u F w f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G Gw : NNReal} (hG : LipschitzWith G (gradient u))
    (hGw : LipschitzWith Gw (gradient w)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hf : Continuous f) (hfc : HasCompactSupport f) (i j k l : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j *
      (hessianMatrix w x k l * f x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf
  apply integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet
    ((measurable_hessianMatrix_entry w k l).mul hf.measurable)
    (hfc.mul_left : HasCompactSupport (fun x => hessianMatrix w x k l * f x))
    (C := (Gw : ℝ) * C)
  intro x
  change ‖hessianMatrix w x k l * f x‖ ≤ (Gw : ℝ) * C
  rw [norm_mul]
  exact mul_le_mul (norm_hessianMatrix_entry_le_of_lipschitz_gradient hGw x k l)
    (hC x) (norm_nonneg _) Gw.coe_nonneg

theorem actual_weighted_generator_trace_entry_integrable {n : ℕ}
    {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G Gw LF : NNReal}
    (hG : LipschitzWith G (gradient u)) (hGw : LipschitzWith Gw (gradient w))
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (i j k l : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j *
      (hessianMatrix w x k l * (η x * Real.exp (-u x))))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact inverse_times_test_hessian_integrable hG hGw hF.continuous hdet
    (hη.continuous.mul (Real.continuous_exp.comp hu.continuous.neg))
    (hηc.mul_right : HasCompactSupport (fun x => η x * Real.exp (-u x))) i j k l

end HessianIncrementAudit.HessianEntryBounds

end HessianEntryBounds

section IncrementEnergyIntegrability

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

namespace HessianIncrementAudit.IncrementEnergyIntegrability

/-- The exact rescaled density needed when integrating the canonical pointwise increment
coercivity, using the original `C¹`/`C²` inputs. -/
theorem integrable_original_increment_coercivity_density {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) (K : ℝ) :
    Integrable (fun x =>
      (η x *
        ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
         ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) *
        Real.exp (-u x)) / (2 * K ^ 2))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact (integrable_hessian_increment_energy hu.continuous hG
    hη.continuous hηc h).div_const (2 * K ^ 2)

end HessianIncrementAudit.IncrementEnergyIntegrability

end IncrementEnergyIntegrability

section GeneratorIntegrability

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

namespace HessianIncrementAudit.GeneratorIntegrability

/-- Derive the actual centered test and determinant input from the original
hypotheses, then consume all three genuine integrability outputs. -/
theorem original_centered_generator_integrability {n : ℕ}
    {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) {LF : NNReal}
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ}
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) :
    let w := fun x => u (x + h) + u (x - h) - 2 * u x
    Integrable (fun x => η x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => w x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x =>
      |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)) := by
    filter_upwards [hdata] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  obtain ⟨hw, hGw⟩ := centeredDifference_contDiff_lipschitz_gradient hu hG h
  exact integrable_weak_generator_densities hu.continuous hG hV hF.continuous
    hdet hw.continuous hGw hη hηc

end HessianIncrementAudit.GeneratorIntegrability

end GeneratorIntegrability

section IntegratedIncrementEnergy

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

namespace HessianIncrementAudit.IntegratedIncrementEnergy

/-- Actual integrability plus the uniform squared-difference-quotient bound
consumed by the next local L2 weak-derivative producer. -/
theorem integrable_and_uniform_difference_quotient_energy {n : ℕ} {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) {D : ℝ}
    (h : EuclideanSpace ℝ (Fin n)) (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hne : h ≠ 0) :
    Integrable (fun x => (η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
        ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)) / ‖h‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
        ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)) / ‖h‖ ^ 2
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      2 * K ^ 2 * D * ∫ x, |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  refine ⟨(integrable_hessian_increment_energy hu.continuous hG
    hη.continuous hηc h).div_const (‖h‖ ^ 2), ?_⟩
  have hh : 0 < ‖h‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  rw [integral_div]
  apply (div_le_iff₀ hh).2
  have hb := integral_mul_hessian_increment_le hu hconv hG hV hVc hF hK
    hdata hη hηc hη0 h hw
  calc
    _ ≤ 2 * K ^ 2 * (D * ‖h‖ ^ 2) *
      ∫ x, |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hb
    _ = _ := by ring

end HessianIncrementAudit.IntegratedIncrementEnergy

end IntegratedIncrementEnergy

run_cmd do
  let env ← Lean.getEnv
  for n in [`FunctionalInequalities.Analysis.measurable_hessianMatrix_entry,
      `FunctionalInequalities.Analysis.norm_hessianMatrix_entry_le_of_lipschitz_gradient] do
    if (env.find? n).isSome then throwError "Old scratch public name leaked: {n}"
  Lean.logInfo "NO_OLD_PUBLIC_ALIASES"

run_cmd do
  let env ← Lean.getEnv
  for (n, h) in [(`FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient, (265072094 : UInt64)),
      (`FunctionalInequalities.Analysis.centeredDifference_nonneg_le, 3239914189),
      (`FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry, 298734493),
      (`FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient, 1711842242),
      (`FunctionalInequalities.Analysis.integrable_hessian_increment_energy, 615525409),
      (`FunctionalInequalities.Analysis.integrable_weak_generator_densities, 1222551683),
      (`FunctionalInequalities.Analysis.integral_mul_hessian_increment_le, 211311595)] do
    let some ci := env.find? n | throwError "Missing frozen declaration: {n}"
    unless ci.levelParams.isEmpty && hash ci.type == h do
      throwError "Complete type changed: {n}"
  Lean.logInfo "FROZEN_COMPLETE_TYPES_MATCH"

#print axioms FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient
#print axioms HessianIncrementAudit.CenteredDifferenceRegularity.exact_statement
#print axioms HessianIncrementAudit.CenteredDifferenceRegularity.actual_centered_difference_generator_symmetry
#print axioms FunctionalInequalities.Analysis.centeredDifference_nonneg_le
#print axioms HessianIncrementAudit.CenteredDifferenceBounds.weighted_scalar_upper
#print axioms FunctionalInequalities.Probability.Stein.measurable_hessianMatrix_entry
#print axioms FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient
#print axioms HessianIncrementAudit.HessianEntryBounds.inverse_times_test_hessian_integrable
#print axioms HessianIncrementAudit.HessianEntryBounds.actual_weighted_generator_trace_entry_integrable
#print axioms FunctionalInequalities.Analysis.integrable_hessian_increment_energy
#print axioms HessianIncrementAudit.IncrementEnergyIntegrability.integrable_original_increment_coercivity_density
#print axioms FunctionalInequalities.Analysis.integrable_weak_generator_densities
#print axioms HessianIncrementAudit.GeneratorIntegrability.original_centered_generator_integrability
#print axioms FunctionalInequalities.Analysis.integral_mul_hessian_increment_le
#print axioms HessianIncrementAudit.IntegratedIncrementEnergy.integrable_and_uniform_difference_quotient_energy
