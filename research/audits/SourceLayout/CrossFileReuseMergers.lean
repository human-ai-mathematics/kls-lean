import Lean
import FunctionalInequalities.Analysis.MetricBV.Scaling
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
import FunctionalInequalities.Probability.Posterior.Generator
import FunctionalInequalities.Probability.Posterior.LogPartition
import FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.LogConcave.Line.Buser

/-! All modules that held the private copies use the existing public producers; the six duplicate
private names are absent and the existing application entry points remain.
The isometric thickening identity needs only pseudo-extended-metric spaces. -/
set_option maxHeartbeats 0 in
run_cmd do
  let removed : Array String := #[
    "_private.FunctionalInequalities.Analysis.BakryEmery.Calculus.0.FunctionalInequalities.Analysis.BakryEmery.line_deriv",
    "_private.FunctionalInequalities.Probability.Posterior.Generator.0.FunctionalInequalities.Probability.Posterior.line_hasDerivAt",
    "_private.FunctionalInequalities.Probability.Posterior.LogPartition.0.FunctionalInequalities.Probability.Posterior.line_hasDerivAt",
    "_private.FunctionalInequalities.Analysis.MetricBV.Scaling.0.FunctionalInequalities.KLS.MetricBV.liminf_coe_mul",
    "_private.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary.0.FunctionalInequalities.KLS.BKL.Localization.measurable_path_uncurry",
    "_private.FunctionalInequalities.KLS.Geometry.Cheeger.Equality.0.FunctionalInequalities.KLS.Isoperimetry.thickening_preimage_of_isometry"]
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if removed.contains name.toString then
      throwError "Removed private duplicate survives: {name}"

set_option autoImplicit false
open FunctionalInequalities

namespace SourceLayout

theorem thickening_preimage_contract {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] {f : α → β} (hf : Isometry f) (hsurj : Function.Surjective f)
    (r : ℝ) (B : Set β) :
    Metric.thickening r (f ⁻¹' B) = f ⁻¹' Metric.thickening r B :=
  KLS.Isoperimetry.thickening_preimage_isometry hf hsurj r B

#print axioms thickening_preimage_contract

end SourceLayout

#check @FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measurable_uncurry_path
#check @FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le
#check @FunctionalInequalities.KLS.MetricBV.perimeter_smul_le
#check @FunctionalInequalities.Probability.Posterior.fderiv_posteriorExpectation_c_apply
#check @FunctionalInequalities.Probability.Posterior.fderiv_logPartition_c_apply
#check @FunctionalInequalities.KLS.Isoperimetry.constant_eq_minkowskiConstant_intrinsic
#check @FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_map
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasDerivAt_line
#print axioms FunctionalInequalities.KLS.Isoperimetry.thickening_preimage_isometry
