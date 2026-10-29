import Lean
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor
import FunctionalInequalities.Analysis.BakryEmery.TensorEnergy
import FunctionalInequalities.Analysis.Tensor.EnergyForm
import FunctionalInequalities.Energy.Cheeger.Basic
import FunctionalInequalities.KLS.BKL.Suspension.Derivatives
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation

/-! Removed private statements are absent with every module that held them imported.
Existing public energy and source-cumulant entry points remain available. -/

set_option maxHeartbeats 0 in
run_cmd do
  let removed : Array String := #[
    "_private.FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate.0.FunctionalInequalities.Analysis.BakryEmery.bochner_temperate_integrable",
    "_private.FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate.0.FunctionalInequalities.Analysis.BakryEmery.bochner_sq_temperate_integrable",
    "_private.FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate.0.FunctionalInequalities.Analysis.BakryEmery.bochner_le_temperate_integrable",
    "_private.FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor.0.FunctionalInequalities.Analysis.BakryEmery.tensorIBP_integrable",
    "_private.FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor.0.FunctionalInequalities.Analysis.BakryEmery.tensorEq_integrable",
    "_private.FunctionalInequalities.Analysis.BakryEmery.TensorEnergy.0.FunctionalInequalities.Analysis.BakryEmery.energyPyth_integrable",
    "_private.FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor.0.FunctionalInequalities.Analysis.BakryEmery.tensorCurv_gradient_inner",
    "_private.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation.0.FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.source_density_integrable",
    "_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.inverse_line_at_zero",
    "_private.FunctionalInequalities.Energy.Cheeger.Basic.0.FunctionalInequalities.Energy.SmoothGradient.Test.localSlope_energy_eq_coe_energy",
    "_private.FunctionalInequalities.KLS.BKL.Suspension.Derivatives.0.FunctionalInequalities.KLS.LogConcave.Suspension.source_mixed_cumulant_entries"]
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if removed.contains name.toString then
      throwError "Removed private duplicate survives: {name}"

#check @FunctionalInequalities.Energy.SmoothGradient.Test.localSlope_energy
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.localSlope_energy
#check @FunctionalInequalities.KLS.LogConcave.Suspension.cumulant_jointLaw_none_entries
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.cumulant_jointLaw_none_entries
