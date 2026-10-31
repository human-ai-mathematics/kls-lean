module

public import Lean
public import FunctionalInequalities.Analysis.Convex.Gradient.Image
public import FunctionalInequalities.KLS.LogConcave.Regular.Isotropic
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Temperate
public import FunctionalInequalities.L2.Components
meta import Lean
import all FunctionalInequalities.Analysis.Convex.Gradient.Image
import all FunctionalInequalities.KLS.LogConcave.Regular.Isotropic
import all FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Temperate
import all FunctionalInequalities.L2.Components

/-! All modules that held the private copies import the common producers; the four duplicate
private names are absent and the existing application entry points remain. -/

@[expose] public section
set_option maxHeartbeats 0 in
run_cmd do
  let removed : Array String := #[
    "_private.FunctionalInequalities.Analysis.Convex.Gradient.Image.0.FunctionalInequalities.Analysis.gradient_increment",
    "_private.FunctionalInequalities.KLS.LogConcave.Regular.Isotropic.0.FunctionalInequalities.KLS.RegularPotential.memLp_two_translate",
    "_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Temperate.0.FunctionalInequalities.KLS.LogConcave.norm_sq_Lp_eq_integral",
    "_private.FunctionalInequalities.L2.Components.0.FunctionalInequalities.L2.norm_sq_eq_integral_norm_sq"]
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if removed.contains name.toString then
      throwError "Removed private duplicate survives: {name}"

#check @FunctionalInequalities.Analysis.mem_range_gradient_iff_tilt_min
#check @FunctionalInequalities.KLS.RegularPotential.isotropic_comp_affine_of_whitening
#check @FunctionalInequalities.KLS.LogConcave.integral_sq_sub_integral_le_of_hasTemperateGrowth
#check @FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL
#print axioms FunctionalInequalities.L2.norm_sq_eq_integral_norm_sq
