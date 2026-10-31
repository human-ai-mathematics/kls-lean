module

public import FunctionalInequalities
public import Lean
meta import Lean

/-! Removed specializations and paper-local aliases are absent from the complete production
environment. -/

@[expose] public section
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[
      `FunctionalInequalities.Analysis.exists_contDiff_one_eqOn_ball,
      `FunctionalInequalities.Analysis.MorseSard.exists_contDiff_eventuallyEq_nat,
      `FunctionalInequalities.Analysis.BakryEmery.integrable_norm_pow_of_exp_cond,
      `FunctionalInequalities.Analysis.BakryEmery.norm_prod_inner_le_cond,
      `FunctionalInequalities.Analysis.BakryEmery.integrable_prod_inner_cond,
      `FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow,
      `FunctionalInequalities.KLS.LogConcave.Suspension.norm_sub_one_le_of_isPositive_mul_self,
      `FunctionalInequalities.KLS.LogConcave.Suspension.opNorm_le_of_inner_eq,
      `FunctionalInequalities.KLS.LogConcave.Suspension.inner_self_pos_of_norm_sub_one_lt,
      `FunctionalInequalities.KLS.LogConcave.Suspension.tendsto_inverseSqrt_one] do
    if env.contains name then throwError "Removed API survived as an alias: {name}"
