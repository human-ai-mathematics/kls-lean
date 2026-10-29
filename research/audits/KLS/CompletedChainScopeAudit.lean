import FunctionalInequalities.KLS.Target
import Lean

namespace CompletedChainScope

/-- The complete KLS producer requires no additional literature hypothesis. -/
theorem closed : FunctionalInequalities.KLS.Conjecture :=
  FunctionalInequalities.KLS.kls

#print axioms closed

run_cmd do
  let env ← Lean.getEnv
  for n in [`FunctionalInequalities.Analysis.Dirichlet.exists_unit_solution,
      `FunctionalInequalities.Analysis.Dirichlet.exists_unit_c1_solution,
      `FunctionalInequalities.Analysis.elliptic_operator_linear_combination] do
    if env.contains n then
      throwError "Deferred Letwin/CNS source entered the completed-chain dependency closure: {n}"

end CompletedChainScope
