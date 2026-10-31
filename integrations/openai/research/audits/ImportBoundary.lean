module

public import KLSOpenAI.Bridge
public import Lean
meta import Lean
@[expose] public section

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name == `FunctionalInequalities.KLS.Target || name == `KLSOpenAI.Target then
      throwError "Bridge imports a closed KLS endpoint: {name}"
  Lean.logInfo "BRIDGE_BOUNDARY_OK: no closed KLS endpoint imported"
example : FunctionalInequalities.KLS.Conjecture → OAI.LeanBlast.KLS.KLSStatement :=
  KLSOpenAI.of_conjecture
