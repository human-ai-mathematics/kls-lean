module

public import KLSOpenAI.Bridge
public import KLSOpenAI.LocallyLipschitz
public import Lean
meta import Lean
@[expose] public section

run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    if name == `FunctionalInequalities.KLS.Target || name == `KLSOpenAI.Target then
      throwError "Bridge imports a closed KLS endpoint: {name}"
  if env.contains `FunctionalInequalities.KLS.kls then
    throwError "Bridge environment contains the closed theorem FunctionalInequalities.KLS.kls"
  Lean.logInfo "BRIDGE_BOUNDARY_OK: no closed KLS endpoint imported"
example : FunctionalInequalities.KLS.Conjecture → OAI.LeanBlast.KLS.KLSStatement :=
  KLSOpenAI.of_conjecture

example : FunctionalInequalities.KLS.Conjecture → KLSOpenAI.LocallyLipschitzStatement :=
  KLSOpenAI.locallyLipschitz_of_conjecture
