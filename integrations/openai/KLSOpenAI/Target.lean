module

public import KLSOpenAI.Bridge
public import FunctionalInequalities.KLS.Target

/-! # The pinned OpenAI KLS statement, proved through the existing KLS library -/

@[expose] public section

namespace KLSOpenAI

/-- The exact OpenAI `KLSStatement`, without additional hypotheses. -/
theorem kls : OAI.LeanBlast.KLS.KLSStatement :=
  of_conjecture FunctionalInequalities.KLS.kls

end KLSOpenAI
