module

public import OAI.Analysis.KLS.Model
public import KLSOpenAI.Target

/-!
# Palomar solution: the dimension-free KLS bound

The proved `KLSOpenAI.kls : OAI.LeanBlast.KLS.KLSStatement` and
`KLSOpenAI.kls_locallyLipschitz : KLSOpenAI.LocallyLipschitzStatement` come from
`integrations/openai/KLSOpenAI/Target.lean`. Both are obtained from this repository's closed
covariance-normalized theorem `FunctionalInequalities.KLS.kls` (the Bizeul–Klartag–Lehec
cutoff route in `formalization/`), through the density bridges `KLSOpenAI.of_conjecture` and
`KLSOpenAI.locallyLipschitz_of_conjecture`. The OpenAI model definitions come from
`integrations/openai/OAI/Analysis/KLS/Model.lean` and the locally Lipschitz definitions from
`integrations/openai/KLSOpenAI/LocallyLipschitz.lean`; Comparator checks their bodies against
those of `Challenge.lean`.
This module declares nothing itself.
-/
