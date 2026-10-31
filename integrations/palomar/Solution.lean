module

public import OAI.Analysis.KLS.Model
public import KLSOpenAI.Target

/-!
# Palomar solution: the dimension-free KLS bound

The proved `KLSOpenAI.kls : OAI.LeanBlast.KLS.KLSStatement` comes from
`integrations/openai/KLSOpenAI/Target.lean`, where it is obtained from this repository's closed
covariance-normalized theorem `FunctionalInequalities.KLS.kls` (the Bizeul–Klartag–Lehec
cutoff route in `formalization/`) through the density bridge `KLSOpenAI.of_conjecture`.
The OpenAI model definitions are imported from `integrations/openai/OAI/Analysis/KLS/Model.lean`,
whose bodies Comparator checks against those of `Challenge.lean`.
This module declares nothing itself.
-/
