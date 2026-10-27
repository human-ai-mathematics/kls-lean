import FunctionalInequalities.Analysis.WaveSplitting.Basic

open FunctionalInequalities.Analysis.WaveSplitting

namespace StateExtensionalityAudit

/-- State extensionality requires no topology, norm or finite coordinate index. -/
theorem components {E ι : Type*} {X Y : State E ι}
    (hu : X.u = Y.u) (hv : X.v = Y.v) (hp : X.p = Y.p) : X = Y :=
  State.ext hu hv hp

#print axioms components
end StateExtensionalityAudit
