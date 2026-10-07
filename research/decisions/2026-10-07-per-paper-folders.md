# 2026-10-07 per-paper folders (BKL)

Owner decision of 2026-10-07 (recorded in HANDOFF during the BKL Theorem 3.1 block): paper-specific
library modules and audit clients get per-paper folders; generic tools stay in their object
families. This batch changes only paths. Map:
[`2026-10-07-per-paper-folders-map.json`](../api-migration/2026-10-07-per-paper-folders-map.json).

## Placement plan

```text
Object and role:     BKL-specific constructions: the Poisson iterates of Section 3 and their lemmas
                     (PoissonIterate/, 8 modules), the finite-copy suspension of Proposition 7.1
                     (Suspension.lean), the Gaussian nonvacuity witness of Theorem 3.1
                     (GaussianTaylor.lean); the 19 BKL audit clients and route statements.
Destination:         formalization/FunctionalInequalities/KLS/BKL/ and research/audits/BKL/.
Namespaces:          unchanged (KLS.LogConcave.PoissonIterate, KLS.LogConcave.Suspension, KLS, …).
Imports:             unchanged edges; no object-family module imports KLS/BKL/.
Public API:          module paths only (11 modules, 19 audit files).
Validation:          lake build, strict audit compilation, research/verify.py.
```

## Left in place

- `Analysis/BakryEmery/TensorEnergy.lean` (BKL Lemma 3.4, Corollary 3.5 and Lemma 3.2 on `𝒜` for
  supplied iterates) is paper-specific, but `KLS/LogConcave/HeatSemigroup/Temperate.lean` imports it;
  moving it would make an object-family module import a per-paper module. Recorded as a candidate
  that first needs the BKL-specific part of `Temperate.lean` split off.
- Generic heat-model and tensor tools motivated by BKL stay in their families: `Regular.lean`
  (regular potentials), `HeatSemigroup/{Inverse,Temperate,Hessian,Tilt,ApproximateEigenfunction}.lean`,
  `Analysis/BakryEmery/Cumulant.lean`, `Analysis/Tensor/*`, `Analysis/DyadicSummation.lean`.
- `solutions/` stays flat (certificate layout); `solutions/ThmBklTaylorCriterion.lean` keeps its path.
- No Letwin or Song–Zhang folder is created until their first module exists.

Historical records (decisions, handoffs, migration maps, block reviews) keep their original paths.
