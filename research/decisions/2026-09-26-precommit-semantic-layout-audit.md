# Precommit semantic and layout audit

Date: 2026-09-26. Scope: the complete previously uncommitted proof and
metadata worktree, including the heat-semigroup, Gaussian, and Cheeger--Buser
continuations. This is a local audit and does not claim remote CI.

## Semantic boundary

The final numerical theorem is
`LogConcave.inverseScale_sq_le_pi_literature`: for every finite-dimensional
log-concave probability law, `inverseScale μ ^ 2 ≤ π * C_P^lit(μ)` in the
repository's `ENNReal` convention. Its proof uses the actual normalized
Gaussian convolution, the sharp smooth-model theorem, Poincaré upper
stability, setwise convergence, and a smooth-test Cheeger stability theorem.
The full-signature clients include zero-dimensional affine support and the
extended optimum; declaration auditing reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. The single deliberate
`sorry` remains the isolated `KLS.kls` target, outside certificate closures.
Individual-domain relative-perimeter convergence, the general RCD theorem,
and dimension-free KLS are not consequences claimed by this result.

## Layout and public API

The foundational finite classical wave flow belonged to the established
`Analysis/WaveSplitting/` family. It had the prohibited coexistence of
`Analysis/WaveSplitting.lean` and `Analysis/WaveSplitting/`. The complete
path map is:

| Old module | New module | Namespace and declarations |
| --- | --- | --- |
| `FunctionalInequalities.Analysis.WaveSplitting` (`Analysis/WaveSplitting.lean`) | `FunctionalInequalities.Analysis.WaveSplitting.Basic` (`Analysis/WaveSplitting/Basic.lean`) | Unchanged |

Three direct Lean consumers were updated: `WaveSplitting/Consistency.lean`,
`WaveSplitting/Energy.lean`, and `research/audits/WaveSplittingAudit.lean`.
There is no compatibility wrapper or alias. Historical decision records
retain their original paths; this map resolves them. Other new modules were
reviewed by mathematical owner and import level: generic wave and semigroup
tools under `Analysis`, generic Poincaré convolution under `Poincare`, Borell
and Gaussian specializations under `KLS/LogConcave/Density`, and reusable
Cheeger stability under `KLS/Geometry/Cheeger`.

## Current-document correction

The Blueprint paragraph immediately before the Cheeger--Buser theorem and
the generated literature register still described the comparison as pending.
The Blueprint is aligned with the current Lean theorem. The literature
register now records the log-concave numerical specialization as a local
fragment while leaving De Ponti--Mondino's general RCD theorem pending.
Progress views are regenerated from the intended Git index.
