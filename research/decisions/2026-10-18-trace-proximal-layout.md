# Trace and proximal responsibility layout (2026-10-18)

This batch supports the existing Lee--Vempala arXiv:1612.01507v3 Lemma 42, Letwin
arXiv:2607.24164v1 trace/tensor bounds and the weak regular-class convex-analysis chain.
It preserves every declaration, hypothesis, constant, dimension, proof payload and certificate
status. Imports and module owners are the migration class; qualified names stay unchanged.

## Matrix trace family

- `Analysis/Matrix/Trace/Algebra.lean` owns finite real trace expansions, entrywise contractions,
  shift/conjugation identities and the elementary trace-energy sum-of-squares bound. It uses
  elementary real/matrix algebra and the actual tactic imports, without matrix spectral calculus.
- `Trace/Power.lean` owns the real-power rearrangement and spectral trace inequality, retaining
  positive definiteness, symmetry and nonnegative exponent assumptions exactly as stated.
- `Trace/Energy.lean` owns spectral positivity, mixed trace energy, Jordan domination and the
  pointwise tensor comparison. The existing private spectral/tensor supports remain together.
  The existing `TraceGram.lean` retains its analytic/Gram integration boundary; moving the
  pointwise tensor proof there would introduce the wrong prerequisite level.

The old `Matrix/Trace.lean` is retired without a compatibility wrapper. Pure algebra consumers
import Algebra; spectral/tensor consumers import their actual owners. Source index types and
empty-index cases remain distinct from the natural-dimension specializations.

## Proximal object

The existing proximal point, its attainment/specification and Lipschitz facts, Moreau derivative
and resolvent symmetry move with their private minimizer supports to the sibling
`Analysis/Convex/Proximal.lean`, depending on Subgradient. The subgradient quadratic-expansion
bridge has no proximal references and remains in `Subgradient.lean`. There is no reverse import.
The choice-based point definition and the assumptions of its validity theorems are preserved
separately. No convexity or regularity condition is added to the object definition.

## Independent acceptance

The [complete map](../api-migration/2026-10-18-trace-proximal-map.json) records exact source
segments, all owners and compiler identifiers. Checks include private-reference boundaries,
source payloads, elaborated types and definition closures, actual dependency changes, updated
clients and live links, private-index view generation, a full local verifier and index/history
protection. Diagnostics and receipts remain under
`build/file-management/2026-10-17-other-families-optimization/batch-03-trace-proximal/`.

The recorded mathematical progress date and all statuses are retained. Owner links are regenerated
and checked; layout does not certify a new theorem or complete another paper. Earlier dated
records and maps remain unchanged.
