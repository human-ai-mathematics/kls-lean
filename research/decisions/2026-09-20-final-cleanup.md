# Final structural cleanup and candidate review (2026-09-20)

This batch completes LD-008 and resolves the responsibility splits LC-001/002. It also closes
LC-003/004 as reviewed, accepted API choices. It changes organization and API names, not proof
completion, dimensional scope, generator domains, weights, or constants. The dimension-free KLS
bound remains open. No commit or push is part of this batch.

## Ownership and migration

The [migration map](../api-migration/2026-09-20-final-cleanup-map.json) lists all 48 renamed
semigroup declarations, all 220 reviewed declarations with source locations, and the two
one-to-many file moves. Generic generated operators, laws, limits and Markov properties now use
`Analysis.Semigroup.Generated`; concrete counterparts use `KLS.LogConcave.HeatSemigroup`.
The public operator constructors are `Generated.operator` and `HeatSemigroup.operator`.
Binder order is unchanged, including the position of the log-concavity proof after the weight
arguments. Clients use explicit arguments where the old dot notation no longer applies.
There are no compatibility aliases. Resolvent/Yosida lemmas and closed-weighted-operator lemmas
keep their own object identities; they are not semigroup operations merely because construction
uses them.

`Energy/Euclidean/LipschitzApproximation` is a real four-module family: Basic (gradient and cutoff
facts), Measurable (gradient measurability and almost-everywhere differentiability), Kernel
(normalized convolution and estimates), Approximation (weighted approximation theorems).
`KLS/LogConcave/Density/BorellRepresentation` has Basic (representative predicate and its
properties), Moments (tail and moment consequences), Construction (existence of the density
representative), and Intrinsic (intrinsic frontends). Pure moves preserve namespaces.

The final audit also gives `BakryEmeryRouteStatements` an explicit KLS Poincare frontend
import for the specialization moved in LD-006. Nine direct clients now import an earlier layer. Two consumers that previously obtained the
full approximation API transitively now import Approximation explicitly. The cutoff layer
imports the Mathlib bump construction used by its original elaborated statement, preserving
instance selection. It does not import the project smooth-gradient energy implementation.
Borell Basic imports the Haar affine-subspace fact directly, without importing log-concave
absolute-continuity construction. Rich original mathematical introductions remain at the final
entrypoint of each family.

## Candidate dispositions

| Candidate | Disposition | Reason |
| --- | --- | --- |
| LC-001 | Resolved | Four distinct roles with actual clients of Basic, Measurable and Kernel; weighted approximation scope preserved. |
| LC-002 | Resolved | Representative facts, moments, construction and intrinsic specialization have independent consumers and explicit prerequisites. |
| LC-003 | Accepted exception after migration | The generator estimate now has the object-qualified short name `Generated.generator_limit`. The two long Gauss–Green names distinguish interior/exterior support conditions that matter mathematically. Length alone is not a defect. Existing `sequentialRelaxation` and graph identities are not renamed without an ownership defect. |
| LC-004 | Accepted public interface | The 73 LipschitzApproximation and 60 Graph/Implicit declarations express named cutoff, kernel, measurability, splitting, coordinate and inverse-function facts. Their role is mathematical reuse, including use by proofs in their own family. Zero external-library uses do not prove implementation privacy. Existing private helpers remain private; no public API is removed on this heuristic. |

This is a source review of the flagged families, not a claim that every possible external client
was inspected. There is no evidence requiring another visibility reduction. Future genuinely
internal implementation helpers should be private at introduction; visibility changes to published
mathematical interfaces require a concrete consumer and migration plan.

## Verification boundary

The [final checks](../technical-debt/2026-09-20-final-checks.json) record the current structural
scan, declaration comparison, API-presence check, and evidence refresh. The full verifier emits a separate snapshot-bound receipt after all
tracked records are finalized.
The declaration comparison traverses project types and definition bodies, applies only the
explicit name map, and checks parameters, universes, visibility and dependencies. Bound variable
labels and anonymous hygienic instance labels are normalized. Generated theorem auxiliaries may
be identified by identical complete types, using proof irrelevance; non-proof definitions are
not collapsed. This inspection supplements compilation and kernel replay, not a replacement.

The original dated audits and prior migration records remain historical snapshots. Current
Blueprint paths, evidence hashes, progress links, overviews and handoff are updated. Progress
views are regenerated through an isolated Git index/object store so unrelated real staging is
preserved. The classification workflow remains in [workflow.md](../workflow.md) and
[naming.md](../naming.md): classify object, scope, role and actual consumers before moving a file;
separate a file move from an API rename; close with client, metadata and semantic verification.
