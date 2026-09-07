# Energy module layout

Date: 2026-09-07. This records a local file organization change requested from the Energy
file-browser view. It follows the subject-directory convention in formalization/README.md.
It does not record new mathematics or change proof status.

## Scope and migration

Twelve Lean files move into three existing topic families: Relaxation, Euclidean/SmoothGradient,
and Euclidean/IntrinsicAffine. Each family's entry module is Basic.lean. The six general energy
interfaces stay at the Energy root; the two cross-topic Euclidean modules stay at that level.
Declaration namespaces, theorem names, statements and proof bodies remain unchanged. Consumers
use the new imports directly, with no forwarding files at old paths. Existing uncommitted work
is preserved. Historical decisions and explorations retain the paths used at their recorded date.

Both columns below are relative to formalization/FunctionalInequalities/. Replace slashes with
dots and remove .lean to obtain import names after FunctionalInequalities.

| Previous path | Current path |
| --- | --- |
| `Energy/Relaxation.lean` | `Energy/Relaxation/Basic.lean` |
| `Energy/RelaxationApproximation.lean` | `Energy/Relaxation/Approximation.lean` |
| `Energy/RelaxationContraction.lean` | `Energy/Relaxation/Contraction.lean` |
| `Energy/RelaxationLowerSemicontinuous.lean` | `Energy/Relaxation/LowerSemicontinuous.lean` |
| `Energy/RelaxationQuadratic.lean` | `Energy/Relaxation/Quadratic.lean` |
| `Energy/RelaxationRecovery.lean` | `Energy/Relaxation/Recovery.lean` |
| `Energy/Euclidean/SmoothGradient.lean` | `Energy/Euclidean/SmoothGradient/Basic.lean` |
| `Energy/Euclidean/SmoothGradientQuadratic.lean` | `Energy/Euclidean/SmoothGradient/Quadratic.lean` |
| `Energy/Euclidean/SmoothGradientDensity.lean` | `Energy/Euclidean/SmoothGradient/Density.lean` |
| `Energy/Euclidean/SmoothGradientClosed.lean` | `Energy/Euclidean/SmoothGradient/Closed.lean` |
| `Energy/Euclidean/IntrinsicAffine.lean` | `Energy/Euclidean/IntrinsicAffine/Basic.lean` |
| `Energy/Euclidean/IntrinsicAffineClosed.lean` | `Energy/Euclidean/IntrinsicAffine/Closed.lean` |

## Validation method

Compare every pre-existing Lean file against the pre-move working-tree snapshot after applying
only this import mapping and module-reference comment updates. Check the complete local import
graph under the same renaming, absence of obsolete active imports, and preservation of unrelated
working-tree edits. Run `python3 research/verify.py` for the existing structural, Python, Lake,
statement-baseline, declaration-axiom and current-module kernel-replay checks. Run reports remain
in build/verification/; this migration does not update a statement baseline or certify new results.

The first structural check detected stale infrastructure hashes for the two Euclidean
cross-topic modules after their import edits. Their pre-move hashes matched the stored evidence,
and the source comparison established that only imports changed. The three corresponding
evidence entries in research/tasks.json now hash the migrated sources; no status is promoted.
