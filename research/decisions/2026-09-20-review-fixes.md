# Third independent-review fixes (2026-09-20)

A third independent review of the layout, API-migration, verifier-hardening and documentation
rounds found two ownership/coverage defects and a group of current-status and navigation defects
that the earlier LD-001/002 closures had missed. This batch fixes them. It changes no theorem
statement, no certificate, no dimensional scope and no proof status; the dimension-free KLS bound
and the general high-dimensional Buser inequality with constant pi remain open. No commit, push,
staging change or cache deletion is part of this batch.

## Correction to the review's own first reading

The review first reported the `Poincare.LipschitzGradient.Comparison` import of
`Energy/LocalSlope/Relaxation` as simply unnecessary, on the evidence that the module elaborates
strictly without it. That evidence was correct but the conclusion was incomplete: the import was
load-bearing as a transitive re-export. Removing it alone breaks `Energy/Cheeger/Basic`, which
uses `Energy.LocalSlope.energy_eq_integral_gradient` and
`Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2` and imports only
`Energy/LocalSlope/Relaxation`. The defect is therefore an ownership defect, recorded as LD-013,
and the fix is a declaration move rather than an import deletion.

## LD-013: Energy declarations reached through a Poincare module

`Energy.LocalSlope.energy_eq_integral_gradient` moves from
`Poincare/LipschitzGradient/Comparison.lean` to `Energy/LocalSlope/Gradient.lean`, beside
`energy_eq_lintegral_gradient`, which its proof rewrites with, and `admissible_iff_memLp_gradient`,
which shares its namespace and binder context. Both of its real consumers —
`Energy/Cheeger/Basic.lean` and `KLS/LogConcave/WeightedGradient/Energy.lean` — are below the
Poincare layer, so the move follows the existing-owner rule rather than a guess at future reuse.

The move is pure. The theorem keeps its namespace `FunctionalInequalities.Energy.LocalSlope`, its
universe parameter, its implicit type variable, its hypothesis names, its parameter order and
binder visibility, and its proof term. It is placed in a dedicated `RealIntegral` section that
reproduces the binder context it was elaborated in, so its `pp.all` signature *and* definition are
byte-identical to the baseline; see `build/review-fixes-2026-09-20/signature-{before,after}.txt`.

`Energy/LocalSlope/Relaxation.lean` then drops the Poincare import, which it never used, and
`Energy/Cheeger/Basic.lean` imports `Energy/Euclidean/LipschitzApproximation/Approximation.lean`
explicitly — the same repair the final cleanup applied to two other consumers of that API. The
project import closure of `Energy/LocalSlope/Relaxation` falls from 43 modules to 13, of
`Energy/Cheeger/Basic` from 44 to 16 and of `Energy/Cheeger/Identification` from 48 to 20, and no
Poincare module remains in any of them. Direct `Energy -> Poincare` edges fall from two to one;
the survivor, `Energy/SmoothGradient/NormalDirection -> Poincare/SmoothTest/Basic`, has a real use.

`Energy.LipschitzGradient.relaxation` and the five bridge theorems beside it stay where they are,
recorded as the reviewed candidate LC-005: after this move no Energy-layer module depends on them,
and the bridges legitimately mix `Energy` and `Poincare` notions.

## LD-014: a library module outside every gate scope

`Analysis/Sard/Planar` had no consumer at all. Certificate import closures covered 174 of the 253
library modules, audit import closures 225 and the aggregate closure 245; their union covered 252,
and this module was the one outside all of them. Its public `sard_plane` and
`volume_image_nonflat_eq_zero` were therefore in no audited declaration closure, leaving kernel
replay — which accepts `sorryAx` — as their only gate. An isolated Lake project reproduced the
consequence: with a `sorry` in `sard_plane`, `check_ledger` reports nothing, the full-scope build
passes with a warning and `leanchecker` replays all 284 modules successfully.

`research/audits/PlanarSardAudit.lean` closes the gap. It restates both theorems, records with
`sard_agrees_in_dimension_two` that the sharp `Analysis.sard` already covers the planar case at
the same regularity, and prints five axiom reports. The verifier discovers it from the source
snapshot and compiles it with warnings as errors, so a proof escape in that module now fails
acceptance. This registers no certificate and advances no proof status.

## Current-status and navigation corrections

* `LEAN_DESIGN.md` named `KLS.Conjecture` in `KLS/Target.lean` as the library's only intentional
  hole. `KLS.Conjecture` is the `def … : Prop` of `KLS/Statement.lean`; it asserts nothing, carries
  no hole and is axiom-audited with the standard axioms only. The hole is the theorem `KLS.kls` in
  `KLS/Target.lean`. The live boundary now says so and keeps the distinction explicit. The same
  wording appears in the dated `2026-09-20-review-remediation.md`; that record is append-only and
  is corrected here rather than rewritten.
* `README.md`, `solutions/README.md` and `formalization/README.md` stated twenty-four certificates
  (twice), eight certificate entry points and ten accepted nodes in live sections. There are
  twenty-six. `solutions/README.md` already documented all twenty-six individually; only the
  summaries were stale. The `Examples` target descriptions now name both example roots.
* `HANDOFF.md` pointed its live Evidence bullet at a 2026-09-19 receipt recording ten gates, 262
  replayed modules and 726 snapshot files — the pre-LD-010 verifier scope. It now describes the
  current gate structure, points at `build/verification/latest.json`, and links the audit-coverage,
  review-remediation and review-closeout records, none of which any live document referenced.
* `formalization/FunctionalInequalities/KLS/README.md` displayed four obsolete paths inside its
  live file table (`Geometry/MinkowskiContent.lean`, `Geometry/SmoothDomain.lean` twice and
  `Geometry/GaussGreen.lean`); the statements were right and only the paths were stale.
* `KLS/LogConcave/Poincare.lean` referred in its module docstring to `KLS.LogConcave.
  AbsoluteContinuity` and to a `LiteratureComparison` module that does not exist.
* `research/naming.md` listed `Geometry/Surface/` among current family directories; that directory
  was removed by the Hausdorff batch.
* `Analysis/Semigroup/Generated/Basic.lean` described `S7`/`S8` as obligations of a research audit,
  and `Generated/Laws.lean` described `S8` as owned by another session. Both are proved in sibling
  modules; the docstrings now point there and keep the per-module non-claims.

## Declaration locations and progress provenance

The `line` field of every one of the 220 entries in `2026-09-20-final-cleanup-map.json` was written
before the same day's namespace-block change shifted declarations by one to eleven lines, and only
48 of them were re-recorded afterwards. That dated map stays unchanged; the
[location refresh](../api-migration/2026-09-20-review-fixes-map.json) records the current line of
all 220, together with the LD-013 move and the two import changes.

`research/progress/STATUS.md` and `LITERATURE.md` were generated from the working tree while their
own provenance text claimed staged canonical records, and `update.py --check` reported them stale.
The generator now states that it used the canonical records of the index of that run and points at
the canonical input digest, which is the verifiable identity of the snapshot. The views are
regenerated through a temporary `GIT_INDEX_FILE` holding exactly the twelve canonical records from
the working tree, saved as `build/review-fixes-2026-09-20/progress.index`; the real index is
untouched, and `GIT_INDEX_FILE=… python3 research/progress/update.py --check` passes against it.
Run against the real, empty-staged index the check still reports a difference, by construction.

## Validation

Full `lake build` over all 284 live modules, one warning: the intentional `KLS/Target.lean` hole.
Byte-identical `pp.all` comparison of the moved declaration. Import graph recomputed: 284 modules,
no cycles, no unresolved local imports, no `X.lean`/`X/` collision. Strict compilation of the new
audit client with warnings as errors. `check_ledger.py`, `check_blueprint.py`, `atlas.py check`,
`statement_snapshot.py check`, the Python test suite and a whole-library `sorryAx` sweep over every
constant originating in a local module. Task evidence hashes refreshed for the edited files after
checking their previous values against the saved baseline in `build/review-fixes-2026-09-20/`.
The complete `research/verify.py` is run last and writes its own snapshot-bound receipt.
