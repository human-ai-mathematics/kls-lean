# Pre-delivery handoff archive

Recorded 2026-10-18 before the combined reuse/comment verification and delivery.
The following previous handoff is preserved verbatim; its receipts and uncommitted-state claims
apply to that earlier snapshot. Current delivery is owned by [HANDOFF](../../HANDOFF.md).

````markdown
# Current KLS handoff

Updated 2026-10-18 for the accepted reuse/API proposal and source-comment maintenance.

## Accepted result and open boundaries

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the selected BKL
cutoff-localization route. Its target is unchanged: one finite covariance-normalized
literature Poincaré bound for every dimension and every log-concave probability law with
finite second moment, including dimension zero and singular affine supports.

The accepted chain is compact Letwin Theorem 1.2 (constant 8) → finite-horizon cutoff BKL (95)
→ source-form BKL Theorem 4.1 → source-form BKL Theorem 1.1 → KLS.
The [paper register](research/progress/LITERATURE.md) owns exact scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean and its certificates.
BKL's main theorem is covered. Letwin's noncompact Theorems 1.1/1.2, the uncut Eldan
construction and literal identities (68)–(73), and the separate uncut intermediate statements
remain open. The four exploratory routes retain their own statuses.

## Current library and maintenance state

The article-standard review, BKL reorganization, documentation corrections and five subsequent
source-layout batches are complete and independently accepted. All 8,018 compared public
interfaces agree across the latter layout work. Proof statements, definitions, assumptions,
certificate states and existing historical records were preserved.

- [Lean design](LEAN_DESIGN.md) and [calling examples](examples/README.md): public interfaces and imports.
- [Module directory](formalization/MODULES.md) and [BKL guide](formalization/FunctionalInequalities/KLS/BKL/README.md): source owners.
- [Maintenance register](research/technical-debt/remaining-families.md): per-batch decisions, migration maps and acceptance requirements; MetricBV cross-family relocation remains deferred.
- [Final documentation decision](research/decisions/2026-10-18-final-documentation-review.md): corrected status prose and shortened navigation.

## Reuse proposal and evidence

The independent Git-pinned downstream acceptance, three narrow clients and two bounded-operator
interfaces are recorded in the [reuse decision](research/decisions/2026-10-18-downstream-reuse.md)
and [example guide](examples/README.md). Concise source headers and the scoped HminusOne openings
preserve all 42 original declaration interfaces and proof-expression comparisons. Existing
certificates, hypotheses and history are unchanged; the one empty migrated source directory was removed.

The downstream/API snapshot `c9958b5d54af9715ff06354bf3a4386c5629387330c1902bc2ef21a1735f1d0d`
passed full local verification at `build/verification/20261018T034819.544549Z/report.json`
(297 gates, 282 strict clients, 9,856 local declarations and 867 module replays).
Every project-local declaration, `KLS.kls` included, is audited; known [vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

The downstream/API proposal has per-batch receipts and its final frozen-tree verification
under `build/reusability/2026-10-18-downstream-and-examples/STATE.json` and `FINAL-ACCEPTANCE.json`.
Each receipt applies to its recorded snapshot; see [receipt scope](research/verification.md#receipts-and-trust-scope).

## Source-comment maintenance

The subsequent documentation-only pass cleans process records in 72 source files, in seven
independently accepted batches. Every byte outside comments is preserved, along with hypotheses,
certificate states, existing history and the real staging area. Original comments and the previous
handoff are retained in the [process-history archive](research/decisions/2026-10-18-source-comment-process-history.md).
Its source comparisons, reassessed evidence hashes and current documentation checks are indexed by
`build/file-management/2026-10-18-source-comment-cleanup/COMPLETION.json`.
This pass changes source/document hashes and does not renew the full Lean receipt above.

## Coordination and delivery

Proof API loops and the original Claude proof-integrator session are idle. The queued review
follow-up stays paused. All sealed failures, previous decisions and controller records remain
historical evidence. The earlier one-commit/one-push delivery is complete at `79fbe1a`;
the reuse/source-interface and comment-maintenance changes are local and uncommitted. Superseded evidence/delivery
wording is preserved in the [reuse decision](research/decisions/2026-10-18-downstream-reuse.md).
````
