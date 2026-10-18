# Library usability: source comments, published Git consumer and compiler API index

Date: 2026-10-18. Baseline: `b9ebbc3c41462fa269f4240ab5a95c703192aea2`.

The three batches are ordered and independently accepted: source-process comment maintenance,
a pure-Git consumer of the published baseline, then the review checklist and generated API directory.
Acceptance records and the final report are under `build/reusability/2026-10-18-library-usability-followup/`.
They retain their individual source snapshots; no earlier receipt is relabelled as current verification.

## Placement and scope

The [remaining comment archive](2026-10-18-remaining-source-process-history.md) preserves original
passages, including task labels, model/job provenance, old migration and progress narration.
Mathematical documentation, source locators, legal notices and all non-comment source bytes are
preserved. Source evidence hashes are reassessed; mathematical metadata and all certificate states
are unchanged. Earlier dated records remain byte-identical.

The independent Lake consumer requires the exact published Git revision and the `formalization/`
subdirectory. Its three clients come from that revision, and all 32 primary modules start without
compiled outputs. Strict compilation, a 467-declaration standard-only audit and 35-module kernel
replay pass. Ten clean pinned third-party source/compiled caches are reused by APFS copy-on-write;
there is no workspace primary-project compiled cache or source overlay. This narrow acceptance is
not a new full KLS verification or a fresh Mathlib rebuild.

The checklist extends [the existing workflow](../workflow.md#review-after-mechanical-checks).
It is informed by the public [Tau Ceti review rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics)
and [formal-library discussion](https://xenaproject.wordpress.com/2026/10/16/how-to-formalize-all-of-mathematics/).
It separates mechanical checks, mathematical meaning, reuse, public API, documentation and evidence.
It does not change the repository's CI policy or create a new automated approval claim.

`research/APIIndex.lean` is a compiler-observation tool; `research/api_index.py` builds the existing
library and extracts public names, kinds, types, universes, owning modules, source positions and
docstrings. It creates the compact [API navigation](../../formalization/API.md) and complete offline
HTML/JSON plus a source/tool hash manifest under ignored `build/api-index/`. The imported module
set must match all current library modules. The generator builds and imports every inventory
module explicitly: the aggregate alone reaches 578 of the 585 source modules. Private/internal names are excluded; compiler-generated
public support may remain. This index records interfaces and never infers proof or certificate status.
Pinned compiled Mathlib imports remain trusted. No production declaration, proof or assumption changes.

Existing module/namespace owners and mathematical dependency directions are unchanged. No aliases,
wrapper modules, new mathematical families, toolchain upgrades, external registrations, Comparator
installation, remote CI, commit or push are part of this task. Local editor configuration and the
actual staging area are preserved. Later upstream contributions or compatibility work need their
own scope and acceptance.

## Previous downstream guide passage (verbatim)

````markdown
The initial independent acceptance used commit `79fbe1a`: 32 project modules were compiled
from its separate Git checkout, without KLS, solution or repository-example imports. Pinned
third-party source/compiled caches were copied separately; this was not a fresh Mathlib rebuild.
The subsequent operator APIs and current examples were tested against an explicit source overlay.
Choose a revision containing those additions when using the Git recipe; [HANDOFF](../HANDOFF.md)
owns delivery status. The [reuse decision](../research/decisions/2026-10-18-downstream-reuse.md)
records the scope and receipt locations.
````

## Previous handoff (verbatim)

````markdown
# Current KLS handoff

Updated 2026-10-18 for combined reuse/API and source-comment delivery.

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
follow-up stays paused. Sealed failures, previous decisions and controller records remain
historical evidence. The [pre-delivery handoff](research/decisions/2026-10-18-pre-delivery-handoff.md)
preserves the preceding state verbatim.

The combined revision retains the two derived semigroup APIs and three calling examples,
with existing proofs, assumptions and certificate states unchanged. Its fresh full local
verification and source/staged-tree comparisons are recorded under
`build/reviews/2026-10-18-reuse-comments-full-validation-and-push/`; `COMPLETION.json` binds
the accepted source snapshot to the resulting commit and confirmed remote revision when delivery
completes. Local editor configuration is excluded. Earlier receipts above retain their original
snapshot scope; ordinary branch delivery does not claim remote CI.
````
