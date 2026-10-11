# Repository file-management goal

Created 2026-10-11 at the owner's request. Goal service is tracked in Codex chat
`01a12b29-a858-7c43-9bb3-b28e3d038b05`. This is repository maintenance; it does not replace the
mathematical controller or change the BKL priorities in [HANDOFF.md](../../HANDOFF.md).

## Scope and execution

The owner requested stronger models through the existing project API. Reuse that connection,
with `gpt-6-astra` as the task model, high reasoning, no weaker fallback and no automatic retry.
Keep the provider, credentials and global configuration unchanged. API workers author the
management plan and file candidates; Codex independently reviews and applies accepted changes.
Only one editor may apply a batch. No commit, push, tag or remote CI is authorized.

The first inventory found approximately 100 GiB in `build/reviews/` and `build/verification/`
(`du`, before cleanup), 293 decision records, 23 handoff records and 466 library Lean modules.
These are dated measurements, not promised reclaimable space.

## Placement plan

Owner: repository-maintenance tooling and research navigation. Scope: evidence inventories,
recoverable storage management, historical-document indexes and a concise current handoff.
Destination: narrowly scoped tooling under `research/` if a reusable tool is warranted;
navigation in the existing research directories; candidates and independent evidence in
`build/reviews/2026-10-11-file-management/`. Extend existing owners where appropriate; create
only substantive files. This phase changes no Lean namespace, public API, proof or certificate.
The API worker must report any concrete module-placement concern before proposing a move;
any accepted move needs the complete mapping and checks in [workflow.md](../workflow.md).

## Baseline and preservation

The actual dirty source tree and Git index were captured in
`build/reviews/2026-10-11-file-management/baseline/`, including per-file SHA-256 records,
tracked diffs, source-file archive and an index copy. The actual index is not modified.
Preserve unrelated modifications, accepted and failed histories, current packet handles,
all live verification receipts, and every referenced evidence path. Classify active,
adopted, historical and rebuildable artifacts before any storage mutation. Storage changes
must preserve content and metadata or provide a verified recoverable archive and complete
path map. Irrecoverable deletion requires a concrete reviewed proposal and owner approval.

## Acceptance

1. Actual inventory and classification with recorded evidence and exclusions.
2. Useful navigation and current-state condensation, with superseded handoff text preserved
   verbatim in a dated decision record and all relative links checked.
3. Safe, recoverable management of reviewed storage candidates; report actual actions and
   measured results, without equating logical duplicate bytes with physical savings.
4. Independent review of API-authored changes; preserve initial files outside the accepted
   scope and the real Git index; check links, consistency and `git diff --check`.
5. Run change-appropriate checks only. A documentation/storage-only change needs no Lean
   rebuild and advances no proof, certificate or coverage status. Old verification receipts
   remain evidence for their recorded snapshots, not a fresh receipt for this edited tree.

Completion requires the implemented files and independent acceptance evidence. Creating this
goal or receiving an API proposal alone does not complete it.

## Accepted implementation and storage-tool placement

The Cutoff and Cumulant family migration is recorded separately in
[the complete path/declaration map](../api-migration/2026-10-11-cutoff-cumulant-family-map.json)
and [the layout decision](../decisions/2026-10-11-cutoff-cumulant-families.md).
The independent comparison covers 122 owned declarations, 137 closure declarations and
16 definition bodies, with explicit compiler-generated identifier mappings. Full `lake build`
passed; no theorem statement, authored namespace, proof status or certificate status changed.

Storage-tool owner: repository evidence maintenance. Create the three substantive layers
`research/artifact_storage/{filesystem,journal,transaction}.py` and the CLI entry point
`research/deduplicate_artifacts.py`: descriptor/metadata operations, durable recovery history,
and bounded transactions have distinct responsibilities and dependencies. These extend the
inventory workflow and have no Lean imports or mathematical API impact. Primary implementations
come from completed `gpt-6-astra` API responses; the coordinator's integration corrections are
preserved as diffs against those candidates. Independent native fixtures and read-only review
must pass before a historical batch. Validation covers APFS/SDK ABI, ACL and binary xattrs,
COW isolation, ordinary restoration, stale path/inode checks and failure recovery.

Same-path COW replacement retains bytes, access/modification times, mode, ownership and xattrs.
It changes inode and ctime; creation time may also change and is recorded. Restore-unique
writes an ordinary independent copy of the verified current bytes with the same specified
metadata. No historical evidence file is deleted, renamed or classified as a proof failure.
Full original scope is checked in ignored `build/file-management/COMPLETION.json`; the final
receipt must match all finished source and documentation edits.

## Confirmed filename extension (2026-10-12)

The owner selected the screenshot's Analysis/BKL scope, then authorized autonomous completion
and a following Goal in the established coordinator / strong API proof constructor / reviewed
Claude integrator mode. After this maintenance goal, inform the original Claude conversation
of the complete path maps and verification, coordinating its LevStochCalc introduction before
continuing the source-faithful BKL/Letwin chain. This does not authorize commit, push or remote CI.

Placement plan: the real operator family owns `Operator/{Coordinates,Positive,InverseSqrt}`;
BKL's six suspension modules own `Suspension/{Basic,Law,Density,Moments,Cumulant,Derivatives}`;
rename `PosteriorDomain` to `PosteriorCovariance` for its actual covariance/coefficient scope.
Move whole files, retain namespaces/public names/proofs, update only prerequisite import tokens
and current consumers. Keep `RingInverseDerivative` generic, and keep `LocalThirdCumulant`:
its local positive exponential radius distinguishes it from all-radius versions. `sigma` is
defined in Law; Basic defines the potential and foundational convexity properties. No new
aggregate or forwarding module. Before editing, export every actually owned declaration and
its structural type/definition closure; compare with an explicit compiler-owner map afterward.
Finish both layout batches together with the full local verifier and a matching final receipt.

The coordinator's `git status` once refreshed only the real index's stat cache. Complete
ordered staging entries and assume/skip flags matched the baseline; the changed index was
saved, and original index bytes were restored. Future read-only Git operations use
`GIT_OPTIONAL_LOCKS=0`. No staged content, HEAD or user work was reset. The final preservation
acceptance distinguishes this cache restoration from staging or committing.
