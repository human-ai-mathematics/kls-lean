# Current documentation and historical navigation

Date: 2026-10-17. The owner selected documentation and navigation organization after the KLS proof review and reuse assessment.
This maintenance changes documentation only. Mathematical statements, proof sources, namespaces, imports, certificates and paper coverage stay unchanged.

## Placement and scope

The existing root `LEAN_DESIGN.md` owns a concise current interface guide; `HANDOFF.md` owns the current result, evidence pointers and work.
Historical design narratives and the previous handoff belong to dated files in `research/decisions/`.
`examples/README.md` owns calling-example navigation beside the existing checked clients.
The research and formalization READMEs link these entry points, and the two chronological indexes remain generated from their existing record directories.

There are no Lean imports or public API changes. This is an extension of the existing documentation owners rather than a module migration.
No compiled artifact, API candidate, verification receipt or prior historical file is deleted or moved.

## Archive map

| Original current entry | Preserved historical record |
| --- | --- |
| `LEAN_DESIGN.md` | [Complete previous design](2026-10-17-lean-design-history.md) |
| `HANDOFF.md` | [Previous current handoff](2026-10-17-pre-documentation-navigation-handoff.md) |

The archives retain the complete original wording, including dated scope and former names. Only relative Markdown link destinations are rebased
for the new directory. Original bytes and a per-link archive map are retained in the ignored maintenance run
`build/file-management/2026-10-17-documentation-navigation/`.
Existing dated decisions, handoffs, source snapshots and failed evidence are unchanged. The two former WIP links in the 2026-09-15 correction register remain historical references, as already classified by the technical-debt register; their files exist in its inspected Git revision `e776840`.

## Current entry points

- [Root summary](../../README.md): statement, proved scope, separate open results and verification commands.
- [Lean design](../../LEAN_DESIGN.md): mathematical layers, frontend distinctions and change policy.
- [Calling examples](../../examples/README.md): checked examples and task-oriented module imports.
- [Current handoff](../../HANDOFF.md): accepted route, exact-snapshot evidence pointers and present work.
- [Research navigation](../README.md): proof, verification, history and storage reading paths.

The canonical literature priority note and proof-path summary now describe the completed stage-4 acceptance. Generated progress views are regenerated from a task-local private index; no theorem, certificate or diagram-node status is changed.

The current summaries describe acceptance of recorded proof snapshots. This prose maintenance does not renew a full Lean verification receipt
for the new documentation snapshot. The mathematical scope is unchanged.

## Validation

Validation covers local links and fragments, complete archive-content preservation modulo recorded URL rebasing,
reproducible chronological indexes, generated progress consistency through a private index, metadata checks and scoped whitespace.
The ledger, Blueprint and atlas checks pass. The private-index regeneration preserves every theorem and certificate status.
All Lean source files and existing historical records retain their baseline hashes.

An index-cache refresh was detected during maintenance. Ordered staging entries, flags and the staged diff match the baseline;
the refreshed index is retained as evidence and the original index bytes are restored at closeout. No staged content is reset.
A documentation-only edit does not require a Lean rebuild. The scoped results are retained in the ignored maintenance run;
no commit, push or remote CI is part of this task.
