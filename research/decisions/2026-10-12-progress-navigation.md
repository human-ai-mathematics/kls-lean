# Progress generation and current-guide navigation

Date: 2026-10-12. Owner-authorized scope: repair index consistency, separate current guides
from history, and add a generated BKL main-proof reading view. No Lean proof, theorem,
certificate, coverage classification, dependency pin or real Git index is changed by this task.
No commit, push, tag or remote CI is authorized.

## Placement and implementation

Owner: `research/progress/update.py` for input selection and generation;
`research/progress/literature.py` for a view of the existing paper lemma maps.
Extend those owners. Canonical selectors and short input-boundary summaries live in
`research/progress/literature.json`; the navigation carries no independent status fields.
The README template, catalogs and declaration sources are read from the chosen Git index
and included in one digest. Old generated template bodies are outputs and are excluded
from the template digest. Missing indexed inputs fail rather than falling back to disk.

The progress README displays generated selected-target coverage and a BKL reading table.
The table starts with conditional assembly and locates the Taylor criterion, suspension,
universal cumulant obligation, stochastic dynamics, Letwin input and moment-map construction.
Status and entry declarations remain derived from their canonical item maps; certificate
links must match the registered declaration. Reading order is not a second dependency graph.
The combined four-route diagram and row-by-row approach table stay on the same page.

## Guide history

The four previous guide bodies are preserved in the dated records below. Only relative
Markdown link destinations are rebased to retain their original repository targets;
mathematical claims, counts, dates, wording and internal heading anchors are retained.
These snapshots are historical and do not override current source or handoff state.

- [Root guide](2026-10-12-root-guide-history.md).
- [Formalization guide](2026-10-12-formalization-guide-history.md).
- [KLS module guide](2026-10-12-kls-module-guide-history.md).
- [Verification guide](2026-10-12-verification-guide-history.md).

Current guides retain reading entry points, layout, operations and trust boundaries;
proof status and coverage are referenced from the paper/node registers and current handoff.
The root guide is a short statement/scope/navigation/verification summary.

## Acceptance scope

Regressions run in disposable Git fixtures for unstaged exclusion, staged catalog/template/
statement inclusion, generated-block repair and missing indexed input rejection. Navigation
checks cover conditional status, source entry membership and certificate membership.
Generate and check all views with a task-local temporary index containing the intended
canonical source/metadata snapshot. Preserve the actual index and existing dirty proof work.
Review links, archived prose, semantic metadata differences and scoped whitespace checks.
Documentation/generator checks establish no new Lean proof or snapshot-bound Lean receipt.

## Local check results

- 18 progress regressions passed, including disposable-index isolation and navigation boundaries.
- 39 Blueprint regressions passed; the structural checker reports four active routes and no errors.
- Generated-view `--check` passed using the task-local canonical index.
- Ledger validation reports 30 registered nodes and no errors; atlas validation reports no cycles.
- Review checks preserve all four archived prose bodies (only link rebasing), validate 97 live
  guide/navigation links and anchors, and confirm unchanged Lean source hashes and real-index staged entries/flags.
  Git stat-cache refreshes are recorded separately and do not change staging.
- Scoped whitespace checks passed. No Lean rebuild, commit, push or remote CI was run.

The task-relative patch and detailed local review are retained under
`build/reviews/2026-10-12-progress-navigation/`. These are documentation/generator checks,
not a new full Lean verification receipt.
