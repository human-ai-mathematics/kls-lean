# Per-node certification in shared dossier headers

**Date:** 2026-08-29 (Asia/Shanghai)

**Type:** repository/provenance convention

## Context

`solutions/glm-linear-baselines.tex` covers both `lem:linear-test-lower` and `thm:glm-fi`. The
former now has a node-specific Lean certificate, while the latter retains its independent agent
review. A single dossier-level `checked_by: agent` line is historically true of the analytic
proof but no longer describes both active ledger modes.

## Decision

When a shared TeX dossier covers nodes with different active certification modes, its header lists
the active `checked_by` value and associated `review:`, `accepted_by:`, or `lean_solution:` path
separately for each node. Historical analytic author and reviewer provenance remains present and
is not rewritten. The production ledger remains the machine-readable authority for active mode.

No checker schema changes are needed: the checker already validates certification per ledger node,
requires the TeX header to enumerate that node, and validates explicit node-specific Lean
artifacts. This decision removes human-facing ambiguity without coupling unrelated nodes or
splitting a sound shared analytic dossier.

## Validation

The updated shared header, ledger node, manuscript statement, analytic lemma, and Lean certificate
are checked together by the post-repair semantic audit. Repository validation includes the full
ledger checker, checker regression suite, standalone dossier compilation, and default Lake build.

The independent follow-up at
`research/reviews/2026-08-29-lean-linear-test-semantic-followup.md` passed this provenance check.
The standalone dossier compiled to 2 pages, the complete manuscript to 161 pages, `lake build`
completed 2,946 jobs, the production checker reported 195 nodes and 0 errors, all 44 regression
tests passed, and `git diff --check` was clean.
