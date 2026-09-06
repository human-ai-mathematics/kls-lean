# Evolving interfaces and current proof certification

**Date:** 2026-09-06 (Asia/Shanghai). **Authorization:** the owner stated
“由于我们处于起步状态，所以我并不打算冻结lean接口”, then approved the proposed
interface-evolution policy with “可以，那就调整一下”.

## Current policy

Public Lean interfaces may evolve, including those of proved results. Proof work can refine a
draft without a prior freeze, and new nodes may move directly from `drafted` to `proved`.
`proved`, `checked_by: lean`, and Blueprint `\leanok` refer to the current statement and proof;
they do not promise signature stability or backward compatibility.

Interface refactors migrate their consumers directly. Changes to hypotheses, conclusions,
test domains, or normalization must be recorded explicitly and synchronized with the ledger,
Blueprint, certificates, and consumers as applicable. Review whether the original mathematical
goal remains covered, and rerun the relevant build and axiom checks. A revision without a
complete proof returns to `drafted` / `checked_by: null` and loses its Lean-certification claims.

This decision supersedes the mandatory `drafted -> frozen -> proved` policy in the earlier
handoff and ledger guide, including the sentence retaining statement-freeze rules in
[the earlier workflow record](2026-09-06-workflow-and-documentation-status.md). That record and
all older freeze and acceptance records remain unchanged as dated evidence. The current
[lifecycle guide](../ledger-schema.md#lifecycle) governs subsequent work. Selected mature
interfaces may receive an explicit stability commitment later.

## Ledger and Blueprint representation

No new status field or schema is introduced. The existing snapshot checker already accepts
direct `drafted -> proved` development. Its behavior remains unchanged; its module description
now states the current policy. Existing support for historical `frozen` nodes remains, with
`checked_by: null`; new work does not use it as a mandatory checkpoint.

Blueprint `\notready` now marks an explicit unresolved statement choice, with the choice
identified in nearby prose. An open proof or a possible future API change alone does not
justify it. Removing the marker neither adds Lean certification nor changes route status.

Fifteen markers that only reflected the former freeze requirement are removed. The affected
statements already specify their current assumptions, domains, and normalization:

- intrinsic raw/core agreement under the displayed density hypotheses;
- the eight marked shared interfaces: smooth/literature comparison, selected/literature
  comparison, Cheeger-scale definition, density Cheeger identification, Cheeger--Buser
  comparison, covariance closure, affine/isotropic reduction, and the one-dimensional bound;
- the two conditional-fiber comparison statements;
- the four analytic approximation and closure statements in Appendix A.

`thm:smooth-gradient-relaxation-two-cheeger` retains the sole `\notready` marker. Its specific
unresolved choice concerns local-slope versus asymptotic-Lipschitz relaxation, including the
comparison for singular measures and the affine-support convention. This is a mathematical
statement question, not a requirement to freeze Lean signatures.

All 32 Lean-certified Blueprint nodes retain their annotations. The six production ledger
nodes, Lean sources, mathematical statements, dependency edges, declaration anchors, and route
sidecar are unchanged by this policy adjustment. The live guides and Blueprint orientation
now consistently describe certification separately from interface stability.

## Validation

- Ledger checker: six proved/Lean nodes, zero errors.
- Blueprint checker: eight chapter files, 86 labels, four active routes, zero errors.
- All 63 Python tests pass. No new checker behavior or test cases were needed.
- Default `lake build` succeeds, 3241 jobs.
- Blueprint PDF, web, and `checkdecls` builds succeed. The PDF has 34 pages, no overfull
  boxes or unresolved references/citations, and nine underfull warnings. Physical pages
  2, 6, 7, 12, 17, 18, 21, and 29 were rendered and visually checked without clipping or overlap.
- The 73 mathematical statement blocks are unchanged after excluding the removed status
  markers and whitespace. All labels, dependency edges, Lean anchors, and `\leanok` annotations
  are unchanged. The `\notready` count is now one, down from sixteen.
- Source hashes confirm that all 105 protected files in the turn snapshot, including Lean
  sources, the production ledger, route sidecar, and existing historical records, are unchanged.
  No source file was deleted. Only 15 existing documentation files or the checker module
  description changed, and this decision record was added.
- The ledger checker's Python AST is unchanged after excluding its module docstring.
- All 111 local Markdown links in the changed guides and this record resolve.
- `git diff --check` passes. No commit or push was performed.

The turn snapshot, preservation report, build logs, and PDF inspection images are in
`/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-evolving-interfaces-20260906-zzqb7_sj`.
