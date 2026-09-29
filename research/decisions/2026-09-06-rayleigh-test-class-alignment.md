# Rayleigh test-class alignment in the Cheeger--Buser proof

**Date:** 2026-09-06 (Asia/Shanghai). This continues the owner's preceding instruction
“fill in the gaps according to your assessment”, following [the review clarifications](2026-09-06-blueprint-review-clarifications.md).
The new screenshot was checked against the source before its suggestion was incorporated.
Work remains local on `main`; no commit or push is included.

## Resolution

The Cheeger--Buser node now directly uses and cites `lem:covariance-test-core-density`, with
`B = I`, when identifying the Rayleigh and literature test classes. No new lemma is introduced.

The source class in [De Ponti--Mondino, equation (2)](https://arxiv.org/pdf/1902.03835)
requires nonzero mean-zero Lipschitz functions that are bounded and have bounded support.
The proof therefore also records the support-preserving mean correction

\[
u_j=g_j-\left(\int g_j\,d\nu\right)\psi,
\qquad \psi\in C_c^\infty(V),\quad \int\psi\,d\nu=1.
\]

For a centered literature test, the density lemma gives convergence of `g_j` in both function
and gradient `L²`. The correction coefficient tends to zero, so both convergences persist.
Each corrected test has zero mean and compact support; a nonzero limit ensures the tests are
eventually nonzero in `L²`. The reverse inclusion uses bounded Lipschitz extension from the
closed intrinsic support. Its boundary has zero measure, so the metric slope and ambient
gradient norm agree almost everywhere. This proves the stated reciprocal identification of
the Rayleigh gap and literature constant. Dimension zero retains the separate treatment.

The displayed Cheeger--Buser statement and its `notready` status are unchanged. This is an
analytic proof clarification; it adds no Lean declaration or certification.

## Validation

- Blueprint checker: eight chapter files, 86 labels, four routes, zero errors.
- Ledger checker: six nodes, zero errors.
- Blueprint PDF, web, and Lean `checkdecls` all passed.
- The PDF remains 34 pages. The changed proof and adjacent material on PDF pages 19--21
  were rendered and visually checked. There are no overfull boxes, unresolved references,
  or bibliography warnings; the nine existing underfull-box notices remain.
- Source comparison verified that only the intended TeX proof/dependency and handoff navigation
  changed, plus this new record. All Lean sources, existing historical records, certificates,
  ledger, route sidecar, theorem statements, and status markers remain unchanged.
- `git diff --check` and local Markdown link checks passed.

Evidence is under
`/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-rayleigh-alignment-sgv6xdp_/`.
The preceding review's validation snapshot remains a separate historical record.
