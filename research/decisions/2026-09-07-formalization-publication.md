# Formalization publication change list

Date: 2026-09-07. The owner explicitly requested publication of the accumulated formalization.
This change list (CL) covers the large push required by the current `HANDOFF.md` workflow.
The destination is the canonical `numina-functional-inequalities/kls-lean` repository on `main`.

## Reviewed scope

- Add the explicit KLS statement/definitions, elaborated golden snapshot, definition checks,
  task atlas, infrastructure assessments, and source-bound verification pipeline.
- Publish the proved ambient/intrinsic and legacy/relaxed Poincare comparisons, weighted
  smooth approximation, and smooth/literature constant comparisons.
- Publish intrinsic absolute continuity for general finite-dimensional log-concave laws and
  the resulting selected/literature constant equality, including singular ambient laws and
  zero-dimensional intrinsic carriers. The ledger now has ten certified nodes.
- Migrate the public names to the canonical/ambient/L2Energy namespaces; update consumers,
  examples, Blueprint links, axiom guards, and current documentation together.
- Include the append-only development, mathematical scope, acceptance, and naming records.
  Generated build products, local verification artifacts, and caches remain ignored.

KLS itself, the full Borell density/moment representation, the concrete Dirichlet property,
Cheeger identification, and the long KLS routes remain open. This publication does not promote
those statements or infer certification from Blueprint rendering.

## Evidence before this publication record

`git fetch origin main` completed; local HEAD and `origin/main` both equal
`70ca1c19c4d207a31716c2e589c0b096521a5490`, with no divergence.
The actual working source digest matched the passed receipt
`build/verification/20260906T162106.565232Z/report.json`:
`b7cb489ef4c9cf2e0b25960ef452587aa8fce69f35d00a5cfd9a8e11434dfeaa`.
That receipt covers structural checks, 97 Python tests, the default Lean build, the
26-declaration statement golden, 105 axiom reports, and replay of all 71 local modules.
The naming decision records the separate 123-declaration semantic comparison.

## Publication procedure and evidence boundary

This record is written before committing. After staging the reviewed source files, commit the
batch and rerun `python3 research/verify.py` on the actual commit, so its generated receipt names
the published candidate SHA and includes this record. Push only after that run passes; verify
the remote `refs/heads/main` against local HEAD and inspect the CI runs for that exact SHA.
The final verification receipt and remote run are the evidence for those subsequent events;
this pre-publication record does not claim that they have already occurred.

Local verification builds local source and replays local modules in Lean's kernel, trusting
pinned third-party compiled imports. It does not constitute an independent external checker
or an isolated third-party source rebuild. Local success, a pushed commit, and remote CI
success are separate facts. Earlier decisions retain their original local-only status claims.
