# Project documentation maintenance

- Formalize published KLS literature. Select work by a named source, pinned version and target
  theorem, retaining its hypotheses, constants, normalization and dimensional scope. Develop
  supporting infrastructure for an identified literature target. Exploratory routes and unproved
  research hypotheses are research records, not formalization targets in their own right.
- Keep progress documentation together in `research/progress/`: `LITERATURE.md` is the primary
  paper-by-paper register (target theorem, Lean statements, status, certificate); `README.md`
  directly displays the literature priorities and the English Mermaid diagrams on the GitHub
  directory page; `STATUS.md` is the generated node register. The root README stays a one-page
  summary: statement, what is proved, what is not, where to look and how to verify.
- Apply the paper-coverage criteria in
  [When a paper is covered](research/progress/LITERATURE.md#when-a-paper-is-covered).
- Keep `HANDOFF.md` limited to the current state. Keep internal maintenance records, agent-session
  artifact tooling and operational history under the ignored local `build/history/` archive;
  preserve superseded records verbatim, with hashes. Keep rules, current source reviews and
  validation inputs in their tracked owning directories so a fresh clone
  needs no local history. Do not rewrite previously pushed Git history during archival cleanup.
- When proof progress changes, review the source-paper mapping in `literature.json`, the complete
  diagram, its date, and the root current-status
  summary. After staging the intended proof/metadata changes, regenerate all progress views with
  `python3 research/progress/update.py` and include it in the same commit. The generator reads
  canonical records from the Git index to exclude unrelated unstaged changes.
- Base completion markers on the current theorem statements and verification evidence. Preserve
  assumptions, dimensional scope, and the distinction between a proved result, a completed route,
  and a ledger certificate. Do not mark a wrapper proved if it still depends on `sorryAx`.
- Keep the literature priorities and the next-step highlight aligned with the current handoff.
  The dimension-free KLS bound is proved through the accepted BKL main line.
- Keep the exploratory route overview complete for the four branches in
  `formalization/blueprint/route-composition.yaml`. The four exploratory routes are not current
  formalization targets and are retained as historical records; their unproved hypotheses remain
  open mathematically. KLS is proved through the accepted BKL main line.
  Badge open hypotheses as such rather than as
  pending formalization, and badge not-formalized results exclusive to superseded routes accordingly.
  Draw arrows from prerequisites toward
  conclusions and ultimately KLS, with AND within each route and OR between sufficient routes.
  Distinguish upstream mathematical results, conditional implications, and local Lean proofs;
  keep refuted branches and restricted model calculations outside the active implication chain.
- Keep one large combined Mermaid diagram and a row-by-row upstream approach table on the same page.
  Maintain `research/progress/nodes.json` and the pinned portfolio inventory; generate the README
  blocks, `STATUS.md`, and `TREE.mmd` with `update.py`. Do not edit generated blocks directly.
  Derive mapped node statuses from Blueprint records; record evidence for auxiliary assessments.
  Label completed local results "Formalized in Lean"; distinguish full approach goals from supporting results.
- Maintain links for every diagram node and the fallback link directory. Review the route
  diagram and the approach table after proof updates or source-file moves.
- Keep the progress tree and its surrounding documentation in English. Preserve unrelated work
  when preparing documentation commits.
- Use the established progress notation: `✓` for completed local Lean proofs, `◐` for partial
  local formalization, `◇` for hypotheses that remain open mathematically and are not current
  formalization targets, and `○` for pending work
  or not-formalized results of superseded routes as labelled. In paper lemma maps (`lemma_map` in
  `literature.json`), `⇑` marks a reviewed stronger statement or a different proof route; list
  every numbered statement of the pinned source version in the literature register (the hub
  displays covered papers only), and let ✓/◐/○ follow the declarations. Keep upstream mathematical or conditional-proof
  provenance separate; it must not turn a pending local formalization into a completed result.
- Run remote CI only at meaningful verification milestones: a new certificate, a faithfully
  formalized paper main theorem, or validation before sharing/release. Lean certification runs
  on explicit manual dispatch or a pushed `milestone/**` tag; ordinary branch pushes and PR
  updates do not trigger it. Lean certification is the only remote certification workflow; the
  manually dispatched Palomar full preflight (`.github/workflows/palomar-preflight.yml`) is
  separate, advisory submission preparation, never dispatched routinely. Build Blueprint
  locally when its artifacts are needed.
  Remote CI uses `research/verify.py --lean-only --no-kernel-replay`; documentation/metadata
  and Python checks remain in the full local verifier. Remote CI preserves the strict Lean
  build and declaration/vendor axiom audits; the local-module kernel replay is part of full
  local verification only. See [receipt scope](research/verification.md#receipts-and-trust-scope).
  Do not use `[skip ci]` to control this policy or add routine scheduled full builds.
  Keep change-appropriate local checks; report remote verification only for the exact SHA
  with a successful run. See `research/workflow.md` for the CI procedure.

# Formalization classification and layout

- Before adding or splitting a module, or changing a public API, follow
  `research/workflow.md` and the detailed rules in `research/naming.md`.
- Classify by mathematical object, actual scope, role and dependency level. Reuse the existing
  owning family; distinguish generic tools, object definitions, substantive properties, concrete
  specializations, identification bridges, counterexamples and audit-only candidate statements.
- Record a brief placement plan in the current task/handoff before editing: owner, scope,
  destination, imports, extend/split/create decision, API impact and validation. This is not an
  extra approval requirement, and small edits do not need a separate planning document.
- Split when responsibilities or dependency requirements diverge, not solely because a file is
  long. Do not create empty future modules or use `Basic`, `Misc` or `Utils` as catch-all files.
- Review directory names, filenames and declaration names separately. Let family directories and
  object namespaces carry context; preserve meaningful mathematical distinctions in the API.
- Treat module moves and namespace/name changes as separate migration classes. Preserve the dirty
  baseline, provide complete maps, update consumers, and compare semantic interfaces before
  refreshing evidence. Historical records stay unchanged; no old-path wrappers or name aliases.
- Finish with the change-appropriate checks in `research/workflow.md`; documentation-only edits
  do not require a Lean rebuild, and layout cleanup does not change proof or certificate status.
