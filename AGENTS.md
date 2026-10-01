# Project documentation maintenance

- Formalize published KLS literature. Select work by a named source, pinned version and target
  theorem, retaining its hypotheses, constants, normalization and dimensional scope. Develop
  supporting infrastructure only for an identified literature target. Temporary exploratory
  routes and unproved research hypotheses are not formalization targets.
- Keep progress documentation together in `research/progress/`: `README.md` directly displays
  the English literature map and current paper priorities; `LITERATURE.md` is the primary
  paper-by-paper register and `STATUS.md` is the generated supporting node register.
  The root README retains the literature entry link and a concise current-status summary.
- Mark a paper target covered only when its main theorem is faithfully stated in Lean, proved
  without nonstandard axioms, and registered with a certificate and verification evidence for
  the exact statement. Supporting lemmas and restricted or conditional counterparts do not
  certify a paper. Keep current handoffs short; retain history in dated `research/decisions/`.
- When proof progress changes, review the source-paper mapping, diagram, date and root current-status
  summary. After staging the intended proof/metadata changes, regenerate all progress views with
  `python3 research/progress/update.py` and include it in the same commit. The generator reads
  canonical records from the Git index to exclude unrelated unstaged changes.
- Base completion markers on the current theorem statements and verification evidence. Preserve
  assumptions, dimensional scope, and the distinction between a proved result, a completed route,
  and a ledger certificate. Do not mark a wrapper proved if it still depends on `sorryAx`.
- Keep the literature priorities and next source-review/proof step aligned with the current handoff.
  A pending node in the Blueprint/atlas is an inventory entry, not authorization to choose an
  exploratory route as the next task. The dimension-free KLS bound
  stays open until that exact statement is proved and verified.
- Preserve exploratory routes separately in `research/explorations/ROUTES.md`, clearly marked
  as non-targets. Their composition and pinned portfolio live in that directory. `active` in
  route metadata means membership in the retained logical composition, not an active proof task.
  Preserve mathematical prerequisites, AND/OR structure, provenance and refutations there;
  do not restore the four-route tree or approach table to the primary progress view.
- Maintain `research/progress/nodes.json`, `literature.json` and the exploratory inventories;
  generate primary and exploratory views with `update.py`. Do not edit generated blocks directly.
  Derive mapped node statuses from Blueprint records; record evidence for auxiliary assessments.
  Label completed local results "Formalized in Lean"; distinguish full approach goals from supporting results.
- Maintain source links for literature nodes and declaration/certificate links in the paper
  register. Review affected supporting and exploratory links after source-file moves.
- Keep the progress tree and its surrounding documentation in English. Preserve unrelated work
  when preparing documentation commits.
- Use the established progress notation: `✓` for completed local Lean proofs, `◐` for partial
  local formalization, and `○` for pending work. Keep upstream mathematical or conditional-proof
  provenance separate; it must not turn a pending local formalization into a completed result.
- Run remote CI only at meaningful verification milestones: a new certificate, a faithfully
  formalized paper main theorem, or validation before sharing/release. Lean certification runs
  on explicit manual dispatch or a pushed `milestone/**` tag; ordinary branch pushes and PR
  updates do not trigger it. Lean certification is the only remote workflow; build Blueprint
  locally when its artifacts are needed.
  Remote CI uses `research/verify.py --lean-only`; documentation/metadata and Python checks
  remain in the full local verifier. Preserve strict Lean audits and local-module replay.
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
