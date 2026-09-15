# Project documentation maintenance

- Keep progress documentation together in `research/progress/`: `ROUTES.md` contains the
  English Mermaid diagrams, `STATUS.md` the generated node register, and `README.md` their index.
  The root README retains the entry link and current-status summary.
- When proof progress changes, review both diagrams, their date, and the root current-status
  summary. After staging the intended proof/metadata changes, regenerate the register with
  `python3 research/progress/update.py` and include it in the same commit. The generator reads
  canonical records from the Git index to exclude unrelated unstaged changes.
- Base completion markers on the current theorem statements and verification evidence. Preserve
  assumptions, dimensional scope, and the distinction between a proved result, a completed route,
  and a ledger certificate. Do not mark a wrapper proved if it still depends on `sorryAx`.
- Keep the next-step highlight aligned with the current handoff. The dimension-free KLS bound
  stays open until that exact statement is proved and verified.
- Keep the route overview complete for the four active branches in
  `formalization/blueprint/route-composition.yaml`. Draw arrows from prerequisites toward
  conclusions and ultimately KLS, with AND within each route and OR between sufficient routes.
  Distinguish upstream mathematical results, conditional implications, and local Lean proofs;
  keep refuted branches and restricted model calculations outside the active implication chain.
- Maintain links for every diagram node and the fallback link directory. Review both the route
  overview and the detailed analytic diagram after proof updates or source-file moves.
- Keep the progress tree and its surrounding documentation in English. Preserve unrelated work
  when preparing documentation commits.
- Use the established progress notation: `✓` for completed local Lean proofs, `◐` for partial
  local formalization, and `○` for pending work. Keep upstream mathematical or conditional-proof
  provenance separate; it must not turn a pending local formalization into a completed result.
- Commits containing only non-Lean files must not trigger CI. Automatic workflow path filters
  select `**/*.lean`; commits with Lean changes retain normal CI. Never add `[skip ci]` to a
  commit containing Lean changes merely because it also updates progress documentation.
