# Project documentation maintenance

- When a proof update changes project progress, update the English Mermaid tree in
  `README.md` under `Proof progress tree`, its last-updated date, and the adjacent current-status
  summary in the same change. Review the tree after every proof update, even if no node changes.
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
