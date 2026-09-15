# Project documentation maintenance

- When a proof update changes project progress, update the English Mermaid tree in
  `README.md` under `Proof progress tree`, its last-updated date, and the adjacent current-status
  summary in the same change. Review the tree after every proof update, even if no node changes.
- Base completion markers on the current theorem statements and verification evidence. Preserve
  assumptions, dimensional scope, and the distinction between a proved result, a completed route,
  and a ledger certificate. Do not mark a wrapper proved if it still depends on `sorryAx`.
- Keep the next-step highlight aligned with the current handoff. The dimension-free KLS bound
  stays open until that exact statement is proved and verified.
- Keep the progress tree and its surrounding documentation in English. Preserve unrelated work
  when preparing documentation commits.
