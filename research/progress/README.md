# KLS progress

| View | Purpose |
| --- | --- |
| [Route diagrams](ROUTES.md) | Four routes toward KLS and the current analytic proof steps, using ✓ / ◐ / ○ |
| [Progress table](STATUS.md) | Local node IDs, mathematical provenance, recorded Lean status, certificates, dependencies, and gaps |

These views describe our formalization work. Upstream mathematical proofs and conditional
arguments remain separate from local Lean proofs. A completed auxiliary result is not necessarily
a separately registered certificate. KLS remains open.

## Where the records come from

- [Blueprint](../../formalization/blueprint/src/chapters/) supplies local node statements,
  dependencies, and Lean annotations.
- [Ledger](../a-series/ledger.yaml) supplies registered certificate records.
- [Task metadata](../tasks.json) supplies mathematical classifications and infrastructure gaps.
- [Route composition](../../formalization/blueprint/route-composition.yaml) supplies explicit
  upstream provenance and the four sufficient-route alternatives.
- [Selected upstream snapshot](../upstream/2026-09-12-kls-research.json) preserves additional
  pinned research records. It is a selection, not the complete upstream ledger.

The table is a derived documentation view, not a new source of proof status. It does not execute
Lean or attest to the latest remote CI result. Follow the [verification guide](../verification.md)
for those checks. The diagrams remain a reviewed summary; their auxiliary nodes need not have
individual Blueprint IDs.

## Updating after proof work

1. Update the relevant source, ledger/Blueprint annotations, and task metadata with the appropriate
   proof evidence. Review [both diagrams](ROUTES.md), their links, and the next-step highlight.
2. Stage only the intended proof and metadata changes, then run from the repository root:

   ```sh
   python3 research/progress/update.py
   ```

   The generator reads canonical records from the Git index, so unrelated unstaged changes do not
   silently enter the published table. It reads `ROUTES.md` from the working tree for the diagram
   node directory. Input hashes in the table identify the records used.
3. Review and stage `STATUS.md`, `ROUTES.md`, and the adjacent root README status summary as needed.
   Use `python3 research/progress/update.py --check` to check that the table is current.

Commits containing only non-Lean files do not trigger CI, as requested by the owner. Both
GitHub workflows automatically run only when `**/*.lean` changes. Keep `[skip ci]` on this initial
non-Lean publication as well. Commits containing Lean changes follow the normal verification and
CI workflow; do not add `[skip ci]` to those commits. Blueprint retains its existing manual trigger.
