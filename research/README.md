# Research navigation

Use the [current handoff](../HANDOFF.md) for present work and the [paper register](progress/LITERATURE.md) for exact theorem scope.
The [Lean design](../LEAN_DESIGN.md) and [calling examples](../examples/README.md) provide the library entry points.

## Reading paths

| Need | Entry |
| --- | --- |
| Follow the proved KLS chain | [Proof path](progress/PROOF-PATH.md) and [BKL main chain](progress/README.md#bkl-main-proof-chain) |
| Check a paper version, theorem or certificate | [Literature register](progress/LITERATURE.md), [certificate directory](../solutions/README.md) and [ledger](a-series/ledger.yaml) |
| Inspect all routes and recorded local statuses | [Progress overview](progress/README.md) and [generated node register](progress/STATUS.md) |
| Reproduce verification or change a module | [Verification](verification.md), [workflow](workflow.md) and [naming](naming.md) |
| Find a historical design or integration decision | [Chronological decisions](decisions/README.md) |
| Read the dated proof correction history | [2026-09-15 correction register](proof-corrections-and-improvements.md); retained historical source references |
| Find a dated work handoff | [Chronological handoffs](handoffs/README.md); current instructions belong to the root handoff |
| Manage compiled artifacts and retention evidence | [Read-only inventory](inventory_artifacts.py) and [recoverable artifact storage](artifact_storage/README.md) |

## Document ownership

Current proof status belongs to the Lean statements, source records and verification receipts linked from the handoff.
Dated decisions and handoffs retain their original claims. They can describe formerly active work or old module paths.
The [design archive](decisions/2026-10-17-lean-design-history.md) preserves the earlier root design narrative.

`research/progress/update.py` owns generated progress blocks, `STATUS.md`, `TREE.mmd` and the paper views.
Edit their canonical records and regenerate them through the selected Git index; do not change generated text directly.
Chronological decision and handoff lists use the existing `make_index` generator in `inventory_artifacts.py`.
This directory keeps navigation separate from the mathematical and verification records it points to.
