# Research navigation

Use the [current handoff](../HANDOFF.md) for present work and the [paper register](progress/LITERATURE.md) for exact theorem scope.
The [Lean design](../LEAN_DESIGN.md) and [calling examples](../examples/README.md) provide the library entry points.

## Reading paths

| Need | Entry |
| --- | --- |
| Follow the proved KLS chain | [Proof path](progress/PROOF-PATH.md) and [BKL main chain](progress/README.md#bkl-main-proof-chain) |
| Check a paper version, theorem or certificate | [Literature register](progress/LITERATURE.md), [certificate directory](../solutions/README.md) and [ledger](a-series/ledger.yaml) |
| Inspect all routes and recorded local statuses | [Progress overview](progress/README.md) and [generated node register](progress/STATUS.md) |
| Query snapshot-bound project context | [Read-only MCP](context-mcp.md) |
| Reproduce verification or change a module | [Verification](verification.md), [workflow](workflow.md) and [naming](naming.md) |
| Prepare an exact public revision | [Release procedure](release.md), [contribution guide](../CONTRIBUTING.md) and [citation metadata](../CITATION.cff) |
| Read the current normative reviews | [Target-scope reviews](progress/target-reviews.md), [infrastructure review](progress/infrastructure-review.md), [statement-snapshot review](a-series/statement-snapshot/REVIEW.md), [BKL independent-target review](audits/BKL/IndependentTargets/REVIEW.md) and the [audit client guide](audits/README.md) |
| Manage compiled artifacts and retention evidence | [Read-only inventory](inventory_artifacts.py) and [recoverable artifact storage](artifact_storage/README.md) |

## Document ownership

Current proof status belongs to the Lean statements, source records and verification receipts linked from the handoff.
Superseded operational handoffs, dated work logs and old-to-new migration maps are preserved byte for byte in a local
archive outside the published tree; a fresh clone does not need them, and current documents do not link to them.

`research/progress/update.py` owns generated progress blocks, `STATUS.md`, `TREE.mmd` and the paper views.
Edit their canonical records and regenerate them through the selected Git index; do not change generated text directly.
This directory keeps navigation separate from the mathematical and verification records it points to.
