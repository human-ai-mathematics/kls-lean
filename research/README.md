# Maintainer index

Use this index for current work, repository operations and validation records.
For the mathematics, start with the [proof path](progress/PROOF-PATH.md),
[literature register](progress/LITERATURE.md), [Lean design](../LEAN_DESIGN.md)
and [calling examples](../examples/README.md).

| Entry | Responsibility |
| --- | --- |
| [Current handoff](../HANDOFF.md) | Active work, accepted result, evidence pointers and next step. |
| [Agent instructions](../AGENTS.md) | Repository documentation, classification and maintenance rules. |
| [Contributing](../CONTRIBUTING.md) | Mathematical changes, review expectations and local checks. |
| [Verification guide](verification.md) | Verification commands, receipt rules and trust scope. |
| [Workflow](workflow.md) | Literature selection, placement, delivery checks and milestone CI. |
| [Naming](naming.md) | Directory, module, declaration and public parameter conventions. |
| [Release procedure](release.md) | Frozen snapshots, downstream checks and exact-revision remote evidence. |
| [Citation metadata](../CITATION.cff) | Project credit and revision information for reuse. |
| [Ledger schema](ledger-schema.md) | Certificate lifecycle, structural fields and interface changes. |
| [Certificate ledger](a-series/ledger.yaml) | Registered node statements, certificate files and certification states. |
| [Certificate directory](../solutions/README.md) | Packaged statements, imported mathematical owners and certification convention. |
| [Task atlas](verification.md#authorities-and-task-navigation) | Commands for task classification, declared dependencies and receipt-aware navigation. |
| [Task records](tasks.json) | Node priorities, assumptions, classification and evidence. |
| [Audit client guide](audits/README.md) | Independent proof clients and explicitly classified candidate statements. |
| [Classical KLS gate](audits/KLS/Classical/README.md) | Mathlib-only formulations, clients, mutation checks and replay scope. |
| [BKL independent-target pilot](audits/BKL/IndependentTargets/README.md) | Separately compiled specifications, definition bridges and baseline checks. |
| [Target-scope reviews](progress/target-reviews.md) | Current source correspondence and exact paper-target scope. |
| [Infrastructure review](progress/infrastructure-review.md) | Reviewed supporting interfaces and validation requirements. |
| [Statement-snapshot review](a-series/statement-snapshot/REVIEW.md) | Normative review of target and definition-closure baseline inputs. |
| [BKL independent-target review](audits/BKL/IndependentTargets/REVIEW.md) | Source correspondence and explicit foundation parameters for the pilot. |
| [Progress hub](progress/README.md) | Literature priorities, covered-paper maps and complete exploratory-route diagram. |
| [Node register](progress/STATUS.md) | Generated Blueprint node statuses, statements and certificates. |
| [Progress generation](verification.md#progress-generation) | Canonical inputs, index isolation and regeneration commands. |
| [Formalization guide](../formalization/README.md) | Library layout, pinned dependencies and build operations. |
| [Module directory](../formalization/MODULES.md) | Complete source-family and filename inventory. |
| [API directory](../formalization/API.md) | Compiler signatures and offline interface search. |
| [Blueprint guide](../formalization/blueprint/README.md) | Mathematical dependencies, marker rules and local rendering. |
| [Vendor guide](../formalization/vendor/README.md) | Pinned provenance, port changes and isolated upstream holes. |

## Document ownership

Current proof status belongs to the Lean statements, source records and verification receipts linked from the handoff.
Superseded operational handoffs, dated work logs and old-to-new migration maps are preserved byte for byte in a local
archive outside the published tree; a fresh clone does not need them, and current documents do not link to them.

`research/progress/update.py` owns generated progress blocks, `STATUS.md`, `TREE.mmd` and the paper views.
Edit their canonical records and regenerate them through the selected Git index; do not change generated text directly.
