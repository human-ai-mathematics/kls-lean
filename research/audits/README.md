# Versioned infrastructure audit sources

These Lean clients are source evidence referenced by `research/tasks.json`. Keep them in Git:
CI validates their paths and SHA-256 hashes from a clean checkout. Generated logs and local
verification receipts belong under the ignored `build/` directory.

The files were copied byte-for-byte from the local coarea audit sources on 2026-09-15, preserving
the recorded evidence hashes. Their comments describe the corresponding historical audit rounds.
`WeightedCoareaRouteStatements.lean` checks proposition types only; it does not prove them.
`LevelSetMeasurableAudit.lean` deliberately reports the axioms of still-open WIP results as well as
proved results. These clients are not ledger certificates and are not library-root imports.

After building the relevant library modules, run any client from `formalization/`, for example:

```sh
lake env lean -DwarningAsError=true ../research/audits/OpenGraphAudit.lean
```
