# Lean statement entry points and certificates

This directory contains thin, node-specific Lean entry points. Reusable definitions and proofs
belong under `formalization/FunctionalInequalities/`; a file here only packages the exact theorem
surface associated with a repository ledger node.

## Lean certification convention

A proved ledger node certified by Lean records:

```yaml
"lean_solution": "solutions/LemLinearTestLower.lean",
"status": "proved",
"checked_by": "lean"
```

The certificate must:

1. stay below `solutions/` and use the `.lean` suffix;
2. name the ledger node in its header;
3. contain no `sorry`, `admit`, `native_decide`, `axiom`, or `unsafe` escape, including its local imports;
4. be included in a default Lake target; and
5. compile through `cd formalization && lake build`.

`python3 research/check_ledger.py` enforces the structural and provenance requirements. The Lake
build performs the machine check. A green structural check alone does not establish semantic
agreement with the reference statement.

For Issue #2, `solutions/LemLinearTestLower.lean` certifies `lem:linear-test-lower` and delegates
the reusable proof to `FunctionalInequalities.Project.LinearTestLower.certificate`.

## Draft and frozen statements

`solutions/LemPoincareTensorization.lean` is the entry point for the drafted tensorization node.
It imports `FunctionalInequalities.Tensorization` and names both candidate public declarations
with `#check`. The imported intermediate and public declarations end with `sorry`; no proof
wrapper or certification is supplied at this stage.

Drafted and frozen nodes use `checked_by: null`. They must meet the same path, header, and default
Lake target requirements, while placeholders remain permitted. Only proved nodes receive the
escape-token check. See `../research/ledger-schema.md` for the human freeze and proof handoff
rules.
