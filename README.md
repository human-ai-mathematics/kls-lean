# kls-lean

Lean formalization of functional inequalities toward the KLS conjecture, with separate
statement review and proof stages. Lean and Mathlib are pinned to **v4.33.0**.

## Where to look

| Purpose | Entry point |
| --- | --- |
| Lean source layout, imports, and build instructions | [formalization/README.md](formalization/README.md) |
| Mathematical definitions and scope | [LEAN_DESIGN.md](LEAN_DESIGN.md) |
| Current work and proof handoff | [NEXT_STEPS_CONTEXT_FOR_CODEX.md](NEXT_STEPS_CONTEXT_FOR_CODEX.md) |
| Node statements and certification status | [research/a-series/ledger.yaml](research/a-series/ledger.yaml) |
| Node-specific Lean entry points | [solutions/README.md](solutions/README.md) |
| Review history | [research/decisions/](research/decisions/) and [research/explorations/](research/explorations/) |

The linear-test/covariance lower bound ([#2](https://github.com/numina-functional-inequalities/kls-lean/issues/2))
and binary tensorization upper bound ([#6](https://github.com/numina-functional-inequalities/kls-lean/issues/6))
are proved. Finite tensorization and optimal-constant equality
([#7](https://github.com/numina-functional-inequalities/kls-lean/issues/7)) have completed human
acceptance and semantic review, with a node certificate and `proved` / `checked_by: lean` status.
The [freeze record](research/decisions/2026-09-03-finite-tensorization-freeze.md) preserves the
approved statements, and the [acceptance record](research/explorations/2026-09-03-finite-tensorization-acceptance.md)
records the review and validation. The publication commit and its matching CI result are tracked
in Issue #7.

The next proposed independent task is the sharp one-dimensional Gaussian Poincaré constant,
beginning with test-domain, variance-parameter, Mathlib API, and proof-route review before human
freezing. Finite tensorization supplies one ingredient of the product-case KLS argument; the
remaining analytic inputs are separate work.

## Verify

From the repository root:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

The default build includes all three proved certificates and the accepted reusable library.
No proof placeholders remain in the current default build. Draft placeholders are permitted by
the workflow; proved certificates and their local imports must be free of proof escapes.
See the [ledger contract](research/ledger-schema.md).
