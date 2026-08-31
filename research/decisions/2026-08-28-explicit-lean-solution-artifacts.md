# Explicit node-specific Lean certificate paths

**Date:** 2026-08-28 (Asia/Shanghai)

**Type:** repository/control-plane decision

## Context

The existing `checked_by: lean` checker convention inferred a `.lean` path by replacing the
suffix of a node's natural-language `solution:` dossier. That convention is ambiguous when one
shared TeX dossier proves several ledger nodes, as
`solutions/glm-linear-baselines.tex` does for `lem:linear-test-lower` and `thm:glm-fi`. It would
also force an unrelated shared filename onto a node-specific certificate.

## Decision

Add an optional `lean_solution:` ledger field with the following contract:

- it is valid only with `checked_by: lean` on a proved or certified-conditional node;
- it is a repository-relative `.lean` path confined under `solutions/`;
- the file must exist and its header must enumerate the ledger node; and
- when omitted, the legacy `.lean` file adjacent to the TeX dossier remains accepted for backward
  compatibility.

The natural-language `solution:` remains required. Lean certification changes the checking mode;
it does not erase the standalone dossier or its provenance. Compilation is a build concern, so
the default `formalization/lake build` target explicitly includes the node certificate. The
control-plane checker validates identity, path safety, type, suffix, existence, and header binding
without attempting to invoke a toolchain.

## Rationale

The explicit field supports thin node-specific certificates while preserving shared analytic
dossiers and existing ledger data. Header binding prevents an arbitrary compiling `.lean` file
from satisfying the existence check for the wrong node. Keeping compilation in Lake makes the
checker deterministic and fast while the standard build remains the machine-proof gate.

## Validation

`research/tests/test_check_ledger.py` covers:

- successful explicit artifact binding;
- a missing declared file;
- a header naming the wrong node;
- confinement outside `solutions/`;
- non-string metadata;
- a non-`.lean` suffix;
- rejection when `checked_by` is not `lean`; and
- the legacy adjacent-file fallback.

The complete checker suite passed:

```text
uv run --with pyyaml python -m unittest discover -s research/tests -p 'test_*.py'
Ran 44 tests ... OK
```

No production ledger was edited as part of this decision; that single-file write remains reserved
for an explicitly assigned sole ledger orchestrator.
