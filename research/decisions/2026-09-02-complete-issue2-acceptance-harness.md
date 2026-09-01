# Complete the Issue #2 Lean certification harness

**Date:** 2026-09-02

**Type:** repository certification harness

## Rationale

The native Issue #2 formalization and node-specific certificate already compiled, but the minimal
repository did not contain the repository-facing certification layer required by the Issue #2
acceptance criteria. Add the smallest complete chain connecting `lem:linear-test-lower` to
`solutions/LemLinearTestLower.lean` through `checked_by: lean`, together with an executable checker
and focused regression tests.

## Decision

- Add one bounded ledger at `research/a-series/ledger.yaml` containing only
  `lem:linear-test-lower`. Unrelated historical KLS/A-series nodes, manuscript files, and
  experiment artifacts remain outside this repository.
- Store the ledger in JSON syntax, which is a valid YAML 1.2 subset. This lets the exact command
  `python3 research/check_ledger.py` run with the Python standard library and no ambient PyYAML
  installation.
- For `checked_by: lean`, require a proved node, a repository-relative `.lean` artifact below
  `solutions/`, an exact node token in the certificate header, no `sorry`/`admit`/`axiom`/`unsafe`
  token, and inclusion of the certificate module in a default Lake target.
- Keep compilation and semantic review as separate gates. The checker validates structure and
  provenance; `lake build` performs the machine check, while the prior term-by-term comparison
  establishes agreement with the reference statement.
- Document the convention in `research/ledger-schema.md`, `solutions/README.md`,
  `LEAN_DESIGN.md`, and `formalization/README.md`. Record the design and Mathlib boundary in the
  new append-only exploration entry.

No Lean source, theorem statement, manuscript, or experiment artifact is modified by this harness
change.

## Files

- `research/a-series/ledger.yaml`
- `research/check_ledger.py`
- `research/ledger-schema.md`
- `research/tests/test_check_ledger.py`
- `solutions/README.md`
- `research/explorations/2026-09-02-issue2-certification-harness.md`
- this append-only decision record
- certification sections in `LEAN_DESIGN.md` and `formalization/README.md`

## Validation

The exact production commands returned:

```text
$ python3 research/check_ledger.py
1 ledger(s), 1 nodes. 0 error(s).

$ python3 -m unittest discover -s research/tests -p 'test_*.py'
.............
----------------------------------------------------------------------
Ran 13 tests in 0.077s

OK

$ cd formalization && lake build
Build completed successfully (2946 jobs).
```

A new local clone was created without copying `.lake/`. Its ledger check and 13 tests passed, and
Lake cloned the pinned dependency graph, checked out Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, and compiled the complete graph:

```text
Build completed successfully (2953 jobs).
```

A second build of the same clean snapshot also passed:

```text
Build completed successfully (2946 jobs).
```
