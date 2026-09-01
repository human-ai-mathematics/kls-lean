# Minimal Issue #2 ledger schema

The production ledger is `research/a-series/ledger.yaml`. It intentionally contains only the
Issue #2 node shipped by this repository. The file uses JSON syntax, which is a valid subset of
YAML 1.2, so `python3 research/check_ledger.py` has no third-party Python dependency.

The top-level object contains:

- `meta.program`: exactly `a-series`;
- `meta.scope`: a short description of the bounded ledger;
- `nodes`: an array of unique node objects.

Every node contains `id`, `kind`, `status`, `statement`, `lean_solution`, and `checked_by`.
`source` is optional provenance prose. For this Issue #2 ledger:

- the required node is `lem:linear-test-lower`;
- `checked_by` is `lean` only when `status` is `proved`;
- `lean_solution` is a repository-relative `.lean` file below `solutions/`;
- the certificate header names the exact node id;
- the certificate contains no `sorry`, `admit`, `axiom`, or `unsafe`; and
- the corresponding Lean module is a root of a default Lake target.

The checker validates structure and provenance. Mathematical correctness and compilation are
separate gates: compare the statement with the reference and run `cd formalization && lake build`.
