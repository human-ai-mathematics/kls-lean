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

Each proved node has exactly one named `certificate`, directly importing the reusable library.
The former `Project/` forwarding layer has been removed. Concrete specializations are checked
with typed `#check` applications rather than duplicate public theorems.

- `LemLinearTestLower.lean` directly combines `Poincare.rayleigh_le_constant` and
  `Covariance.lambdaMax_le_constant` into the Issue #2 Euclidean statement, retaining the finite
  second-moment assumption and the zero-dimensional case.
- `LemPoincareTensorization.lean` directly combines `Poincare.Holds.prod` and
  `Poincare.constant_prod_le` into the Issue #6 Hilbert statement. A typed application checks
  Euclidean factors of arbitrary dimensions, including zero.
- `LemPoincareFiniteTensorization.lean` contains
  `Solutions.LemPoincareFiniteTensorization.certificate`, directly packaging the Issue #7
  binary reverse/equality, finite tensorization/equality, and boundary conclusions. Its API
  checks also retain the supporting transport interfaces.

All three nodes are recorded as `proved` with `checked_by: lean`. The binary tensorization freeze and
acceptance records are `../research/decisions/2026-09-03-tensorization-freeze.md` and
`../research/explorations/2026-09-03-tensorization-acceptance.md`; the latter records validation
and the final publication/CI status.

## Future draft and frozen statements

Drafted and frozen nodes use `checked_by: null`. They must meet the same path, header, and default
Lake target requirements, while placeholders remain permitted. Only proved nodes receive the
escape-token check. See `../research/ledger-schema.md` for the human freeze and proof handoff
rules.

## Finite tensorization certificate

Issue #7 and node `lem:poincare-finite-tensorization` use
`solutions/LemPoincareFiniteTensorization.lean`, with `status: proved` and `checked_by: lean`.
Its sole named certificate covers the ledger claim. The 45 `#check @...` statements retain
the reusable API surface; eight Euclidean statement families and six concrete boundary cases
are checked through typed applications of that API. These applications add no duplicate
specialization declarations. The deduplication review remains in
`../research/explorations/2026-09-03-certificate-deduplication.md`; the original 53-name candidate
is preserved as history in `../research/decisions/2026-09-03-finite-tensorization-candidate.md`.

The scope includes binary reverse bounds/equality, finite fixed-constant tensorization,
finite optimal equality, and the supporting coordinate/isometry transports. Their library
proofs are implemented, as recorded in
`../research/explorations/2026-09-03-finite-tensorization-proofs.md`. Application checks verify
how these declarations specialize; the certificate separately combines the accepted conclusions.

The user's confirmation and final semantic review complete the human acceptance recorded in
`../research/decisions/2026-09-03-finite-tensorization-freeze.md` and
`../research/explorations/2026-09-03-finite-tensorization-acceptance.md`. The final publication
SHA and matching CI result are tracked in
[Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7).
The existing #2 and #6 nodes retain their ledger claims, certificate signatures, and independent
checked import closures.
See `../formalization/README.md` for the current reusable module layout.
