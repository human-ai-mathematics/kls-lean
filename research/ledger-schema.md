# Statement lifecycle and Lean certification ledger

The production ledger is `research/a-series/ledger.yaml`. It uses JSON syntax (a subset of
YAML 1.2), so the checker requires only Python 3.11 or newer and its standard library.

The top-level object contains `meta.program` (exactly `a-series`), `meta.scope` (nonempty prose),
and `nodes` (an array of unique nodes). Every node contains `id`, `kind` (currently `lemma`),
`status`, `statement`, `lean_solution`, and `checked_by`. `source` is optional provenance prose.
The existing `lem:linear-test-lower` node remains required. It, `lem:poincare-tensorization`,
and `lem:poincare-finite-tensorization` are recorded as `proved` with `checked_by: lean`.

## Lifecycle

| Status | Meaning | `checked_by` | Lean artifact |
| --- | --- | --- | --- |
| `drafted` | Candidate statement awaiting human review | `null` | Compilable declaration skeleton; placeholders allowed |
| `frozen` | Human-approved statement awaiting proof | `null` | Same frozen signatures; placeholders allowed |
| `proved` | Completed proof and certification | `"lean"` | No forbidden escape tokens in the artifact or its local imports |

The intended progression is `drafted → frozen → proved`. Only human review can freeze a
statement. Proof work begins after that review; the proof agent must preserve the frozen public
signatures and ledger statement. A suspected error goes into a new append-only exploration
entry for human resolution. The checker validates a snapshot; it does not infer human approval
or enforce transition history. A green skeleton build is not proof certification.

For a future unproved node, retain the `checked_by` field with the explicit JSON value `null`.
This illustrative node is not an entry in the current ledger:

```json
{
  "id": "lem:future-result",
  "kind": "lemma",
  "status": "drafted",
  "statement": "The exact mathematical statement, including all assumptions and encoding choices.",
  "lean_solution": "solutions/LemFutureResult.lean",
  "checked_by": null
}
```

The tensorization signatures, complete ledger statement, and human acceptance are recorded in
`decisions/2026-09-03-tensorization-freeze.md`. Its source correspondence, semantic review,
validation evidence, and publication/CI status are recorded in
`explorations/2026-09-03-tensorization-acceptance.md`. Earlier draft-stage decision and exploration
entries remain unchanged as historical records. In particular, their past placeholder counts
do not describe the current proved node.

## Structural and proof checks

For every status, the artifact must exist under `solutions/`, have the `.lean` suffix, name the
exact node id in its header, and be a root of a default Lake target. A draft artifact can import
the reusable declaration modules and name their public signatures with `#check`; it is a
statement entry point rather than a proof certificate. The default build compiles its imports.
Each proved node uses one named certificate directly referencing the reusable library; concrete
specializations can be checked by typed applications without additional public wrapper theorems.

For `proved` nodes only, the conservative static guard rejects `sorry`, `admit`, `native_decide`,
`axiom`, and `unsafe`. It scans the entry point and recursively follows literal local Lean
imports resolved below `formalization/` or the repository root. It scans source text including
comments, does not scan unrelated draft modules, and does not audit third-party dependencies.
This guards against an unproved imported declaration being hidden behind a thin entry point.

Run all three acceptance commands:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

The checker validates structure and provenance; `lake build` checks elaboration and compilation.
Neither command replaces mathematical review or the proof-phase inspection of theorem axioms.

## Finite tensorization acceptance (2026-09-03)

Node `lem:poincare-finite-tensorization` for Issue #7 uses
`lean_solution: solutions/LemPoincareFiniteTensorization.lean`, with `status: proved` and
`checked_by: lean` after human ratification and proof acceptance. Its sole named certificate
packages the binary, finite-product, and boundary conclusions. The same default-build file
retains the 45 supporting public-interface checks, eight Euclidean statement families and six
concrete boundary applications. No schema or checker exemption is needed.

The current approval and exact statement snapshot are in
`decisions/2026-09-03-finite-tensorization-freeze.md`; semantic, machine, and publication gates
are recorded in `explorations/2026-09-03-finite-tensorization-acceptance.md` and Issue #7.
The earlier candidate and wrapper-removal records retain their historical draft status and
placeholder counts. Both earlier proved nodes preserve their mathematical statements and
retained certificate signatures.
