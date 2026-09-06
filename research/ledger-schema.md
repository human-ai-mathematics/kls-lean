# Statement lifecycle and Lean certification ledger

The production ledger is `research/a-series/ledger.yaml`. It uses JSON syntax (a subset of
YAML 1.2), so the checker requires only Python 3.11 or newer and its standard library.

The top-level object contains `meta.program` (exactly `a-series`), `meta.scope` (nonempty prose),
and `nodes` (an array of unique nodes). Every node contains `id`, `kind` (currently `lemma`),
`status`, `statement`, `lean_solution`, and `checked_by`. `source` is optional provenance prose.
The existing `lem:linear-test-lower` node remains required. It,
`lem:poincare-tensorization`, `lem:poincare-finite-tensorization`, and
`lem:poincare-gaussian-one-dimensional` are recorded as `proved` with `checked_by: lean`.

## Lifecycle

The repository is in an exploratory stage. Public Lean interfaces may evolve, including those
of proved nodes; there is no default backward-compatibility promise or mandatory freeze stage.
Proof work may begin while a statement is being refined. New nodes normally move directly from
`drafted` to `proved` once the current statement, proof, and certification evidence agree.

| Status | Meaning | `checked_by` | Lean artifact |
| --- | --- | --- | --- |
| `drafted` | Current statement under development or awaiting a complete proof | `null` | Compilable declaration skeleton; placeholders allowed |
| `proved` | Current statement has a completed proof and certification | `"lean"` | No forbidden escape tokens in the artifact or its local imports |
| `frozen` | Historical human-reviewed statement snapshot, still accepted by the checker | `null` | Compilable unproved declaration; placeholders allowed |

`frozen` is not used as a required stage for new work. Earlier freeze and acceptance records
remain dated review evidence, not permanent restrictions on public signatures. No per-node API
stability field is needed: interface evolution is the repository default. An explicit stability
commitment may be introduced later for selected mature interfaces.

`proved`, `checked_by: lean`, and Blueprint `\leanok` certify the current statement and proof;
they do not freeze an interface. When renaming declarations, reorganizing parameters, or
refactoring modules, migrate the affected consumers directly and rerun the relevant checks.
Changes to hypotheses, conclusions, test domains, or normalization must also be recorded in a
new decision or exploration entry and reflected in the ledger, Blueprint, certificates, and
consumers as applicable. Check whether the original mathematical goal is still covered; a
stronger hypothesis or weaker conclusion must not be hidden by a successful build. If the revised
statement lacks a complete proof, record it as `drafted` with `checked_by: null` and remove its
Lean-certification claims until it is proved again.

The checker validates a snapshot; it does not infer human approval or enforce transition history.
A green skeleton build is not proof certification. Mathematical review and transitive axiom
inspection remain part of certification, without a separate mandatory freeze checkpoint.

The public KLS target additionally has a definition-dependency golden under
`research/a-series/statement-snapshot/`. This records a reviewed statement baseline, not a ledger
certificate or a permanent signature lock. Intentional baseline changes require a new nonempty
`research/decisions/` record explaining mathematical scope changes and whether the original goal
is still covered; toolchain or printing-only changes must be identified as such. Update it explicitly
with `python3 research/statement_snapshot.py update --decision research/decisions/NEW-RECORD.md`.
Normal verification only compares and fails on drift. The checker verifies the decision's content
hash and requires a new decision path for an update; it cannot judge the adequacy of the review.
See [verification.md](verification.md) for the local definition closure, external trust leaves and
the rule to finish source/decision edits before final verification. Existing historical records
remain append-only. This rule does not require a freeze before developing an interface change.

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

The [local verification runner](verification.md) joins this ledger with the existing explicit
Blueprint certificate mapping and fails if a proved node has no mapping for axiom inspection.
It requires a report for every mapped certificate, audits all Blueprint Lean anchors, replays
the local compiled modules, and ties the results to actual source hashes. All seven current
certificates also retain default-build axiom guards. The generated task atlas derives these
statuses; `tasks.json` does not own or duplicate certification state.

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

## One-dimensional Gaussian acceptance (2026-09-04)

Node `lem:poincare-gaussian-one-dimensional` uses
`lean_solution: solutions/LemPoincareGaussianOneDimensional.lean`, with `status: proved` and
`checked_by: lean` after human semantic approval and proof closeout. Its sole named certificate
packages the valid-constant and exact-optimal-constant conclusions for every mean and every
nonnegative variance. The same default-build entry point checks all 20 supporting public
declarations and the boundary applications. `solutions/GaussianAxiomAudit.lean` additionally
makes the certificate's exact transitive axiom set a default-build obligation.

The approved contract and the two generalized tail interfaces are recorded in
`decisions/2026-09-04-gaussian-poincare-freeze.md`; the final architecture, semantic review,
proof-escape checks, axiom audit and local machine gates are recorded in
`explorations/2026-09-04-gaussian-poincare-acceptance.md`. Earlier candidate, design, signature
and statement-validation records remain unchanged and retain their historical `drafted` state.
No schema, checker or regression-test exemption was introduced for this promotion.

## Comparison certificates (2026-09-06)

`lem:ambient-intrinsic-poincare-comparison` and `lem:legacy-relaxed-poincare-comparison`
are now `proved` with `checked_by: lean`. Their named certificates package all five and seven
reviewed conclusions respectively. The owner authorized proof work after the external-review
assessment; the 12 theorem signatures are unchanged. The approval, semantic boundaries and
local proof audits are recorded in `decisions/2026-09-06-poincare-comparison-proofs.md`.
The earlier draft record is preserved. That comparison batch brought the ledger to six certified nodes.

## Weighted approximation acceptance (2026-09-06)

`lem:covariance-test-core-density` adds the seventh proved node. Its sole certificate packages
all four original contracts; both certificate and reusable theorems retain default-build axiom
guards. The existing Blueprint mapping includes this node directly, without another graph node
or checker exemption. See [the acceptance record](decisions/2026-09-06-weighted-approximation-acceptance.md).

## Smooth/literature comparison acceptance (2026-09-06)

`thm:smooth-lipschitz-constant-equivalence` is the eighth proved node. Its sole certificate
packages all eight proved interfaces with individual quantifiers; each component and the
certificate have default-build axiom guards. The comparison retains intrinsic absolute continuity,
so the general log-concave comparison and Borell node remain uncertified. The a.e. slope and
extended-energy declarations omit a redundant second-countable instance, covering the original
scope. See [the proof record](decisions/2026-09-06-smooth-literature-proofs.md).
