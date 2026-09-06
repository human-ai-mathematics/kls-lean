# Verification and task scheduling closeout

Date: 2026-09-06, Asia/Shanghai.

## Goal and authorization

The owner accepted the prompt review with “可以，那就按照你的判断去执行”. This is a bounded
local extension of the existing infrastructure. Existing implementation is reused. No commit,
push, remote execution, API freeze, automatic worker or mathematical-state promotion is included.
New infrastructure files may be explicitly staged locally; staging is not a commit or publication.
Unrelated working-tree changes and existing decisions/explorations remain untouched.

Read `research/verification.md`, then the snapshot tool, task schema and definition checks.
The earlier local-atlas decision remains historical evidence; it is not rewritten by this record.

## Statement baseline and scope review

The initial golden is established by this decision. No target or domain definition is changed.
The current statement chooses one finite nonnegative constant before all natural dimensions and
all probability laws with compact-set log-concavity and finite second moment. It uses the squared
pointwise local-slope energy on the intrinsic affine law, without a factor one half, and compares
the optimal constant with the norm of the centered covariance operator. Dimension zero and
zero-energy tests remain included. KLS remains an unproved proposition.

The agent's inspection checks the encoding against its current documented contract; this does
not assert human mathematical approval, equivalence with every literature formulation, or a proof
of the conjecture. The source target and definitions are byte-identical to the starting snapshot.

`StatementSnapshot.lean` traverses elaborated local types and definition bodies, including
structure constructors. It discovers 26 local declarations from the target, including the energy,
covariance and affine-coordinate dependencies omitted by a root-only print. Theorem types are
retained; theorem proof bodies are excluded. External declarations are explicit trust leaves.
The golden also records toolchain, manifest and this decision's hash. Printing truncation fails.

Normal verification compares without updating. An explicit update needs a new decision path
describing mathematical changes, original-goal coverage, or a printing/toolchain-only change.
This is a change detector and record-linkage rule, not semantic-equivalence certification.

## Scheduling and implementation evidence

Tasks and generated atlas now use local schema version 2. Missing, failed and stale verification
distinguish `verify_recorded` from `verify_prerequisites`. Dispatch also carries a separate
verification field, so a dependency or infrastructure action cannot imply a verified snapshot.

Each explicit published/local-argument record has infrastructure status, Mathlib revision, source
evidence hashes and concrete gaps. `available`, `missing` and `unchecked` are independent of
mathematical classification. Dependency blockers retain their own action and their infrastructure
details. Open premises remain attached to conditional tasks, and research/refuted nodes retain
their existing routing. Three-attempt reassessment is policy only; no counter or executor exists.

The initial assessment covers two tasks. Existing Dirac examples provide the required APIs.
The smooth-density pilot needs a local weighted-gradient cutoff/mollification adapter.
Mathlib already supplies Rademacher, almost-everywhere convolution approximation and value
smoothing; the inspected C1 convolution derivative theorem alone does not supply the desired
Lipschitz weak-gradient transport. Evidence pins the relevant source files at Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`; that dependency checkout was clean when inspected.
The other 25 explicit published/local-argument records are unchecked. This is not an exhaustive
absence claim about Mathlib, and no unproved approximation is smuggled into the target definition.

## Definition sanity checks

Six named checks cover constant admissibility and zero energy in all allowed coordinate spaces,
zero-dimensional covariance, the literal inequality in dimension zero for every finite C,
real identity slope one, and ambient identity energy one at a Dirac atom. Each has a default-build
transitive axiom guard and is included in the verification runner's audit. The nonzero check
specifically protects normalization beyond constant/zero-dimensional examples.

Existing raw Dirac representative checks and Gaussian-to-intrinsic-smooth-relaxation checks are
reused. A Gaussian literature-constant bound still needs the smooth/locally-Lipschitz comparison.
That proposition can be stated, but its proof does not follow from the currently certified bridges.
No placeholder or seventh ledger certificate is introduced.

## Evidence, order of operations and publication boundary

Git HEAD during implementation: `70ca1c19c4d207a31716c2e589c0b096521a5490`.
The existing pre-task full receipt was
`build/verification/20260906T105746.717894Z/report.json`, for working-tree source SHA256
`60a4b7fab2854ed43004d6d57a0b52bd13d5d7486a0048806ad309f5e5f418f5`.
It was checked against the starting tree; it does not validate these subsequent changes.

Implementation preflight at source SHA256
`538c9393c94be61b570fe630dfe9bbeba9e4b54762791d228b3e9b9ad5b06f68` passed 97 Python tests,
the `solutions.StatementChecks` build, and inspection of all six new checks' axiom reports:
only `propext`, `Classical.choice` and `Quot.sound`. The tests include real Lean fixtures in which
an unchanged root print hides a changed helper through a structure field; the dependency snapshot
detects that change and newly referenced helpers. They also cover missing/malformed golden,
explicit update records, stale evidence and infrastructure/conditionality interactions.

This record, the final guards and documentation precede the final full verification. After creating
the golden, run `python3 research/verify.py`, then export and query the atlas. The immutable generated
report under `build/verification/` is authoritative for that final run's status, source SHA256,
Git HEAD, commands, logs and replay coverage. The final response links its exact path. Do not write
that final hash back into this decision: doing so would invalidate the snapshot it describes.

The final run is not predeclared passed here. It must check structural metadata, tests, default
build, golden comparison, every covered declaration's axioms and all current local compiled modules.
The local CI configuration already calls this runner; no duplicate pipeline is added.
No new remote CI execution, commit or push has been performed or claimed. Isolated source rebuilding,
fresh third-party replay and independent external checking remain unperformed. Third-party compiled
imports remain trusted. The mathematical pilot itself remains unformalized.
