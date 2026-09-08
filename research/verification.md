# Local verification and task atlas

The goal is to make the next formalization task and its evidence reproducible while retaining
the distinction between known mathematics, local arguments, open research, and Lean proofs.
This workflow runs locally and does not commit, push, dispatch agents, or publish artifacts.
Public interfaces remain editable under [the lifecycle](ledger-schema.md#lifecycle).

## Reading path and authorities

1. [KLS statement](../formalization/FunctionalInequalities/KLS/Statement.lean) and
   [its definitions](../formalization/FunctionalInequalities/KLS/Definitions.lean): the literal
   current target, with finite universal constant, every natural dimension, finite second
   moment, compact-set log-concavity and the intrinsic local-slope literature constant.
2. [Blueprint](../formalization/blueprint/README.md): mathematical statements and declared
   dependencies; the route sidecar owns alternative branches, adapters and pinned provenance.
3. [Ledger](a-series/ledger.yaml): the seventeen certified mathematical nodes. A compiled definition
   or conjecture declaration is not another proved ledger theorem.
4. [Task metadata](tasks.json): mathematical classification, retained assumptions, priority,
   evidence references and the retry policy. It contains no second copy of Lean proof status.
5. [Atlas exporter](atlas.py) and [verification runner](verify.py): derived navigation and
   snapshot-bound machine evidence. Neither parses informal prose to decide mathematical truth.

## Commands

Run from the repository root:

```bash
python3 research/atlas.py check
python3 research/verify.py
python3 research/atlas.py export
python3 research/atlas.py ready
python3 research/atlas.py show thm:selected-literature-constant-equivalence
```

`check` runs the existing ledger/Blueprint structural checks plus task classification, reference,
certificate coverage and cycle checks. The 87 navigation labels contain 74 mathematical nodes;
chapter labels are not tasks. Statement dependencies and those in the immediately following
proof are combined. The graph records declared dependencies, not an extraction of proof terms;
missing mathematical prerequisites can still be discovered while formalizing a node.

`verify.py` runs the Python tests, default Lake build, elaborated statement snapshot comparison,
declaration and axiom audit, and kernel
replay of every compiled module under `FunctionalInequalities`, `solutions`, and `examples`.
It copies the compiled parts of exactly the current source modules into the run's `local-olean/`
view, records their hashes, and replaces only the local entry in Lake's search path for replay.
This excludes orphaned modules and ignored duplicate artifacts in an old development cache
without deleting them. A missing current compiled module or any replay coverage mismatch fails.
Explicit prefixes are necessary: the package name `functional-inequalities` differs from the library name,
so bare `leanchecker` guesses the wrong module in this checkout. The runner clears an inherited
`LEAN_PATH` before invoking Lake, uses Lake's toolchain binary for the filtered replay, and limits
Lean worker threads to two. This view is made from the current build; it is not a source rebuild.

The generated declaration audit imports the built library and certificates, checks all Blueprint
Lean anchors, all local declarations reached by the statement snapshot, and the twenty-five named
definition checks in `solutions/StatementChecks.lean`, and inspects their transitive axioms.
Missing reports or axioms outside `propext`,
`Classical.choice`, and `Quot.sound` fail acceptance. The seventeen certificates additionally have
default-build guards. The expected certificate list comes from the existing explicit
Blueprint-to-ledger mapping; a new proved ledger node without a mapping is an error.

Each run writes immutable evidence under `build/verification/<UTC timestamp>/`, including logs,
the generated Lean audit, full printed certificate declarations, the input atlas, and a report.
`build/verification/latest.json` identifies the latest attempt, including a failed one.
The report hashes tracked and nonignored untracked source content, detects deletions, and records
HEAD separately. Sources must have identical hashes before and after verification. Editing any
source makes a prior receipt stale even when HEAD is unchanged. Build output is ignored by Git
and does not invalidate its own receipt. The input atlas saved inside a verification run predates
that run's successful receipt; export again afterwards for current dispatch actions.

`ready` lists actions and blockers. `complete` or `formalize` is available only with a passing
receipt matching the current source snapshot. Missing, failed or stale evidence produces
`verify_recorded` for a previously annotated declaration, and `verify_prerequisites` for an
unproved task whose mathematical and infrastructure prerequisites are ready. These both request
the same repository verification; neither claims a new proof. Every dispatch also records
`verification: current | required`, including tasks whose primary action is a dependency or
infrastructure action. This receipt is local workflow evidence, not a
tamper-resistant or adversarial proof-validation protocol.

To inspect changes against an earlier exported atlas:

```bash
python3 research/atlas.py diff --against build/verification/PREVIOUS_RUN/atlas.json
```

Replace `PREVIOUS_RUN` with an existing run directory. The diff reports statement text, proof,
dependency, task and declaration changes, followed by changed source files. A referenced
definition changing is visible even if the conjecture's displayed type remains identical.
This reports changes; it does not automatically classify them as stronger, weaker or equivalent.
Record changes to hypotheses, conclusions, domains or normalization in a decision entry and
check whether the original mathematical goal is still covered. No API freeze is introduced.

## Statement baseline and definition coverage

`research/StatementSnapshot.lean` inspects elaborated declarations using `pp.all` and explicit
proof printing at width 100. Starting from the seven target/domain/energy definitions, it follows
local declaration types and definition bodies, including structure constructors and their fields.
Local ownership comes from the imported module, not merely the declaration namespace. The initial
baseline covers 26 local declarations, including `literatureEnergy`, `Covariance.operator`,
`intrinsicMeasure`, the coordinate map and affine support. Adding a referenced local helper expands
the captured dependency set automatically. Theorem types are included; theorem proof bodies are
omitted. Opaque definition bodies are included. Unsafe, partial and axiom declarations fail capture.

The golden file is [statement-snapshot/golden.json](a-series/statement-snapshot/golden.json).
It records fully explicit printed types/bodies, direct references, the external leaf names, the
toolchain, Lake manifest hash and the decision establishing that baseline. Imported non-project
declarations are trust-boundary leaves covered by pinned dependencies, not recursively snapshotted
Mathlib bodies. This is a drift detector with an explicit coverage boundary, not semantic
equivalence checking, independent verification, or evidence that the target matches the literature.

The standalone command builds the target before inspecting its current declarations:

```bash
python3 research/statement_snapshot.py check
```

A missing or mismatched baseline fails; `verify.py` never regenerates it. For an intentional change,
append a decision explaining the old/new mathematical scope and whether the original goal remains
covered, or explaining a toolchain/printing-only change. Then explicitly run:

```bash
python3 research/statement_snapshot.py update --decision research/decisions/NEW-RECORD.md
```

The update requires a different nonempty decision path. Checking also verifies that the referenced
decision's bytes have not been rewritten. This enforces record linkage, not the quality of the
mathematical review. A definition change and its baseline update can be developed together under
the current evolving-interface policy. No prior freeze checkpoint is added.

Finish decision and documentation edits **before** the final verification. A decision can cite an
earlier preflight report; the final generated receipt in `build/verification/` records its own exact
source SHA256 and Git HEAD. Do not write that final hash back into a source file and claim the
receipt still matches: decisions are themselves included in the source hash.

## Atlas schema and scheduling semantics

`tasks.json` and generated atlas use schema version 2. This is a local data-schema version, not an
external Atlas product. Tasks have `policy` and a `nodes` object keyed by existing Blueprint labels.
Each entry has these fields, with `infrastructure` required for `local_argument` and `published`
and optional for `definition`. A definition may need a nontrivial construction or a
well-definedness adapter; opting into assessment does not change its mathematical classification.
Other mathematical classes still do not accept this field. This additive schema-2 extension is
recorded in [the Borell/Claude handoff](decisions/2026-09-07-borell-equivalence-claude-handoff.md).

| Field | Meaning |
| --- | --- |
| `mathematics` | `definition`, `published`, `local_argument`, `conjectural`, `refuted`, or `unknown` |
| `evidence` | References of the form `blueprint:<existing node id>`; the referenced block and route provenance identify sources |
| `assumptions` | Named open premises explicitly retained in the theorem being formalized |
| `priority` | Integer 0 through 9; smaller is earlier, not stronger evidence |
| `note` | Mathematical scope, review requirement or execution guidance |
| `infrastructure` | Assessed implementation prerequisites, independently of mathematical truth |

An infrastructure record has exactly `status`, `mathlib_revision`, `evidence` and `gaps`:

| Status | Required evidence | Scheduling when mathematical prerequisites are ready |
| --- | --- | --- |
| `unchecked` | Revision `null`, empty evidence and gaps; no assessment is claimed | `inspect_infrastructure` |
| `available` | Current Mathlib commit and nonempty source evidence; no identified gaps | `formalize`, `formalize_conditional`, or `verify_prerequisites` |
| `missing` | Current Mathlib commit, source evidence and concrete missing interfaces | `develop_infrastructure` |

Each evidence item is `{ "path": "repository-relative/source", "sha256": "content hash" }`.
Evidence files must exist inside the repository (including pinned Mathlib sources); changed bytes
or a changed Mathlib revision fail metadata validation. Reassess and update the evidence, or return
the record to `unchecked`. `available` is a documented implementation assessment, not a theorem.
`missing` may name a local adapter still to implement; it does not claim a whole field is absent
from Mathlib. A zero-length gaps list on an unchecked record does not mean no prerequisites exist.

Initial assessment is deliberately bounded: the existing Dirac checks supply the needed APIs;
the smooth-density pilot now has a proved local weighted-gradient cutoff/mollification adapter
and its source hashes are recorded as available. Mathlib already
contains `LipschitzWith.ae_differentiableAt`,
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`, and smooth approximation tools.
`HasCompactSupport.hasFDerivAt_convolution_right` differentiates a C¹ factor; it alone does not give
the desired derivative transport for a merely Lipschitz test. The smooth/literature comparison now
has eight proved local slope/gradient and finite-constant transport adapters, assessed as available
with source hashes. The new intrinsic absolute-continuity proof and general log-concave
comparison have available local adapters too. Other published/local argument task records remain explicitly unchecked; inspect `tasks.json`
for their current assessments. This is not a survey claiming Mathlib lacks SDE,
BV or spectral theory. It does not add an analytic premise to the pilot theorem.

Research, refuted and unresolved-statement classifications take precedence. Recorded declarations
retain their certification action. Missing mathematical prerequisites keep action `blocked`, while
the infrastructure record remains visible too. Missing or unchecked infrastructure never promotes
a task to proof completion or removes a retained open premise.

Every node without a Lean-certification annotation requires explicit classification. For already
annotated definitions/theorems, certification metadata is derived from Blueprint and, where
applicable, the ledger. Published inputs and agent-reviewed arguments never become Lean proofs
merely by being cited. Missing classifications fail closed. A `local_argument` may be a proof
plan or a written argument: read its note and evidence and review it before extended proof search.

The generated `build/atlas.json` joins statements, declaration anchors, source locations,
statement hashes, direct dependencies, classification, dispatch blockers, route compositions,
certificate mappings and the source snapshot. Each task key includes its node id, statement,
dependencies and the current snapshot. This deliberately conservative first implementation
invalidates tasks on any source change; finer dependency-local caching is deferred.

- `all_of` and `any_of` in the route sidecar are preserved verbatim. Repository adapters remain
  alignment metadata and never become synthetic logical edges into `conj:kls`.
- A task proving `A -> B` may retain A without a proof, once A has a built Lean statement.
  A is still a research node. A certified implication's unproved premises also block an
  unconditional downstream consumer unless explicitly retained there.
- Research nodes go to `research`; unresolved statement choices go to `clarify_statement`;
  unclassified mathematics goes to review. Refuted packages are excluded from proof search.
- A complete certificate certifies its displayed proposition; no route metadata automatically
  promotes the KLS conjecture or an open assumption.

These commands describe and validate tasks; they do not yet launch workers or implement leases.
The policy requests a pause for reassessment after three attempts on an unchanged task; no attempt
counter, automatic stopping or automatic mathematical reclassification is implemented. Coordinators must
record whether failures come from an API gap, missing known lemma, statement error, counterexample,
or research frontier in `explorations/`. A retry budget is not evidence that a statement is false.
No unattended retry executor is included in this phase.

## Borell equivalence and conditional-fiber proofs

The 2026-09-07 owner request deliberately retained seven `sorry` proofs for Claude: one
compact/Borel log-concavity equivalence and six conditional-fiber well-definedness contracts.
Claude then proved all seven. `thm:compact-borell-logconcavity-equivalence` is now a proved
ledger node with the sole certificate `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate`,
registered in `check_blueprint.CERTIFICATES`, with `\leanok` on statement and proof and
default-build axiom guards. `def:conditional-fiber-form` carries `\leanok` as a definition node
because its six contracts are proved and guarded in `StatementChecks.lean`; it is not a ledger
theorem. The declaration audit still examines every Blueprint anchor and was not relaxed:
`STANDARD_AXIOMS` is unchanged and no anchor was omitted.

Definitions may opt into an infrastructure record while retaining `mathematics: definition`,
using the same source/pin/gap validation and scheduling as other assessed tasks. The
conditional-fiber record is now `available` with no gaps. Existing theorem infrastructure
requirements are unchanged.

The statement golden still covers its original 26 declarations; the new objects do not occur
in that root closure, so no baseline update is made. New anchors, twenty-five named typed checks,
six contract guards and the certificate guards provide the stated additional coverage, without
claiming an expanded golden. Source scope is in
[the handoff decision](decisions/2026-09-07-borell-equivalence-claude-handoff.md) and the
proofs are described in
[the completion record](decisions/2026-09-07-borell-equivalence-and-conditional-fiber-proofs.md).

## Borell density representation

`thm:borell-logconcave-density` was drafted and then proved on 2026-09-07. While drafted, its
five `sorry` obligations were deliberately kept out of the Blueprint `\lean` anchors, because the
declaration audit examines every anchor for standard-only axioms and would have failed on a
placeholder rather than hidden it. Now all five theorems, the predicate `KLS.IsBorellDensity`,
the two support identities and the certificate `Solutions.ThmBorellLogconcaveDensity.certificate`
are anchored with `\leanok`, the certificate is registered in `check_blueprint.CERTIFICATES`, and
the certificate file carries default-build axiom guards for the certificate and its nine main
dependencies. Statement design and the semantic alignment review are in
[the statement decision](decisions/2026-09-07-borell-density-statements.md); the proofs are
described in [the proof record](decisions/2026-09-07-borell-density-proofs.md).

## Affine covariance Poincaré constant

`def:affine-poincare-constant` was implemented on 2026-09-07 as a definition node.
`Energy.Euclidean.covariancePreEnergy ν` has globally Lipschitz `L²(ν)` tests with integrable
`⟪Σ ∇g, ∇g⟫`, `Σ = Covariance.operator ν`; `Energy.Affine.energy μ` is its sequential relaxation
on the intrinsic law, and `Poincare.Affine.constant μ` is `Poincare.L2Energy.constant` of that
relaxation. The definition needs no log-concavity; for log-concave laws the three well-definedness
contracts of the Blueprint sentence (finite intrinsic second moment, a.e. differentiability of
tests, representative independence of the energy) are proved in
`KLS/LogConcave/AffineCovariance.lean`. Twelve anchors carry `\leanok`; the node is not a ledger
theorem, `check_blueprint.CERTIFICATES` is unchanged, and the statement golden is unchanged
because the new objects do not occur in the KLS statement closure. The definition task record is
`available` with source and Mathlib evidence hashes. Five new named checks cover the unfolding,
the test fields, the energy integral, dimension zero and the ambient Dirac law. Read
[the record](decisions/2026-09-07-affine-poincare-constant-definition.md).

## Covariance-core closure

`lem:covariance-core-closure` was proved on 2026-09-08 and is the fourteenth certificate,
`Solutions.LemCovarianceCoreClosure.certificate`, registered in `check_blueprint.CERTIFICATES`.
The Blueprint operator `T g = Σ^{1/2} ∇g` is `KLS.LogConcave.gradientOperator` with an arbitrary
continuous linear `B` in place of the square root, following the certified approximation lemma.
The certificate packages dense domain, closability, closure independence of every core between
the smooth compactly supported classes and the full domain, and the identification of the
sequential relaxation of `‖T f‖²` with `‖T̄ f‖²` on the domain of the closure and `⊤` outside.
The generic relaxation/closure identification lives in `Energy/Relaxation/LinearPMap.lean` and
is reusable for other operators. Fourteen anchors carry `\leanok` on statement and proof; the
statement golden is unchanged. Read
[the record](decisions/2026-09-08-covariance-core-closure.md).

## Affine covariance closed form

`thm:affine-covariance-relaxation-closed` was proved on 2026-09-08 and is the fifteenth
certificate, `Solutions.ThmAffineCovarianceRelaxationClosed.certificate`. Quadraticity of the
affine pre-energy is expressed through a square root `B` of the intrinsic covariance
(`Covariance.exists_sqrt`); the certificate packages dense realization, the closed quadratic form
`Energy.ClosedQuadratic (Energy.Affine.energy μ)`, the sequential core, translation of the intrinsic
law with its `L²` isometry, and the identification of the affine relaxation and constant with the
closed form on the core `ℝ + C_c^∞`. Seventeen anchors carry `\leanok` on statement and proof;
the statement golden is unchanged. Read
[the record](decisions/2026-09-08-affine-covariance-relaxation-closed.md).

## Affine constant translation invariance

`lem:affine-poincare-translation-invariance` was proved on 2026-09-08 and is the sixteenth
certificate, `Solutions.LemAffinePoincareTranslationInvariance.certificate`. The ambient translate
is `Energy.Euclidean.translateLaw μ b`; the certificate packages log-concavity of the translate,
invariance of the ambient covariance operator and of the affine-support direction, a
variance-preserving `L²` isometry intertwining the two affine relaxations, the identity
`Poincare.Affine.constant (translateLaw μ b) = Poincare.Affine.constant μ`, the ambient second
moment of a log-concave law and the zero mean of the translate by the negative barycenter. The
constant identity is proved for every Borel law. Sixteen anchors carry `\leanok` on statement and
proof; the statement golden is unchanged. Read
[the record](decisions/2026-09-08-affine-poincare-translation-invariance.md).

## Affine and isotropic KLS formulations

`thm:affine-isotropic-reduction` was proved on 2026-09-08 and is the seventeenth certificate,
`Solutions.ThmAffineIsotropicReduction.certificate`. The three statements `KLS.IsotropicBound K`,
`KLS.CovarianceBound K` and `KLS.AffineBound K` quantify over every finite-dimensional Euclidean space
of one fixed universe; the certificate packages their pairwise equivalences for every `K` and the
implication from `KLS.AffineBound K` (universe zero) to `KLS.Conjecture`. The proof centers and whitens
the intrinsic law (`Covariance.exists_whitening`), transports the covariance relaxation along
translations and continuous linear equivalences, and identifies the identity-weighted Lipschitz
gradient relaxation constant with the literature constant. Twenty-six anchors carry `\leanok` on
statement and proof; the route sidecar claim for the node is `proved` with Lean evidence; the
statement golden is unchanged. The same inspection records `thm:cmh-recovery-affine-poincare-bound`
as `missing` infrastructure with four concrete gaps. Read
[the record](decisions/2026-09-08-affine-isotropic-reduction.md).

## Definition checks

Default-build named checks cover constant admissibility/zero energy in every allowed dimension,
zero-dimensional covariance and the literal inequality for every finite C, local slope of the real
identity equal to one, and ambient identity energy one under a Dirac law. Each has a transitive
axiom guard and is also audited by the runner. The nonzero examples test the energy normalization;
the intrinsic literature constant uses the affine carrier, not the ambient raw identity energy.

Existing raw representative tests in `examples/PoincareFoundation.lean` and Gaussian transfer
checks in `solutions/LemLegacyRelaxedPoincareComparison.lean` remain the reusable coverage for those
contracts. The smooth/locally-Lipschitz comparison is now proved under intrinsic absolute
continuity; a concrete Gaussian literature specialization must still discharge that premise.
No placeholder is added for it. A bare `#check P` only checks
that P is a well-formed expression; acceptance uses proof terms with the expected proposition or
proved named theorems, followed by transitive axiom inspection.

## Pilot and falsification

The first priority is `lem:covariance-test-core-density`, then the smooth/locally-Lipschitz
comparison and selected/literature comparison; all three are now certified. The intrinsic
absolute-continuity input and the stronger Borell density/moment representation are separately
certified. The written arguments are in Blueprint Appendix A and the shared
bridges chapter; the weighted gradient approximation is not supplied by ordinary value-only
smooth density in L². Formalizers must identify or construct that analytic step explicitly.
The pipeline does not require the more general, unresolved Cheeger-energy identification.

Review new statements against the existing Dirac and normal-direction obstructions, zero
dimension, empty products, zero energy, infinite optimal constants, and Gaussian variance
normalization. Numerical tests are counterexample leads, not proofs or assurances of truth.
Formalizer/prover roles may be combined. A coordinator owns task selection and integration;
a reviewer checks scope and evidence; a falsifier checks boundary cases; a researcher handles
the explicit open gates. These are responsibilities, not six required persistent agents.

The approximation input has its own seventh certificate, and the smooth/literature comparison
under intrinsic absolute continuity has the eighth. Intrinsic absolute continuity from
compact-set log-concavity and the general constant equality now have the ninth and tenth.
The full Borell density/moment representation was subsequently certified as the twelfth node.
The original eight ledger claims were unchanged by the ninth and tenth additions; see the
[general proof record](decisions/2026-09-06-general-logconcave-comparison.md),
[approximation acceptance](decisions/2026-09-06-weighted-approximation-acceptance.md) and
[comparison proofs](decisions/2026-09-06-smooth-literature-proofs.md).

## Trust and release boundary

The kernel replay checks local module declarations using already compiled imported environments.
Pinned third-party compiled imports remain trusted; this is not `--fresh`, independent checker
verification, or a clean-source reconstruction. Comparator, an external checker, and isolated
release rebuilding are deferred. Ordinary draft modules may contain placeholders under the
ledger lifecycle; certification and axiom checks reject them in the audited claims' dependencies.

CI uses the same verification runner and uploads evidence as workflow artifacts. Editing its
configuration locally does not run remote CI or publish any source. No successful CI run or
remote publication is claimed by a local receipt.
