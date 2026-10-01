# Formalization classification and delivery workflow

Use this workflow before adding a module, splitting an existing module, or changing a public API.
It applies across the library. [Naming conventions](naming.md) define the detailed naming and
parameter rules; [AGENTS.md](../AGENTS.md) makes the workflow part of normal project work.
Record recurring layout and naming issues in the [technical-debt register](technical-debt/README.md),
with evidence, affected consumers, and an acceptance check. Separate confirmed debt, review
candidates, and accepted exceptions; close entries only after verification.

## 0. Select a literature target

Use [the paper register](progress/LITERATURE.md) and its current source-review priorities as
the primary work plan. Before implementing a proof, identify the paper/version, theorem locator,
exact hypotheses, constants and normalization, intended Lean statement, existing supporting
declarations and verification scope. Record this in the current task or handoff. A reusable
infrastructure task must name the paper theorem it supports and the precise missing interface.

Exploratory routes in [the separate research register](explorations/ROUTES.md) are non-targets.
The Blueprint and `atlas.py` retain them for statement/dependency audits; their pending nodes
and dispatch classifications are not the current work queue. `active` in exploratory composition
means a logical branch is retained, not that its open gate should be formalized next.
Retain proved auxiliary results and conditional implications with their actual scope.

Paper coverage requires a faithfully matched main theorem, proof, registered certificate and
exact-statement verification evidence. Completed supporting declarations cannot supply a missing
main-theorem statement or certificate. Keep current handoffs short and move superseded execution
records to dated `research/decisions/` files.

## 1. Classify by mathematical responsibility

For each proposed group of declarations, identify its primary object, necessary mathematical
structure, consumers, and role. Inspect the actual statements and dependencies; neither a task
label nor an incidental import determines ownership. Do not strengthen or weaken a statement to
make it fit a directory.

| Role | Placement rule | Example |
| --- | --- | --- |
| Reusable analytic or algebraic tool | Lowest existing mathematical family that owns the object; avoid application assumptions | Hessian and directional-derivative tools in `Analysis/BakryEmery/Calculus.lean` |
| Object definition and elementary properties | The object's family, below substantial applications and estimates | Classical weighted operator in `BakryEmery/Laplacian.lean` |
| Substantive theorem or property | A topic module inside the owning family | `IntegrationByParts.lean`, `Gamma.lean`, `Bochner.lean` |
| Concrete specialization | The concrete family's module; import the abstract result | `KLS/LogConcave/HeatSemigroup/Domain.lean` |
| Identification between two objects | Place at their integration boundary, with a descriptive topic name | Closed-form normalization in `WeightedGradient/Energy.lean` |
| Counterexample or obstruction | The family of the statement being refuted; independent from the successful construction | `Semigroup/Exponential/Counterexample.lean` |
| Proof client, signature check, candidate statement | `research/audits/`; distinguish proved clients from type-checked candidates | `SemigroupDomainStabilityAudit.lean` |
| Historical rationale, route, verification record | Dated `research/decisions/`; never use it as the canonical API index | Layout decision plus an old-to-new migration map |

Reuse the existing Energy, Probability, Poincare and KLS families when they own the mathematics.
Do not move everything abstract to Analysis, or everything used by Buser to a Buser directory.
A generic result may remain in an established local family when that avoids an unjustified new
abstraction; its statements must retain their actual generality. Extract to a shared family when
real consumers establish shared ownership, rather than guessing future reuse.

## 2. Choose the dependency direction

Imports should flow from applications toward their prerequisites:

```text
concrete specialization -> abstract interface -> construction/properties -> basic tools
pointwise Gamma/Bochner -> weighted Laplacian -> differential calculus
integration by parts   -> weighted Laplacian -> differential calculus
```

These are responsibility examples, not a universal linear ordering. Identification modules may
legitimately import both sides of a bridge. Check the actual import graph for cycles and avoid
having a low-level tool import the application that first needed it.

An import of measure/integration machinery in a pointwise module, or a counterexample imported
by a successful construction, is a review signal: inspect whether the dependency is necessary.
Do not remove required imports merely to make the graph look smaller, or claim that an arbitrary
API assumption is mathematically necessary because the current implementation uses it.

## 3. Decide whether to extend, split, or create

Apply these questions in order:

1. Does an existing module have the same object, role and prerequisite level? Extend it.
2. Would the addition mix independent roles, introduce an avoidable heavy dependency, or force
   clients to import unrelated material? Split along that mathematical boundary.
3. Otherwise, create a narrowly named module in the existing owning family.
4. Create a new family directory only when the existing family rules in `naming.md` apply:
   three or more related modules, or a genuine two-module basic/extension pair. Do not make a
   directory for one isolated file. The library-root exception remains unchanged.

Line count and long basenames are review signals, not automatic splitting thresholds. A long
coherent proof can remain together; a short module can still be misplaced. `Basic.lean` must be
an actual foundational entry, not a container for whichever helper was written first.
Do not create empty `Form.lean`, `Smoothing.lean`, or future-route modules before they contain work.
One-use proof helpers should normally be private and local to the consuming module.

## 4. Name the three layers separately

| Layer | What it communicates | Avoid |
| --- | --- | --- |
| Directory | Mathematical family or established carrier/test-class distinction | Dates, milestone codes, or temporary proof plans |
| File | One responsibility or property within that family | Repeating the family name, vague `Misc`/`Utils` buckets |
| Namespace and declaration | Object context followed by a short operation/property | Restating a whole epsilon–delta formula in a theorem name |

Keep mathematical terms such as `IntegrationByParts` intact. Preserve distinctions needed to
avoid ambiguity: arbitrary weights, L1 versus L2, operator domain versus form domain, intrinsic
versus ambient space, boundary restrictions, and one-sided versus full derivatives. The full
contract belongs in the type and docstring; names must not promise a stronger result.
For example, `Generated.right_derivative` can name an epsilon–delta right-limit theorem, while
its type explicitly retains `f ∈ D(T†T)` and `t ≥ 0`.

A file move preserves its existing namespace and declarations. A namespace or public-name change
is a separate, explicitly mapped API migration. Named arguments, parameter order, visibility,
universes and assumptions are interfaces too; changes to them are not pure renames.
Do not add a conclusion-bearing structure, extra assumptions, or compatibility aliases to make
names or parameter lists shorter.

## 5. Record a small placement plan before editing

For a new module or a reorganization, record the following in the active handoff, task update,
or an existing decision record. A small local edit does not need a new standalone document.

```text
Object and role:
Exact scope / non-claims:
Existing owner and consumers:
Destination module and namespace:
Required imports / dependency direction:
Extend, split or create, and why:
Public API changes and affected clients:
Validation scope:
```

Use this as a working decision, not an additional approval gate. Proceed within the user's
existing authorization. If the intended module changes role during implementation, revisit the
placement before adding more declarations to it.

## 6. Deliver with evidence proportional to the change

| Change | Required checks |
| --- | --- |
| Documentation only | Review links, rule consistency and the scoped diff; `git diff --check`; no Lean rebuild solely for prose |
| New or changed proof | Strict compilation of affected modules and a real client, axiom audit, applicable project acceptance gates; keep pending targets separate |
| Module split/move | Save the actual dirty baseline; provide a one-to-many path and declaration-location map; update imports and clients; compare statements/definitions and run the full build and `research/verify.py` |
| Public API migration | Additionally record full old/new names, compare elaborated types and definition closures with the explicit map, check named arguments/visibility, test new names and absence of old aliases |

For proof, path or API changes, synchronize affected evidence hashes, live documentation and
Blueprint anchors. Regenerate progress views from staged canonical records as required by
`AGENTS.md`; a temporary index may preserve the user's actual staging. Compare old evidence to
the baseline before refreshing hashes. Preserve historical decisions/explorations and earlier
migration maps; add a new map instead of rewriting history. Review the full progress diagram
and current-status summary when proof status or node source paths change.

Verification receipts certify their recorded snapshots. Documentation edits after a successful
run change that snapshot; do not present the old receipt as fresh verification of the new tree.
Distinguish source checks, kernel replay, certificate registration and remote CI. File cleanup
alone never advances mathematical proof status. Preserve unrelated work; commit and push only
when authorized.

### Local pre-push gate

The tracked `.githooks/pre-push` runs the full local verifier, including `lake build`, ledger
checks and transitive axiom checks for every local declaration except the exact open target
`FunctionalInequalities.KLS.kls`. This catches dependent wrappers and is stronger than a text
search for `sorry`. It retains the full local metadata and Python checks.

Enable it for a checkout with `git config core.hooksPath .githooks`, after preserving any
existing hook configuration. Hook installation is opt-in. It verifies a clean tracked checkout
and accepts outgoing HEAD branches or tags at HEAD; check out another outgoing commit first.
Ref deletion needs no proof run. Unrelated untracked editor configuration is left alone;
untracked Lean clients still enter the verifier's source-discovery checks. The hook provides
local evidence for its recorded working snapshot, not a remote certificate.

### Remote CI at verification milestones

Ordinary branch pushes and PR updates do not run remote CI, including Lean changes. Keep the
local checks above; before milestone certification, run `python3 research/verify.py` from the
repository root and resolve failures locally. A meaningful remote run establishes clean-runner
evidence for a new certificate, a faithfully formalized paper main theorem, or a snapshot being
shared or released. Changes to the toolchain, dependencies or verification machinery can also
justify a manual reproducibility check. Do not rerun a successful unchanged SHA without a
specific verification reason.

Run Lean certification either manually with `gh workflow run lean.yml --ref <branch-or-tag>`
or by explicitly pushing a `milestone/<name>` tag for the intended commit. Choose one trigger
per milestone. Confirm the run's actual `head_sha` and conclusion before recording remote
evidence; an unrun or failed snapshot is not remotely verified. Manual dispatch becomes
available once the workflow is present on the default branch.

Lean certification is the only remote workflow. Build Blueprint PDF/web artifacts locally
when needed, following the [formalization guide](../formalization/README.md#lean-blueprint).
There is no periodic CI schedule, and `[skip ci]` is not part of this policy. Local receipts,
remote certification and Blueprint artifacts remain separate evidence.

Remote certification runs `python3 research/verify.py --lean-only`: it builds all current
library, solution and example modules, strictly compiles the independent Lean audit clients,
audits transitive axioms of all local declarations except the exact open target `KLS.kls`,
and replays the local modules in the kernel. A wrapper depending on the target is rejected.
The Lean receipt is bound to Lean sources, pinned dependencies and verification tooling;
documentation, Blueprint/task metadata, statement-baseline records and Python tests are
checked by the full local command, not remote CI. Remote success does not certify those
local metadata gates or prove KLS. Evidence artifacts contain reports, logs and generated
Lean clients; compiled module copies stay on the runner.

`research/verify.py` strictly compiles every live, nonignored `research/audits/**/*.lean`
file from the source snapshot as an independent client, including files outside the default
Lake targets. Warnings are errors, and printed axiom reports must use only standard axioms.
This gate is necessary after dependency changes even when the audit source itself is unchanged.
Audit elaboration does not certify candidate statements or add these clients to kernel replay;
local-module replay and certificate checks retain their separately reported scopes.

Before audit elaboration, rebuild the complete current library/solution/example scope and use a
fresh view containing only those modules. Replace the local build search path for audits,
statement checks and replay; invoke Lean directly so Lake cannot restore an unfiltered path.
Reject on-disk production/audit Lean sources absent from the Git-aware snapshot. Packaging
ignore rules must not suppress mathematical family directories, including on case-insensitive Git.

Keep live path directories outside preserved historical sections. Correct accidental historical
edits against their saved baseline and explain the correction in a new record. Also inspect
host-local Git exclusions: tracked ignore rules alone do not determine source visibility.

A passing receipt is not a universal library no-sorry invariant. Certificate import closures and
explicit declaration axiom audits enforce their stated scopes; kernel replay alone accepts
sorryAx. Report the observed library hole inventory separately from what the gates guarantee.
