# Infrastructure audit clients

Every ordinary `.lean` file below `research/audits/` is an independent Lean client of the library:
it imports production modules and is compiled strictly (warnings are errors) by the verifier. Proof
clients state their own concrete instances and hypotheses and end in `#print axioms`; the axiom
reports a client actually prints are checked and may contain only standard axioms. A
proposition-only file compiles the same way but declares nothing, so it prints no axiom report and
proves nothing. These clients are source evidence referenced from `research/tasks.json`; they are
not ledger certificates, not library-root imports, and compiling one does not change a theorem's
status. The earlier per-client journal is not part of the published tree.

## Four kinds of file

| Kind | How to recognise it | What a passing compile means | Examples |
| --- | --- | --- | --- |
| Proof client | `…Audit.lean`; `theorem`/`example` declarations that derive every hypothesis and invoke a production theorem, ending in `#print axioms` | The invoked theorem applies to the stated concrete instance with standard axioms only | [BKL/KlsAudit.lean](BKL/KlsAudit.lean), [BakryEmeryOperatorCoreAudit.lean](BakryEmeryOperatorCoreAudit.lean), [MetricBVCheegerAudit.lean](MetricBVCheegerAudit.lean) |
| Counterexample or obstruction | A client that proves a negative statement or the failure of a dropped hypothesis | The obstruction is itself a proved local declaration; it refutes a strengthening, not the library result | [ExponentObstructionAudit.lean](ExponentObstructionAudit.lean) |
| Proposition-only candidate statement | `…RouteStatements.lean`; `#check`/type-level statements of propositions | Only that the proposition is well typed. **It is not a proof** and registers nothing | [WeightedCoareaRouteStatements.lean](WeightedCoareaRouteStatements.lean), [SharpSardRouteStatements.lean](SharpSardRouteStatements.lean), [BKL/Proposition71RouteStatements.lean](BKL/Proposition71RouteStatements.lean) |
| Separately run `.lean.in` pilot | Templates compiled by their own runner into isolated modules; not part of the ordinary client sweep | Whatever the pilot's README states: a reviewed specification, bridges and replay in its own scope | [BKL/IndependentTargets/](BKL/IndependentTargets/README.md) via `run.py`; [KLS/Classical/](KLS/Classical/README.md) via `check.py`, run by the verifier as the `classical-kls` gate |

Within a proof client, a `#check` line is still a type check. Some clients keep dated comments
about the historical rounds in which they were written, including statements that were open at
the time; those comments are records, not current status. Current status is owned by the
[paper register](../progress/LITERATURE.md) and the [certificate guide](../../solutions/README.md).

## Families

| Directory | Mathematics audited |
| --- | --- |
| [research/audits/](.) (root) | Coarea, Sard and Hausdorff slicing; Bakry–Émery, heat semigroup and Γ₂; Cheeger–Buser and the log-concave line; metric BV and Minkowski content; wave splitting, Yosida and von Neumann limits; Gaussian regularization and Borell density |
| [BKL/](BKL/) | Letwin compact bound supports, cumulant bounds, posteriors and localization, Taylor iterates, Proposition 7.1 supports, isotropic reduction and the closed KLS endpoint |
| [CEK/](CEK/) | Moment-regularity potentials and their weak-derivative supports |
| [BKL/IndependentTargets/](BKL/IndependentTargets/README.md), [KLS/Classical/](KLS/Classical/README.md) | The two `.lean.in` pilots above |

## Run one client

After building the library, from `formalization/`:

```sh
lake env lean -DwarningAsError=true ../research/audits/OpenGraphAudit.lean
```

The pilots are run through their own scripts, documented in their READMEs.

## Where the clients are checked

| Run | What it does with these files | What it does not do |
| --- | --- | --- |
| Full local verifier, `python3 research/verify.py` | Rebuilds the library into a filtered compiled view; strictly compiles **every** live `research/audits/**/*.lean` client against that view, including files outside the default Lake targets; runs the `classical-kls` gate; audits the axioms of every local declaration; replays local modules; validates `tasks.json` evidence paths and SHA-256 hashes with the atlas, the vendor provenance lock, the statement golden and the Python regressions | It does not certify candidate statements or make clients part of kernel replay |
| Remote Lean certification, `python3 research/verify.py --lean-only` (manual dispatch or a `milestone/**` tag) | Builds, strictly compiles all current `.lean` clients, runs `classical-kls`, the axiom audits and the local replay, and binds Lean sources, pinned inputs and tooling | It does **not** run the atlas/tasks metadata checks, the Python tests, the vendor-lock or the statement-golden comparison; those are full-local gates |

Client and declaration counts are snapshot-bound and are recorded in the receipts, not here; see
[receipts and trust scope](../verification.md#receipts-and-trust-scope). Adding a client means adding
the file and its `tasks.json` evidence entry; `verify.py` rejects a live audit source missing from the
Git-aware snapshot.
