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
| [research/audits/](.) (root) | Coefficient freezing (`CoefficientFreezingAudit.lean`), the quotient-limit and radius-absorption tools (`SchauderToolsAudit.lean`); Coarea, Sard and Hausdorff slicing; Bakry–Émery, heat semigroup and Γ₂; Cheeger–Buser and the log-concave line; metric BV and Minkowski content; wave splitting, Yosida and von Neumann limits; Gaussian regularization and Borell density; affine derivative scaling with local cutoffs and local Hessian interpolation (Schauder supports) |
| [BKL/](BKL/) | Letwin compact bound supports, cumulant bounds, posteriors and localization, Taylor iterates, Proposition 7.1 supports, isotropic reduction and the closed KLS endpoint |
| [CEK/](CEK/) | Moment-regularity potentials and their weak-derivative supports; same-witness difference-quotient equations (`DifferenceQuotientAudit.lean`); uniformly elliptic difference-quotient equations with λ, Λ and the W(∇u) forcing at one witness (`EllipticityAudit.lean`) |
| [Newtonian/](Newtonian/) | Gilbarg–Trudinger Chapter 4 potential theory: Lemma 4.2 representation, Theorem 4.5 compact Poisson estimates (planar bump and spatial signed clients), and the harmonic half of Theorem 4.6 (planar trace-zero quadratic) |
| [Letwin/](Letwin/) | The first Schauder bootstrap step and the C³ regular moment potential (`BootstrapThree.lean`); Letwin Theorem 1.2 without compact support, Lemma A.1 regular approximation (alternate Theorem 1.2 derivation, finite polynomial sums), the weak regular-class target Stein kernel (frozen support statements, same-witness prefixes), the directional weak subsolution with local coefficient bounds, actual rough square/log/power tests, uniform Caccioppoli/energy-variable/weak Sobolev data (one witness, then each compact S, then every direction and cutoff), and the Moser inputs at ONE witness (log and power energies, dyadic cutoffs, normalized-ball L^p limit, n = 2 finite exponents), the actual log-gradient all-ball Morrey bound with the exponential integrability of its critical potential at one witness, one global-class dyadic gain step, and the actual local deficit (cap only on B_4R) with local log energy, one weak log extension, buffered B_3R Morrey and critical-potential exponential integrability at one witness, the actual local John–Nirenberg and power moments per R, the fixed-compact joint inputs with uniform-exponent JN moments inside the same extension, and, in a final section of `Caccioppoli.lean`, the bounded actual weak Harnack products for n > 2, n = 2 and n = 1 and the all-dimension essential-infimum weak Harnack at one fixed-compact witness, and the given-data weak Harnack applied at ONE regular moment potential retaining all its regular-class data; `HessianHolder.lean`: from the original inputs, one regular moment potential with gradient transport, C², a locally Hölder Hessian and the everywhere log-determinant equation with positive definite Hessian and cap; `GradientInverse.lean`: from the original inputs, the same potential with transport, C², positive definite Hessian, a homeomorphism ∇u : ℝⁿ ≃ₜ int K and a C¹ inverse on int K |
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
