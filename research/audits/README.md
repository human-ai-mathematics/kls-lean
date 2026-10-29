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
| Proof client | `…Audit.lean`; `theorem`/`example` declarations that derive every hypothesis and invoke a production theorem, ending in `#print axioms` | The invoked theorem applies to the stated concrete instance with standard axioms only | [BKL/KlsAudit.lean](BKL/KlsAudit.lean), [BakryEmery/OperatorCoreAudit.lean](BakryEmery/OperatorCoreAudit.lean), [MetricBV/CheegerAudit.lean](MetricBV/CheegerAudit.lean) |
| Counterexample or obstruction | A client that proves a negative statement or the failure of a dropped hypothesis | The obstruction is itself a proved local declaration; it refutes a strengthening, not the library result | [Vector/ExponentObstructionAudit.lean](Vector/ExponentObstructionAudit.lean) |
| Proposition-only candidate statement | `…RouteStatements.lean`; `#check`/type-level statements of propositions | Only that the proposition is well typed. **It is not a proof** and registers nothing | [Coarea/WeightedRouteStatements.lean](Coarea/WeightedRouteStatements.lean), [Sard/SharpRouteStatements.lean](Sard/SharpRouteStatements.lean), [BKL/Proposition71RouteStatements.lean](BKL/Proposition71RouteStatements.lean) |
| Separately run `.lean.in` pilot | Templates compiled by their own runner into isolated modules; not part of the ordinary client sweep | Whatever the pilot's README states: a reviewed specification, bridges and replay in its own scope | [BKL/IndependentTargets/](BKL/IndependentTargets/README.md) via `run.py`; [KLS/Classical/](KLS/Classical/README.md) via `check.py`, run by the verifier as the `classical-kls` gate |

Within a proof client, a `#check` line is still a type check. Client comments describe the
checked statements, not current status. Current status is owned by the
[paper register](../progress/LITERATURE.md) and the [certificate guide](../../solutions/README.md).

## Families

Clients live in one directory per audited family or paper; no client sits directly in
`research/audits/`. A directory carries the family or paper name, so basenames keep only the
distinguishing terms, plus the kind suffix (`Audit`, `RouteStatements`) where the directory uses it.

| Directory | Mathematics audited |
| --- | --- |
| [Semigroup/](Semigroup/) | Abstract semigroup generation, exponential limits and contraction, resolvent limits, Yosida families and limits, von Neumann `T*T` and the generated semigroup, with their route statements |
| [HeatSemigroup/](HeatSemigroup/) | The log-concave heat semigroup `P_t`: construction, Markov property, domain and form-domain stability, smoothing, almost-everywhere and chain-rule passages, Gaussian profiles, spectral decay, the π coefficient and the Buser bridge |
| [BakryEmery/](BakryEmery/) | Bakry–Émery calculus: Γ, Γ₂ and Bochner, generator identification, operator core, interior regularity, gradient estimates, reverse self-improvement, ergodicity and the heat-test class, with the interface route statements |
| [WaveSplitting/](WaveSplitting/) | Wave splitting: finite construction, energy, weighted energy, residual, consistency, stability, localization, time averages and error bounds |
| [MetricBV/](MetricBV/) | Metric BV and Minkowski content: definition classes, local L¹ and Lipschitz relaxations, recovery sequences, support restriction, complements, lower semicontinuity and the BV Cheeger identification |
| [Coarea/](Coarea/) | Scalar coarea formulas (regular, smooth, Lipschitz, locally Lipschitz, weighted) and the isoperimetry bridge |
| [Sard/](Sard/) | Planar, equidimensional and sharp finite-regularity Sard theorems |
| [Hausdorff/](Hausdorff/) | Hausdorff slicing: Borel, compact and critical slices, null slicing, level-set measurability and the Eilenberg majorant |
| [Whitney/](Whitney/) | First-order jets and the compact Whitney construction and extension |
| [Graph/](Graph/) | Graph Jacobians, open-graph integrals and the linear area formula, with the area-formula route statements |
| [Vector/](Vector/) | The codimension-`m` coarea program: graphs, fibre integrals, regular charts, slicing, rank stratification and rank-deficient coarea, Lipschitz and locally Lipschitz vector coarea, with the exponent obstruction |
| [Cheeger/](Cheeger/) | Cheeger equality, inequality and infimum, and the Buser route statements |
| [Line/](Line/) | The one-dimensional log-concave line: Buser bound, Gaussian profile and Gaussian regularization |
| [Density/](Density/) | Borell density continuity and log-concavity, convolution log-concavity and Gaussian smoothing, approximation and regularity |
| [Energy/](Energy/) | Euclidean slope energies: comparison, density and recovery, with their route statements |
| [Poincare/](Poincare/) | The Klartag density-frontend literature Poincaré identification and its route statements |
| [IteratedDerivative/](IteratedDerivative/) | Schauder supports: coefficient freezing (`CoefficientFreezingAudit.lean`), the quotient-limit and radius-absorption tools (`SchauderToolsAudit.lean`), affine derivative scaling with local cutoffs and local Hessian interpolation |
| [BKL/](BKL/) | Letwin compact bound supports (including the matrix trace-integral coefficient, `MatrixTraceIntegralCoefficientAudit.lean`), cumulant bounds, posteriors and localization, Taylor iterates, Proposition 7.1 supports, isotropic reduction and the closed KLS endpoint |
| [CEK/](CEK/) | Moment-regularity potentials and their weak-derivative supports; same-witness difference-quotient equations (`DifferenceQuotientAudit.lean`); uniformly elliptic difference-quotient equations with λ, Λ and the W(∇u) forcing at one witness (`EllipticityAudit.lean`) |
| [Newtonian/](Newtonian/) | Gilbarg–Trudinger Chapter 4 potential theory: Lemma 4.2 representation, Theorem 4.5 compact Poisson estimates (planar bump and spatial signed clients), and the harmonic half of Theorem 4.6 (planar trace-zero quadratic) |
| [Letwin/](Letwin/) | The first Schauder bootstrap step and the C³ regular moment potential (`BootstrapThree.lean`); Letwin Theorem 1.2 without compact support, Lemma A.1 regular approximation (alternate Theorem 1.2 derivation, finite polynomial sums), the weak regular-class target Stein kernel (restated support statements, same-witness prefixes), the directional weak subsolution with local coefficient bounds, actual rough square/log/power tests, uniform Caccioppoli/energy-variable/weak Sobolev data (one witness, then each compact S, then every direction and cutoff), and the Moser inputs at ONE witness (log and power energies, dyadic cutoffs, normalized-ball L^p limit, n = 2 finite exponents), the actual log-gradient all-ball Morrey bound with the exponential integrability of its critical potential at one witness, one global-class dyadic gain step, and the actual local deficit (cap only on B_4R) with local log energy, one weak log extension, buffered B_3R Morrey and critical-potential exponential integrability at one witness, the actual local John–Nirenberg and power moments per R, the fixed-compact joint inputs with uniform-exponent JN moments inside the same extension, and, in a final section of `Caccioppoli.lean`, the bounded actual weak Harnack products for n > 2, n = 2 and n = 1 and the all-dimension essential-infimum weak Harnack at one fixed-compact witness, and the given-data weak Harnack applied at ONE regular moment potential retaining all its regular-class data; `HessianHolder.lean`: from the original inputs, one regular moment potential with gradient transport, C², a locally Hölder Hessian and the everywhere log-determinant equation with positive definite Hessian and cap; `GradientInverse.lean`: from the original inputs, the same potential with transport, C², positive definite Hessian, a homeomorphism ∇u : ℝⁿ ≃ₜ int K and a C¹ inverse on int K |
| [Klartag/](Klartag/) | Klartag arXiv:1309.2767v1 supports: transport and dual Laplacians, power supersolutions, generator and Hessian bounds, linear growth and moment limits |
| [Elliptic/](Elliptic/) | Elliptic operators, maximum principles and log/radial barriers (`Analysis/Elliptic/`) |
| [SourceLayout/](SourceLayout/) | Layout and migration guards: module-closure and private-merger checks for reorganized owners |
| [StochasticCalculus/](StochasticCalculus/) | Clients of the vendored `LevyStochCalc` martingale regularization interfaces |
| [KLS/](KLS/) | Completed-chain scope audit; the `Comparator/` and `Classical/` pilots |
| [BKL/IndependentTargets/](BKL/IndependentTargets/README.md), [KLS/Classical/](KLS/Classical/README.md) | The two `.lean.in` pilots above |

## Run one client

After building the library, from `formalization/`:

```sh
lake env lean -DwarningAsError=true ../research/audits/Graph/OpenIntegralAudit.lean
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
