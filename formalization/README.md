# Lean formalization

Reusable mathematics is organized by topic under `FunctionalInequalities/`.
Each ledger node has one entry point in repository-root `solutions/`, importing the mathematics
directly. There is no intermediate project-specific wrapper layer.

Public interfaces may evolve, including those of proved results. Proof work may refine a draft
without a prior freeze; certification applies to the current statement and proof. Migrate
affected consumers directly and document changes to mathematical scope. The
[lifecycle guide](../research/ledger-schema.md#lifecycle) is the current policy; earlier freeze
records preserve dated reviews rather than a default compatibility promise.

Downstream applications, examples, and smoke tests may start from
[`Poincare/Foundation.lean`](FunctionalInequalities/Poincare/Foundation.lean). Reusable library
modules must instead import their exact direct dependencies so the direction below remains
acyclic. The foundation's
[mathematical guide](FunctionalInequalities/Poincare/README.md) records the `L²`, extended-energy,
relaxation, closed-form, Dirichlet, and pure-optimization layers and distinguishes them from the
accepted smooth-test API.

For a first concrete application, read
[`examples/PoincareFoundation.lean`](../examples/PoincareFoundation.lean). Its examples are compiled
by the default `Examples` target and cover arbitrary laws, the selected energy, singular raw
tests, infinite relaxation, and the accepted Gaussian constants.

## Certified and WIP boundaries (2026-09-12)

The current ledger records 24 certified nodes. The aggregate and certificate imports exclude the
four WIP modules, which retain 24 explicit `sorry` bodies (5 perimeter, 9 Cheeger-infimum,
5 analytic prerequisites, 5 singular-law Cheeger comparisons). Some WIP results without a direct
hole still depend transitively on `sorryAx`. Ordinary elaboration is allowed to warn on these
files; warnings-as-errors is expected to reject their remaining holes. The owner retains them
for later work. See the [audit record](../research/decisions/2026-09-12-status-audit-and-wip-retention.md) for existing inputs,
remaining geometric-analysis proofs and the still-open uniform KLS bound.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](../research/naming.md) and [the migration record](../research/decisions/2026-09-08-mathematical-api-organization.md).


## Source map

The literal target is in [`KLS/Statement.lean`](FunctionalInequalities/KLS/Statement.lean), with
compact-set log-concavity and the intrinsic local-slope literature constant in
[`KLS/Definitions.lean`](FunctionalInequalities/KLS/Definitions.lean). These modules define the
current conjecture and do not prove it. They share the existing covariance operator through
[`Probability/Covariance.lean`](FunctionalInequalities/Probability/Covariance.lean).
[`StatementChecks.lean`](../solutions/StatementChecks.lean) checks the expanded target and
constant-function/zero-dimensional boundary encodings in the default build.
The [local workflow](../research/verification.md) adds task selection and snapshot-bound evidence.

```text
formalization/
├── FunctionalInequalities.lean     # Aggregate: definitions, proved results and drafts
├── FunctionalInequalities/
│   ├── Probability/               # Probability laws, affine support, covariance, ball estimates
│   ├── L2/                        # Mean and variance on real L²
│   ├── Energy/                    # Extended energies, relaxation and Euclidean realizations
│   ├── Poincare/                  # Constants, comparisons, products and Gaussian models
│   └── KLS/                       # Target definitions, log-concavity and route-specific objects
├── Dev/                           # Optional search scratchpad; not a Lake library, never built
├── blueprint/                     # TeX sources, dependency routes and rendering tools
├── lakefile.toml                   # Library, solution, example and development targets
├── lake-manifest.json              # Pinned dependencies
├── lean-toolchain                 # Lean version
└── README.md
```

This is a topic map, not an exhaustive file listing. Use the subject guides for detailed
reading order and placement rules:

| Topic | Entry points and guide |
| --- | --- |
| Probability | [Basic](FunctionalInequalities/Probability/Basic.lean), [AffineSupport](FunctionalInequalities/Probability/AffineSupport.lean), [IntrinsicCovariance](FunctionalInequalities/Probability/IntrinsicCovariance.lean), [Covariance](FunctionalInequalities/Probability/Covariance.lean), [CovarianceSqrt](FunctionalInequalities/Probability/CovarianceFactorization.lean), [CovarianceWhitening](FunctionalInequalities/Probability/CovarianceWhitening.lean), [BallDomination](FunctionalInequalities/Probability/BallDomination.lean), [BallAverages](FunctionalInequalities/Probability/BallAverages.lean), [TwoPointVariance](FunctionalInequalities/Probability/TwoPointVariance.lean) |
| Real L² | [MeanVariance](FunctionalInequalities/L2/MeanVariance.lean) |
| Energy | [Guide](FunctionalInequalities/Energy/README.md): general interfaces, `Relaxation/`, and `Euclidean/` |
| Poincaré | [Foundation guide](FunctionalInequalities/Poincare/README.md), [Euclidean comparisons](FunctionalInequalities/Poincare/Euclidean/README.md), [affine covariance constant](FunctionalInequalities/Poincare/CovarianceGradient/Intrinsic.lean), [its ambient translation invariance](FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean), [Lipschitz/literature bridge](FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean), [Gaussian guide](FunctionalInequalities/Poincare/Gaussian/README.md); product modules are in `Poincare/Product/` and `Poincare/FiniteProduct/` |
| KLS | [Guide](FunctionalInequalities/KLS/README.md), including [log-concavity](FunctionalInequalities/KLS/LogConcave/README.md), isotropy, isoperimetry, conditional fibers and their Dirichlet form (`KLS/ConditionalFiber/Closed.lean`), the explicit slice kernel and the log-concave fiber input `κ = 4`, the log-concave contracts of the affine covariance constant, log-concavity under ambient translation and the affine/isotropic reduction of KLS |
| Blueprint | [Build and navigation guide](blueprint/README.md) |

The root aggregate also imports the Borell representation module. Successful aggregate
compilation alone does not certify anything. Proved certificates import their specific
dependencies and are checked separately; the [ledger](../research/a-series/ledger.yaml)
records their status. Development search commands stay in `Dev/Search.lean`.


Import the module needed by the argument, for example:

```lean
import FunctionalInequalities.Poincare.SmoothTest.Basic
-- For downstream applications using L² and extended energies:
import FunctionalInequalities.Poincare.Foundation
import FunctionalInequalities.Poincare.Product.Tensorization
-- For finite-product tensorization and optimal equality:
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
-- For the sharp one-dimensional Gaussian constant:
import FunctionalInequalities.Poincare.Gaussian.Real
```

The module hierarchy locates files; declaration namespaces remain unchanged. In particular,
theorems still use `FunctionalInequalities.Poincare`, variance helpers use
`FunctionalInequalities.ProductVariance`, and covariance definitions use
`FunctionalInequalities.Covariance`.

### New foundation: exact proof boundary

The live foundation now proves the complete closed-quadratic chain, not merely a proposed
interface:

- `PreEnergy.Quadratic` packages a linear realization and finite quadratic energy.
- Sequential relaxation is lower semicontinuous in every pseudometric ambient space. Every
  finite-energy point has a recovery sequence; dense realization gives recovery at every point,
  including points with value `⊤`.
- `PreEnergy.Quadratic.closedQuadratic_sequentialRelaxation` proves that a quadratic pre-energy
  with dense realization has a full `ClosedQuadratic` sequential relaxation, including the
  extended parallelogram identity.
- `Energy.SmoothGradient.relaxation_closedQuadratic` instantiates this result for the finite-dimensional
  Borel `C∞` gradient pre-energy. `Energy.SmoothGradient.Intrinsic.closedQuadratic`
  transports it through affine-support coordinates.
- `affineSupport` is the smallest closed affine subspace containing almost every point.
  `intrinsicL2Equiv` is a two-sided real linear isometric equivalence between the original and
  intrinsic real `L²` spaces, rather than a one-way embedding.
- `Energy.Relaxation.Contraction` gives a conditional transfer theorem: a continuous map satisfying
  `RelaxedContractionBound` on realized tests decreases relaxed energy everywhere.
- `Poincare.SmoothGradient.Intrinsic` exposes `Holds`, the optimal `ENNReal` constant, and their
  exact order-theoretic equivalence for the intrinsic-affine relaxed energy.
- The proved comparison modules identify ambient and intrinsic-affine relaxed energies, preserve
  arbitrary pre-energy Poincare constants under relaxation, and identify the finite-dimensional
  smooth-test constant with the selected canonical constant.

In Mathlib v4.33 ordinary `C∞` regularity is `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` is analytic. Both the
accepted smooth tests and the new smooth-gradient tests use `∞`.

The foundation now provides the Markov/Dirichlet witness for the smooth relaxation and its
intrinsic-affine pullback (`Energy/SmoothGradient/Dirichlet.lean`), and the one-dimensional
log-concave bound `C_P^lit(ν) ≤ 4 Var_ν` on `ℝ` (`KLS/LogConcave/Line/SharpPoincare.lean`, with the
distribution-function and affine-profile tools of `Probability/Line/`; Bobkov's `12 Var` stays as an
independent corollary in `Line/Poincare.lean`), and the raw/sequential-core agreement
`AgreesOnTests`/`IsSequentialCoreFor` of the smooth-gradient pre-energy for every law with a local
density (`Energy/SmoothGradient/Core.lean`, hypotheses `Energy.SmoothGradient.LocalDensity`). The
conditional-fiber form of the frame route is a proved `Energy.Dirichlet` energy on `L²(μ)` for every
Borel law and every direction law (`KLS/ConditionalFiber/Closed.lean`, via the two-point variance
identity of `Probability/TwoPointVariance.lean`), and under a fiber Poincaré input `κ` it is at most
`κ` times the local-slope gradient energy, so a form-gap bound `C` gives `C_P^lit(μ) ≤ κ C`
(`KLS/ConditionalFiber/EnergyComparison.lean`, for Haar-absolutely continuous laws and admissible
frames). For a full-dimensional log-concave law that input is supplied with `κ = 4`: base-law almost
every conditional fiber is log-concave on the line (`KLS/LogConcave/ConditionalFiber.lean`, via the
explicit slice kernel of `KLS/ConditionalFiber/SliceKernel.lean`, the Haar line splitting of
`Probability/HaarLine.lean` and the one-dimensional Prékopa--Leindler inequality of
`Probability/Line/BrunnMinkowski.lean` with `KLS/LogConcave/Line/OfDensity.lean`), so
`D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ` and `C_P^lit(μ) ≤ 4 C`; the frame question is still open. It
does **not** provide raw-gradient fiber consistency for singular measures;
`Energy/SmoothGradient/NormalDirection.lean` proves that fiber consistency fails for the ambient
pre-energy on every proper affine support. The identification with the metric Cheeger energy
`𝓔^can = 2 · Ch` is proved whenever the intrinsic law is absolutely continuous with respect to a
Haar measure, hence for every log-concave law (`Energy/Cheeger.lean` on top of
`Energy/LocalSlope/Relaxation.lean`, `cor:absolutely-continuous-relaxation-two-cheeger`); the
singular case stays open in `Energy/WIP/Cheeger.lean`. The ambient/intrinsic and smooth-test/relaxed comparisons
are proved and do not require raw/core agreement. Their comparison with the locally Lipschitz
literature constant has a written argument in Blueprint Appendix A. The weighted approximation
input and eight comparison interfaces are now certified under intrinsic absolute continuity.
Import `FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison` for the proved API.
Import `FunctionalInequalities.KLS.LogConcave.Poincare` for the general
log-concave version: intrinsic absolute continuity is now proved from compact-set log-concavity.
The full Borell density/moment representation is separately Lean-certified. See the
[general proof record](../research/decisions/2026-09-06-general-logconcave-comparison.md), the
[proof record](../research/decisions/2026-09-06-smooth-literature-proofs.md) and the
[mathematical guide](FunctionalInequalities/Poincare/README.md) for the theorem flow and the
Dirac counterexample explaining the agreement boundary.

### Placement rules

- Put reusable mathematics in its subject directory. Binary product work belongs in
  `Poincare/Product/`; dependent finite-product work belongs in `Poincare/FiniteProduct/`.
  Directory context supplies the prefix, so prefer `Product/Geometry.lean` to a flat
  `ProductGeometry.lean`.
- Give each proved ledger node one `certificate` in `../solutions/`, combining library
  conclusions directly. Keep these ledger-bound file paths stable.
- Check Euclidean and boundary specializations by typed applications of the same API. Do not
  introduce another named theorem merely to repeat a general theorem at a concrete type.
- Split modules by mathematical responsibility or dependency, not by issue number or proof
  status. A draft becoming proved does not require another file move.
- Keep the new dependency direction one-way: probability and `L²` primitives feed energy
  functionals and property layers, which then feed Poincaré optimization. Concrete Euclidean
  pre-energies do not belong in the pure optimizer. `Poincare/Foundation` is a downstream
  aggregate, never an import of a reusable lower-layer module.
- Keep geometry independent of tensorization theorems. `FiniteProduct/Geometry` imports
  `Product/Geometry` and the required Mathlib APIs; `FiniteProduct/Tensorization` assembles
  finite geometry with `Product/Tensorization` and `Transport`. The finite node's solution
  entry point also imports `Product/Reverse` for its binary reverse bounds and equality.
- Keep proved certificates' import closures independent of future draft modules. The root
  aggregate exports both `Poincare/Foundation` and the accepted library, including
  `Poincare/Product/Reverse` and
  `Poincare/FiniteProduct/Tensorization` and `Poincare/Gaussian/Real`. The solution entry points
  compile through the `Solutions` default target, including explicit draft statement checks.
- Update this source map and current documentation when moving a module. Historical decisions
  and explorations remain append-only; append a migration record instead of rewriting them.

The [2026-09-03 migration record](../research/explorations/2026-09-03-module-layout.md)
maps the earlier flat paths to this layout. Old import paths have no forwarding files. Historical
records, including the earlier Mathlib API probe, retain the paths used at their recorded stage.
The later [wrapper removal record](../research/explorations/2026-09-03-certificate-deduplication.md)
removes `Project/` and records the 45 reusable interfaces retained at acceptance.

The [2026-09-07 Energy migration record](../research/explorations/2026-09-07-energy-module-layout.md)
groups the relaxation, smooth-gradient and intrinsic-affine file families. The
[Energy guide](FunctionalInequalities/Energy/README.md) gives the reading order and import examples.

The [2026-09-07 log-concavity migration record](../research/explorations/2026-09-07-logconcave-module-layout.md)
records the four moves into `KLS/LogConcave/` and the accompanying documentation corrections.

## Statements and proof status

The table below lists the original Poincaré certificates. The complete current list, including
log-concavity results and the Borell draft, is in [solutions/README.md](../solutions/README.md)
and the [ledger](../research/a-series/ledger.yaml).

| Issue | Default entry point in `../solutions/` | Status |
| --- | --- | --- |
| #2: linear-test/covariance lower bounds | [LemLinearTestLower.lean](../solutions/LemLinearTestLower.lean) | `proved` / `lean` |
| #6: binary tensorization upper bounds | [LemPoincareTensorization.lean](../solutions/LemPoincareTensorization.lean) | `proved` / `lean` |
| #7: finite tensorization and optimal equality | [LemPoincareFiniteTensorization.lean](../solutions/LemPoincareFiniteTensorization.lean) | `proved` / `lean` |
| Gaussian: sharp one-dimensional constant | [LemPoincareGaussianOneDimensional.lean](../solutions/LemPoincareGaussianOneDimensional.lean) | `proved` / `lean` |
| Ambient/intrinsic comparison | [LemAmbientIntrinsicPoincareComparison.lean](../solutions/LemAmbientIntrinsicPoincareComparison.lean) | `proved` / `lean` |
| Smooth-test/relaxed comparison | [LemLegacyRelaxedPoincareComparison.lean](../solutions/LemLegacyRelaxedPoincareComparison.lean) | `proved` / `lean` |

The two comparison entries package 12 proved theorems and retain 12 application checks;
see their [reading guide](FunctionalInequalities/Poincare/Euclidean/README.md). The generic bridge
accepts any finite pre-energy realized in real `L²`; the concrete comparisons allow every
finite-dimensional Borel probability, including singular and zero-dimensional laws. They are
exported by `Poincare.Foundation` and the root aggregate. Their certificates and all
12 theorem dependencies are guarded against nonstandard axioms.

For the accepted Gaussian result, read the
[mathematical guide](FunctionalInequalities/Poincare/Gaussian/README.md). Its 20 declarations are
all proved and retain individual source notes: 7 in `Density`, 9 in `Hardy`, and 4 in `Real`.
`Density` provides Mathlib-based density calculus, `Hardy` isolates the interval/Tonelli and
half-line analytic estimates, and `Real` derives the valid and optimal constants using the
existing Poincaré and linear-test APIs. The solution file
contains the sole node certificate,
`Solutions.LemPoincareGaussianOneDimensional.certificate`, prints the complete interface and
checks seven applications without duplicate specialization theorems. Human semantic and
mathematical review has confirmed the variance normalization, the separate zero-variance Dirac
case, and the exact smooth L2 finite-energy scope. The earlier
[candidate review package](../research/decisions/2026-09-04-gaussian-poincare-candidate.md)
remains historical. The current contract and proof closeout are recorded in the
[Gaussian freeze](../research/decisions/2026-09-04-gaussian-poincare-freeze.md) and
[Gaussian acceptance record](../research/explorations/2026-09-04-gaussian-poincare-acceptance.md).
The root aggregate imports `Poincare/Gaussian/Real`.

`Poincare/SmoothTest/Transport.lean`, `Poincare/Product/Reverse.lean`, and `Poincare/FiniteProduct/`
contain the accepted mathematics and its library proofs; see the
[proof-stage record](../research/explorations/2026-09-03-finite-tensorization-proofs.md).
The solution entry point contains the sole node certificate,
`Solutions.LemPoincareFiniteTensorization.certificate`. It retains checks of all 45 public
interfaces, eight Euclidean statement families, and six concrete boundary applications. These
applications introduce no duplicate public declarations. The human confirmation and final
semantic review are recorded in the
[finite freeze](../research/decisions/2026-09-03-finite-tensorization-freeze.md) and
[acceptance record](../research/explorations/2026-09-03-finite-tensorization-acceptance.md).

All accepted smooth-test constants use globally `C∞` (`ContDiff ℝ ∞`) real-valued L2 tests with
integrable squared canonical gradient. Binary products use `WithLp 2 (E × F)` and finite products
use `PiLp 2 E`;
the laws are transported product probabilities. The finite statements include the empty family,
zero-dimensional factors, and infinite optimal constants. They do not identify this test domain
with a closed Dirichlet or Sobolev domain.

The exact mathematical contracts are in [LEAN_DESIGN.md](../LEAN_DESIGN.md). Historical review
records include
the [binary freeze](../research/decisions/2026-09-03-tensorization-freeze.md) and the
[finite freeze](../research/decisions/2026-09-03-finite-tensorization-freeze.md). The Gaussian
freeze and acceptance links above record its accepted scope and final evidence.
The [ledger](../research/a-series/ledger.yaml) records certification status, and
[solutions/README.md](../solutions/README.md) explains the certificate checks.

## Lean Blueprint

The [Blueprint](blueprint/README.md) is an executable reading order and dependency graph for the
formalization. It separates four things that prose can otherwise blur:

- the energy-parameterized `L²`/closed-energy engine already certified by Lean;
- the selected intrinsic-affine canonical frontend;
- the status-explicit endpoint bridges, including analytic proofs of the locally Lipschitz,
  relative-perimeter comparison awaiting formalization, the certified covariance-core closure,
  the certified Dirichlet/normal
  contraction, the certified one-dimensional `4 Var` bound, `2 Ch_μ`, affine normalization, the
  imported Cheeger comparison, and the optional stronger raw-test/core question;
- four sufficient long-route alternatives that share this analytic infrastructure. No
  probabilistic or logical independence is asserted.

The Blueprint is not a second proof-status database. Lean declarations and the
[ledger](../research/a-series/ledger.yaml) remain authoritative. A `\lean{...}` annotation maps a
statement to a local declaration, and `\leanok` records the support of that checked declaration;
for the ten ledger-backed certificate nodes it additionally requires the matching ledger record.
Absence of `\leanok` means only that a node is not locally Lean-certified: its mathematical status
may instead be open, conditional, imported, or proved with upstream agent review. `\notready`
marks an explicit unresolved statement choice, such as the test domain or normalization; the
nearby text must identify that choice. Possible future API changes alone do not justify it, and
removing it does not certify a proof.
Successful PDF or web rendering alone certifies none of these claims. The route sidecar records
recursive AND/OR composition, pinned provenance, and active or historical branch disposition; it
is likewise not a proof certificate.

The helper script accounts for the Lake package living in `formalization/` rather than at the Git
root. With `xelatex`, `latexmk`, and Graphviz's `dot` available, run the following from the
repository root:

```bash
python3 -m venv /tmp/kls-blueprint-venv
source /tmp/kls-blueprint-venv/bin/activate
python -m pip install --requirement formalization/blueprint/requirements.txt

python3 research/check_blueprint.py
python3 -m unittest discover -s research/tests -p 'test_check_blueprint.py'
(cd formalization && lake build)
python3 formalization/blueprint/build.py checkdecls
python3 formalization/blueprint/build.py pdf
python3 formalization/blueprint/build.py web
```

The final three commands may be replaced by
`python3 formalization/blueprint/build.py all`. Generated files are written to
`formalization/blueprint/lean_decls`, `formalization/blueprint/print/`, and
`formalization/blueprint/web/`; all are intentionally untracked. The dedicated
[`blueprint.yml`](../.github/workflows/blueprint.yml) workflow repeats these gates and uploads the
PDF and web tree as artifacts without deploying Pages.

## Build and validation

- Lean: `leanprover/lean4:v4.33.0` in `lean-toolchain`.
- Mathlib: tag `v4.33.0`, resolved by `lake-manifest.json` to
  `db584cd6d46c92f209a44c0f1c829460d327499d`.

Install [Elan](https://github.com/leanprover/elan) if needed. It reads `lean-toolchain`
automatically. From the repository root:

```bash
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
(cd formalization && lake build)
```

For a focused validation of the new foundation, run from `formalization/`:

```bash
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/Relaxation/Quadratic.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/SmoothGradient/Closed.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Closed.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Poincare/SmoothGradient/Intrinsic.lean
lake build FunctionalInequalities.Poincare.Foundation
lake build Examples solutions.FoundationAxiomAudit
```

The default targets build the library, `Solutions`, and `Examples`. `Solutions` contains all eight
certificate entry points, plus `solutions/GaussianAxiomAudit.lean` and
`solutions/FoundationAxiomAudit.lean`. `Examples` compiles `examples/PoincareFoundation.lean` from
the repository root. All ten accepted nodes and their local import closures are proof-complete.
The ledger checker scans proved certificates and their local imports for forbidden tokens. Lean
compilation checks the proofs; the guarded audits fix the Gaussian certificate and 27 foundation and comparison
declarations to the transitive axiom set `propext`, `Classical.choice`, and `Quot.sound`.
An unexpected dependency fails the default build.

Lake downloads the pinned dependency on the first build. `.lake/` is ignored and
`lake-manifest.json` is committed. The repository's `.github/workflows/lean.yml` runs the two
Python checks and the default Lean build. The official `leanprover/lean-action@v1` sets up Lean;
CI fetches only the local library, solution, and example files' directly imported Mathlib modules and
their upstream dependencies, then runs the complete default `lake build`. Whole-`.lake` GitHub
caching and automatic full-Mathlib downloads are disabled to limit runner disk usage.

The final publication SHA and CI result for that same commit are tracked in
[Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7); earlier build or
CI results do not substitute for that publication check.

To change dependency versions, choose a compatible Lean/Mathlib release, update `lean-toolchain`
and the `rev` in `lakefile.toml`, then run `lake update` and `lake build` from this directory.
Commit the toolchain, Lake configuration, and regenerated manifest together; keep a release pin.
