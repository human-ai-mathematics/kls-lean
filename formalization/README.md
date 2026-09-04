# Lean formalization

Reusable mathematics is organized by topic under `FunctionalInequalities/`.
Each ledger node has one entry point in repository-root `solutions/`, importing the mathematics
directly. There is no intermediate project-specific wrapper layer.

Downstream applications, examples, and smoke tests may start from
[`Poincare/Foundation.lean`](FunctionalInequalities/Poincare/Foundation.lean). Reusable library
modules must instead import their exact direct dependencies so the direction below remains
acyclic. The foundation's
[mathematical guide](FunctionalInequalities/Poincare/README.md) records the `L²`, extended-energy,
relaxation, closed-form, Dirichlet, and pure-optimization layers and distinguishes them from the
accepted legacy smooth-test API.

## Source map

```text
formalization/
├── blueprint/                                  # Executable theorem/dependency map
│   ├── src/                                # Shared TeX source for PDF and web
│   └── route-composition.yaml             # Machine-checked alternative KLS routes
├── FunctionalInequalities.lean               # Aggregate of the proved library
└── FunctionalInequalities/
    ├── Probability/
    │   ├── Basic.lean                       # Bundled probability-measure boundary
    │   └── AffineSupport.lean               # Minimal affine carrier and intrinsic law
    ├── L2/
    │   └── MeanVariance.lean                # Intrinsic real L² mean and variance
    ├── Energy/
    │   ├── Functional.lean                  # Extended energy and finite domain
    │   ├── Comparison.lean                  # Pointwise extended-energy comparison
    │   ├── Relaxation.lean                  # Sequential relaxation of a pre-energy
    │   ├── QuadraticPreEnergy.lean           # Finite quadratic pre-energy interface
    │   ├── RelaxationLowerSemicontinuous.lean # LSC of sequential relaxation
    │   ├── RelaxationRecovery.lean          # Finite/all-point recovery sequences
    │   ├── RelaxationQuadratic.lean         # Quadratic laws and ClosedQuadratic theorem
    │   ├── RelaxationContraction.lean       # Conditional continuous-contraction transfer
    │   ├── FormCore.lean                    # Agreement, generation and core predicates
    │   ├── ClosedQuadratic.lean             # Closed quadratic property layer
    │   ├── Dirichlet.lean                   # Markov and Dirichlet property layers
    │   └── Euclidean/
    │       ├── SmoothGradient.lean           # C∞ gradient pre-energy and relaxation
    │       ├── SmoothGradientQuadratic.lean  # Test algebra and quadratic energy
    │       ├── SmoothGradientDensity.lean    # Dense C∞ realization in real L²
    │       ├── SmoothGradientClosed.lean     # ClosedQuadratic smooth relaxation
    │       ├── IntrinsicAffine.lean          # Bidirectional intrinsic L² equivalence
    │       └── IntrinsicAffineClosed.lean    # Transported ClosedQuadratic theorem
    └── Poincare/
        ├── Foundation.lean                  # Aggregate for the new layered API
        ├── Optimal.lean                     # Pure finite test-family optimizer
        ├── Comparison.lean                  # Test-family/domain comparisons
        ├── L2Energy.lean                    # Extended L² energy bridge
        ├── L2Comparison.lean                # Energy-order constant comparison
        ├── Euclidean/
        │   ├── SmoothGradient.lean          # Ambient relaxed-gradient constant
        │   └── IntrinsicAffine.lean         # Intrinsic-affine Holds and optimal constant
        ├── Basic.lean                       # Admissible, energy, Holds, constant
        ├── LinearTest.lean                  # Linear tests, Rayleigh, covariance bounds
        ├── Transport.lean                   # Coordinate lifts and isometry transport
        ├── Product/
        │   ├── Geometry.lean                # Binary Hilbert product and its measure
        │   ├── Variance.lean                # L2/Fubini and variance decomposition
        │   ├── Admissible.lean              # A.e. admissible sections and energy
        │   ├── Tensorization.lean           # Binary upper bounds
        │   └── Reverse.lean                 # Coordinate reverse bounds and equality
        ├── FiniteProduct/
        │   ├── Geometry.lean                # PiLp, dependent measure, reindexing, split
        │   └── Tensorization.lean           # Finite upper bounds and optimal equality
        └── Gaussian/
            ├── README.md                    # Theorem guide, examples and proof map
            ├── Density.lean                 # 7 density/calculus and integrability interfaces
            ├── Hardy.lean                   # 9 interval, Tonelli and energy interfaces
            └── Real.lean                    # 4 fixed/sharp-constant interfaces
```

Import the module needed by the argument, for example:

```lean
import FunctionalInequalities.Poincare.Basic
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
- `smoothGradientRelaxation_closedQuadratic` instantiates this result for the finite-dimensional
  Borel `C∞` gradient pre-energy. `intrinsicAffineSmoothGradientRelaxation_closedQuadratic`
  transports it through affine-support coordinates.
- `affineSupport` is the smallest closed affine subspace containing almost every point.
  `intrinsicL2Equiv` is a two-sided real linear isometric equivalence between the original and
  intrinsic real `L²` spaces, rather than a one-way embedding.
- `RelaxationContraction` gives a conditional transfer theorem: a continuous map satisfying
  `RelaxedContractionBound` on realized tests decreases relaxed energy everywhere.
- `Poincare.Euclidean.IntrinsicAffine` exposes `Holds`, the optimal `ENNReal` constant, and their
  exact order-theoretic equivalence for the intrinsic-affine relaxed energy.

In Mathlib v4.33 ordinary `C∞` regularity is `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` is analytic. Both the
accepted legacy tests and the new smooth-gradient tests use `∞`.

The foundation does **not** yet provide a Markov/Dirichlet witness for the smooth relaxation, an
`AgreesOnTests` or core theorem, raw-gradient fiber consistency for singular measures, or an
identification with Cheeger energy `2 · Ch`. It also does not identify the legacy smooth-test
constant with the new extended-energy constant, or the intrinsic-affine relaxation constant with
the ambient relaxation constant. See the
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
  `Poincare/FiniteProduct/Tensorization` and `Poincare/Gaussian/Real`. All four certificates
  compile through the `Solutions` default target.
- Update this source map and current documentation when moving a module. Historical decisions
  and explorations remain append-only; append a migration record instead of rewriting them.

The [2026-09-03 migration record](../research/explorations/2026-09-03-module-layout.md)
maps the earlier flat paths to this layout. Old import paths have no forwarding files. Historical
records, including the earlier Mathlib API probe, retain the paths used at their recorded stage.
The later [wrapper removal record](../research/explorations/2026-09-03-certificate-deduplication.md)
removes `Project/` and records the 45 reusable interfaces retained at acceptance.

## Statements and proof status

| Issue | Default entry point in `../solutions/` | Status |
| --- | --- | --- |
| #2: linear-test/covariance lower bounds | [LemLinearTestLower.lean](../solutions/LemLinearTestLower.lean) | `proved` / `lean` |
| #6: binary tensorization upper bounds | [LemPoincareTensorization.lean](../solutions/LemPoincareTensorization.lean) | `proved` / `lean` |
| #7: finite tensorization and optimal equality | [LemPoincareFiniteTensorization.lean](../solutions/LemPoincareFiniteTensorization.lean) | `proved` / `lean` |
| Gaussian: sharp one-dimensional constant | [LemPoincareGaussianOneDimensional.lean](../solutions/LemPoincareGaussianOneDimensional.lean) | `proved` / `lean` |

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
The proved-library aggregate imports `Poincare/Gaussian/Real`.

`Poincare/Transport.lean`, `Poincare/Product/Reverse.lean`, and `Poincare/FiniteProduct/`
contain the accepted mathematics and its library proofs; see the
[proof-stage record](../research/explorations/2026-09-03-finite-tensorization-proofs.md).
The solution entry point contains the sole node certificate,
`Solutions.LemPoincareFiniteTensorization.certificate`. It retains checks of all 45 public
interfaces, eight Euclidean statement families, and six concrete boundary applications. These
applications introduce no duplicate public declarations. The human confirmation and final
semantic review are recorded in the
[finite freeze](../research/decisions/2026-09-03-finite-tensorization-freeze.md) and
[acceptance record](../research/explorations/2026-09-03-finite-tensorization-acceptance.md).

All accepted legacy constants use globally `C∞` (`ContDiff ℝ ∞`) real-valued L2 tests with
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
formalization. It separates three things that prose can otherwise blur:

- the canonical `L²`/closed-energy foundation already certified by Lean;
- the precise analytic bridges that remain open, including Dirichlet/normal-contraction,
  `2 Ch_μ`, raw-test/core agreement, and ambient/intrinsic comparison;
- four alternative long routes from the canonical interface to KLS.

The Blueprint is not a second proof-status database. Lean declarations and the
[ledger](../research/a-series/ledger.yaml) remain authoritative. A `\lean{...}` annotation maps a
statement to a declaration, and `\leanok` is used only at the status justified by that declaration
and the ledger. An exact but open mathematical statement may appear without `\leanok`; a node
whose final hypotheses are not frozen is additionally marked `\notready`. Successful PDF or web
rendering alone certifies none of these claims.

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
cd formalization && lake build
```

For a focused validation of the new foundation, run from `formalization/`:

```bash
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/RelaxationQuadratic.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/Euclidean/SmoothGradientClosed.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/Euclidean/IntrinsicAffineClosed.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Poincare/Euclidean/IntrinsicAffine.lean
lake build FunctionalInequalities.Poincare.Foundation
```

The default targets build the library and the `Solutions` target containing all four entry points
above plus `solutions/GaussianAxiomAudit.lean`. All four accepted nodes and their local import
closures are proof-complete. The ledger checker scans proved certificates and their local imports
for forbidden tokens. Lean compilation checks the proofs; the guarded audit fixes the Gaussian
certificate's transitive axiom set to `propext`, `Classical.choice`, and `Quot.sound` and makes any
change fail the default build.

Lake downloads the pinned dependency on the first build. `.lake/` is ignored and
`lake-manifest.json` is committed. The repository's `.github/workflows/lean.yml` runs the two
Python checks and the default Lean build. The official `leanprover/lean-action@v1` sets up Lean;
CI fetches only the local library and solution files' directly imported Mathlib modules and
their upstream dependencies, then runs the complete default `lake build`. Whole-`.lake` GitHub
caching and automatic full-Mathlib downloads are disabled to limit runner disk usage.

The final publication SHA and CI result for that same commit are tracked in
[Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7); earlier build or
CI results do not substitute for that publication check.

To change dependency versions, choose a compatible Lean/Mathlib release, update `lean-toolchain`
and the `rev` in `lakefile.toml`, then run `lake update` and `lake build` from this directory.
Commit the toolchain, Lake configuration, and regenerated manifest together; keep a release pin.
