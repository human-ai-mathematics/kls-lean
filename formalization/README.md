# Lean formalization

Reusable mathematics is organized by topic under `FunctionalInequalities/Poincare/`.
Each ledger node has one entry point in repository-root `solutions/`, importing the mathematics
directly. There is no intermediate project-specific wrapper layer.

## Source map

```text
formalization/
├── FunctionalInequalities.lean               # Aggregate of the proved library
└── FunctionalInequalities/
    └── Poincare/
        ├── Basic.lean                       # Admissible, energy, Holds, constant
        ├── LinearTest.lean                  # Linear tests, Rayleigh, covariance bounds
        ├── Transport.lean                   # Coordinate lifts and isometry transport
        ├── Product/
        │   ├── Geometry.lean                # Binary Hilbert product and its measure
        │   ├── Variance.lean                # L2/Fubini and variance decomposition
        │   ├── Admissible.lean              # A.e. admissible sections and energy
        │   ├── Tensorization.lean           # Binary upper bounds
        │   └── Reverse.lean                 # Coordinate reverse bounds and equality
        └── FiniteProduct/
            ├── Geometry.lean                # PiLp, dependent measure, reindexing, split
            └── Tensorization.lean           # Finite upper bounds and optimal equality
```

Import the module needed by the argument, for example:

```lean
import FunctionalInequalities.Poincare.Basic
import FunctionalInequalities.Poincare.Product.Tensorization
-- For finite-product tensorization and optimal equality:
import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
```

The module hierarchy locates files; declaration namespaces remain unchanged. In particular,
theorems still use `FunctionalInequalities.Poincare`, variance helpers use
`FunctionalInequalities.ProductVariance`, and covariance definitions use
`FunctionalInequalities.Covariance`.

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
- Keep geometry independent of tensorization theorems. `FiniteProduct/Geometry` imports
  `Product/Geometry` and the required Mathlib APIs; `FiniteProduct/Tensorization` assembles
  finite geometry with `Product/Tensorization` and `Transport`. The finite node's solution
  entry point also imports `Product/Reverse` for its binary reverse bounds and equality.
- Keep proved certificates' import closures independent of future draft modules. The root
  aggregate exports the accepted library, including `Poincare/Product/Reverse` and
  `Poincare/FiniteProduct/Tensorization`. All three certificates compile through default targets.
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

All constants use the existing globally smooth, real-valued L2 tests with integrable squared
canonical gradient. Binary products use `WithLp 2 (E × F)` and finite products use `PiLp 2 E`;
the laws are transported product probabilities. The finite statements include the empty family,
zero-dimensional factors, and infinite optimal constants. They do not identify this test domain
with a closed Dirichlet or Sobolev domain.

The exact mathematical contracts are in [LEAN_DESIGN.md](../LEAN_DESIGN.md). Human review uses
the [binary freeze](../research/decisions/2026-09-03-tensorization-freeze.md) and the
[finite freeze](../research/decisions/2026-09-03-finite-tensorization-freeze.md).
The [ledger](../research/a-series/ledger.yaml) records certification status, and
[solutions/README.md](../solutions/README.md) explains the certificate checks.

## Build and validation

- Lean: `leanprover/lean4:v4.33.0` in `lean-toolchain`.
- Mathlib: tag `v4.33.0`, resolved by `lake-manifest.json` to
  `db584cd6d46c92f209a44c0f1c829460d327499d`.

Install [Elan](https://github.com/leanprover/elan) if needed. It reads `lean-toolchain`
automatically. From the repository root:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

The default targets build the library and all three entry points above. The current build has
no proof placeholders or warnings. The ledger checker scans proved certificates and their local imports for forbidden
tokens; Lean compilation and transitive axiom inspection verify the proofs separately.

Lake downloads the pinned dependency on the first build. `.lake/` is ignored and
`lake-manifest.json` is committed. The repository's `.github/workflows/lean.yml` runs the two
Python checks and the default Lean build, using the official `leanprover/lean-action@v1` and
Mathlib cache.

The final publication SHA and CI result for that same commit are tracked in
[Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7); earlier build or
CI results do not substitute for that publication check.

To change dependency versions, choose a compatible Lean/Mathlib release, update `lean-toolchain`
and the `rev` in `lakefile.toml`, then run `lake update` and `lake build` from this directory.
Commit the toolchain, Lake configuration, and regenerated manifest together; keep a release pin.
