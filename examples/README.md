# Lean calling examples

The examples demonstrate public interfaces, test domains and boundary cases. They are compiled by the default `Examples` target.
Use [library design](../LEAN_DESIGN.md) for the layer boundaries and the [formalization guide](../formalization/README.md) for setup.

## Start with a checked client

| File | Calls demonstrated |
| --- | --- |
| [PoincareFoundation.lean](PoincareFoundation.lean) | Arbitrary probability spaces, energy comparison, singular laws, empty test families and sharp Gaussian constants |
| [ApiOrganization.lean](ApiOrganization.lean) | Public test objects, L² transport, covariance invariance and dimension zero |

From the repository root, build these examples with the pinned toolchain:

```bash
cd formalization
lake build Examples
```

`ApiOrganization.lean` uses the aggregate import for an overview. For a new application, select the mathematical owner below.

## Choose a mathematical entry point

| Task | Import | Scope to retain |
| --- | --- | --- |
| Compare Poincaré constants after changing an energy | `FunctionalInequalities.Poincare.L2.Comparison` | Arbitrary probability space; comparison on the specified finite energy domain |
| Use sharp one-dimensional Gaussian constants | `FunctionalInequalities.Poincare.Gaussian.Real` | The second Gaussian parameter is variance; the theorem uses the smooth-test frontend |
| Combine two factor laws | `FunctionalInequalities.Poincare.Product.Reverse` | The smooth-test product constant is the maximum of factor constants, including infinity |
| Combine finitely many Hilbert factors | `FunctionalInequalities.Poincare.FiniteProduct.Tensorization` | Dependent finite product, probability factors and the stated smooth finite-energy tests |
| Identify the literature constant for a log-concave law | `FunctionalInequalities.KLS.LogConcave.Poincare` | Finite-dimensional real geometry; absolute continuity is derived in intrinsic coordinates |
| Use a generated contraction semigroup | `FunctionalInequalities.Analysis.Semigroup.Generated.Laws` | Closed densely defined operator between real Hilbert spaces; no probability model is required |
| Extend a PSD trace bound to symmetric matrices | `FunctionalInequalities.Analysis.Matrix.Integral` | Arbitrary measure and finite matrix index; the displayed estimate has coefficient 2 |

For example, a Gaussian product calculation needs these two owners:

```lean
import FunctionalInequalities.Poincare.Gaussian.Real
import FunctionalInequalities.Poincare.Product.Reverse
```

The concrete Gaussian calls are in `PoincareFoundation.lean`; the product identity is
[`constant_prod_eq`](../formalization/FunctionalInequalities/Poincare/Product/Reverse.lean).

## Keep the frontend explicit

`SmoothTest`, `SmoothGradient`, `WeightedGradient`, `CovarianceGradient` and `LocalSlope` describe different tests or energies.
Use the proved comparison for the hypotheses at hand. Raw gradient energy can depend on the representative of an L² class for a singular law;
`PoincareFoundation.lean` contains the Dirac example. `Ambient` and `Intrinsic` also distinguish different carriers.

For a certificate or paper target, use the [certificate directory](../solutions/README.md) and the
[paper register](../research/progress/LITERATURE.md). A reusable calling example does not register a new certificate.
