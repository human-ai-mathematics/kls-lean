# Lean calling examples

These are compiled clients of existing mathematics, with no ledger certificate or new paper-coverage claim.
The default `Examples` target checks every file below. Use [library design](../LEAN_DESIGN.md) for layer boundaries.

| Client | Calls and scope |
| --- | --- |
| [MatrixIntegral.lean](MatrixIntegral.lean) | One matrix-integral import; arbitrary real coefficient, an indefinite symmetric matrix, and an identity field with the PSD premise discharged |
| [GeneratedSemigroup.lean](GeneratedSemigroup.lean) | One semigroup-law import; bounded-operator norm and composition, plus a closed full-domain zero operator; real Hilbert spaces without a finite-dimension assumption |
| [FiniteProductCovariance.lean](FiniteProductCovariance.lean) | Finite tensorization, Gaussian and probability transport imports; variances `1, 0, 4`, a Dirac factor, the empty product, and covariance under translation |
| [PoincareFoundation.lean](PoincareFoundation.lean) | Energy comparison, singular laws, empty test families and sharp one-dimensional Gaussian constants |
| [ApiOrganization.lean](ApiOrganization.lean) | Aggregate-import overview of test objects, L² transport, covariance invariance and dimension zero |

From the repository root:

```bash
cd formalization
lake build Examples
```

## Use the owning interface

| Task | Import | Keep explicit |
| --- | --- | --- |
| Extend a PSD trace estimate to symmetric matrices | `FunctionalInequalities.Analysis.Matrix.Integral` | The PSD estimate is an input; arbitrary measure, finite index and real coefficient |
| Compose generated bounded operators | `FunctionalInequalities.Analysis.Semigroup.Generated.Laws` | Closed operator, dense domain, nonnegative times; `Generated.operator_add_time` and `norm_operator_le_one` |
| Combine finite factor laws | `FunctionalInequalities.Poincare.FiniteProduct.Tensorization` | Probability factors, smooth finite-energy frontend; empty families and infinite optimal constants are allowed |
| Use sharp real Gaussian constants | `FunctionalInequalities.Poincare.Gaussian.Real` | The second Gaussian parameter is variance; zero variance is permitted |
| Transport a covariance operator | `FunctionalInequalities.Probability.Transport` | Pushforward/translation belongs to the probability law; L² pullback is a separate operation |
| Compare energies | `FunctionalInequalities.Poincare.L2.Comparison` | Specified finite-energy domains on a probability space |
| Identify the log-concave literature constant | `FunctionalInequalities.KLS.LogConcave.Poincare` | Intrinsic coordinates and the theorem's geometric hypotheses |

The matrix client uses `Measure` with `IsProbabilityMeasure` for its concrete probability case,
so its generic integral import need not expose the bundled `ProbabilityMeasure` object.
The Gaussian product's value `4` belongs to `SmoothTest`; covariance translation is a separate
operator identity. Changing energy frontend requires the corresponding proved comparison.

## Connect a separate Lake project

Use the same [pinned Lean toolchain](../formalization/lean-toolchain). The package is in the
repository's `formalization/` subdirectory. In an independent project's `lakefile.toml`:

```toml
[[require]]
name = "functional-inequalities"
git = "https://github.com/human-ai-mathematics/kls-lean.git"
rev = "<reviewed-full-commit-containing-the-used-interfaces>"
subDir = "formalization"
```

For local development, replace `git`, `rev` and `subDir` with `path = "../KLS/formalization"`.
Import an owning module in the client and build the client's Lake target.

The initial independent acceptance used commit `79fbe1a`: 32 project modules were compiled
from its separate Git checkout, without KLS, solution or repository-example imports. Pinned
third-party source/compiled caches were copied separately; this was not a fresh Mathlib rebuild.
The subsequent operator APIs and current examples were tested against an explicit source overlay.
Choose a revision containing those additions when using the Git recipe; [HANDOFF](../HANDOFF.md)
owns delivery status. The [reuse decision](../research/decisions/2026-10-18-downstream-reuse.md)
records the scope and receipt locations.

`SmoothTest`, `SmoothGradient`, `WeightedGradient`, `CovarianceGradient` and `LocalSlope` use
different tests or energies. Raw gradient energy can depend on the chosen L² representative
for a singular law; the foundation client includes that obstruction. `Ambient` and `Intrinsic`
also use different carriers. See the [certificate guide](../solutions/README.md) and
[paper register](../research/progress/LITERATURE.md) for exact registered targets.
