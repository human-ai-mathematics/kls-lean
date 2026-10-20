# Lean calling examples

These are compiled clients of existing mathematics, with no ledger certificate or new paper-coverage claim.
The default `Examples` target checks every file below. Use [library design](../LEAN_DESIGN.md) for layer boundaries.

| Client | Calls and scope |
| --- | --- |
| [KlsApplications.lean](KlsApplications.lean) | Directly calls `KLS.kls`: a universal covariance-normalized smooth-test bound, a variance inequality, isotropic specialization and Gaussian convolution with bound `C + t` |
| [MetricBV.lean](MetricBV.lean) | Generic metric-space perimeter: compose nonzero measure scaling and finite-measure complement symmetry; no KLS application import |
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
| Obtain the main KLS bound | `FunctionalInequalities.KLS.Target` | Choose the universal constant before the dimension and law; the statement uses the intrinsic local-slope constant |
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

## Apply KLS to another argument

[KlsApplications.lean](KlsApplications.lean) starts with `obtain ⟨C, hC⟩ := KLS.kls`.
Its `covariance_bound` converts the intrinsic local-slope conclusion into
`Poincare.SmoothTest.Holds` through the proved log-concave comparisons. Then
`variance_bound` applies `Holds.variance_le` to a smooth L² function with integrable squared
gradient. `isotropic_bound` removes the covariance factor; `gaussian_convolution_bound`
combines it with the Gaussian and convolution interfaces. Each bound chooses one constant
before quantifying over dimensions and laws, including dimension zero.

The last example supplies the Poincaré input of Kook–Vempala–Zhang,
[*In-and-Out: Algorithmic Diffusion for Sampling Convex Bodies*, NeurIPS 2024](https://papers.nips.cc/paper_files/paper/2024/file/c4006ff54a7bbda74c09bad6f7586f5b-Paper-Conference.pdf),
Definition 2 and the Poincaré part of Lemma 11: Gaussian convolution with covariance `t Id`
adds `t` to the bound. The normalization is `Var f ≤ C ∫ ‖∇f‖²`, with no factor `1/2`.
The Lean client uses smooth finite-energy tests. The sampler, divergence contraction and
log-Sobolev assertions require their own formalization; this example adds no paper-coverage claim.

Other uses of KLS include normal approximation in Fang–Koike,
[*Sharp High-dimensional Central Limit Theorems for Log-concave Distributions*](https://arxiv.org/abs/2207.14536),
and entropy estimates in Ball–Nguyen,
[*Entropy jumps for isotropic log-concave random vectors and spectral gap*](https://arxiv.org/abs/1206.5098).
These are potential application targets, with no local formalization status assigned here.

## Connect a separate Lake project

For a first local call of the main theorem, follow the complete
[KLS first-use walkthrough](FIRST-USE.md). It includes the pinned toolchain, package location,
client target, cache preparation and strict compilation. The path dependency uses the current
local source tree. The Git procedure below instead selects a committed revision.

Use the same [pinned Lean toolchain](../formalization/lean-toolchain). The package is in the
repository's `formalization/` subdirectory. In an independent project's `lakefile.toml`, pin the
reviewed commit. The pin below is the recorded downstream baseline; it is not a claim
of acceptance for a later release revision:

```toml
[[require]]
name = "functional-inequalities"
git = "https://github.com/human-ai-mathematics/kls-lean.git"
rev = "5d41bd7dd379d0c0858f1b8416f61c82e0fe26eb"
subDir = "formalization"
```

While the repository is private, Lake's Git fetch needs GitHub read access (an authenticated
HTTPS remote); anonymous fetching is not yet available. For local development, replace `git`,
`rev` and `subDir` with `path = "../KLS/formalization"`. Import an owning module in the client
and build the client's Lake target.

This pin passed all three narrow clients with freshly compiled primary modules and trusted
pinned third-party caches. Its receipt records the exact Git revision and results under the
[verification trust rules](../research/verification.md#receipts-and-trust-scope); these interface
checks exclude KLS, solution and example imports.
[API browsing](../formalization/API.md) provides compiler-derived signatures.

`SmoothTest`, `SmoothGradient`, `WeightedGradient`, `CovarianceGradient` and `LocalSlope` use
different tests or energies. Raw gradient energy can depend on the chosen L² representative
for a singular law; the foundation client includes that obstruction. `Ambient` and `Intrinsic`
also use different carriers. See the [certificate guide](../solutions/README.md) and
[paper register](../research/progress/LITERATURE.md) for exact registered targets.

## Reproduce downstream acceptance

From the repository root, select one full Git commit:

```bash
python3 research/downstream.py --rev FULL_40_HEX_COMMIT
```

The default source is the GitHub repository. Add `--repository /path/to/repository`
for a local committed revision before pushing, `--cache-packages DIR` for clean pinned
third-party caches, `--output NEW_DIR` for a receipt directory, or `--threads N` (default 2).
HTTP(S), file URLs and local Git directories are supported. Existing output directories
are rejected; a working-tree overlay is never used.

The runner builds the three narrow clients from that commit, strictly compiles them, audits
every declaration in their primary import closure and replays all primary/client modules.
Each started run retains `receipt.json`, logs, generated audit sources and evidence hashes.
Exit codes are 0 for success, 1 for a failed run with a receipt, and 2 for invalid arguments.

A passed receipt is downstream acceptance, not a new certificate. Explicit third-party
compiled caches are trusted. Without them, Lake fetches pinned dependencies and the runner
requests the needed Mathlib cache when applicable; this does not replay third-party modules.
See [receipt scope](../research/verification.md#receipts-and-trust-scope).
