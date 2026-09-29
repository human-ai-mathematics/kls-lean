# Energy module guide

This directory organizes extended nonnegative energies, sequential relaxation, and Euclidean
implementations by mathematical responsibility. See the [module placement rules](../../README.md#placement-rules)
and the [Poincaré foundation guide](../Poincare/README.md) for definitions, assumptions, and proof boundaries.

## Reading order

| Purpose | Entry point and subsequent modules |
| --- | --- |
| General energies and comparisons | `Form/Functional.lean` → `Form/Comparison.lean` |
| Relaxation of finite test energies | `Relaxation/Basic.lean` (including comparison along continuous maps, `sequentialRelaxation_comp_le`, and its constant-factor version `_comp_le_mul`) → `Relaxation/Approximation.lean` |
| Lower semicontinuity and recovery sequences | `Relaxation/LowerSemicontinuous.lean`, `Relaxation/Recovery.lean` |
| Quadraticity and closure | `Form/QuadraticPreEnergy.lean`, `Form/ClosedQuadratic.lean` → `Relaxation/Quadratic.lean` |
| Cores and the Markov property | `Form/Core.lean`, `Form/Dirichlet.lean`; conditional transfer in `Relaxation/Contraction.lean` |
| Dirichlet property of smooth-gradient relaxation | `SmoothGradient/Dirichlet.lean`: smoothed normal contractions `NormalContraction.smoothed`, test composition `Test.compSmoothed`, `SmoothGradient.markovian`/`dirichlet`, and the intrinsic version `Intrinsic.dirichlet`; valid for every Borel probability law |
| Smooth-gradient implementation | `SmoothGradient/Basic.lean` → `Quadratic.lean`, `Density.lean` → `Closed.lean`; `SmoothGradient/NormalDirection.lean`: on a proper affine support, a normal coordinate represents the zero L² class but has raw energy 1, so the ambient pre-energy fails `RespectsAmbientFibers`; `SmoothGradient/Core.lean`: raw/sequential-core agreement `preEnergy_agreesOnTests`, `preEnergy_isSequentialCoreFor` under `LocalDensity`, with intrinsic-law instances |
| Implementation within the affine support | `SmoothGradient/Intrinsic/Basic.lean` → `Closed.lean` |
| Comparing the implementations and Lipschitz approximation | `SmoothGradient/Intrinsic/Comparison.lean`, `Euclidean/LipschitzApproximation/Approximation.lean` |
| L² relaxation of local slope and asymptotic Lipschitz energy | `LocalSlope/Relaxation.lean`: `AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`, `LocalSlope.{preEnergy,relaxation}`, and the unconditional comparison `relaxation_le_asymptoticLipschitz`; equality of the two conventions for finite-dimensional Borel probability laws is in `Cheeger/Identification.lean` |
| Metric Cheeger energy and `𝓔^can = 2·Ch` | `Cheeger/Basic.lean`: `Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`; `Cheeger/Identification.lean` proves `SmoothGradient.relaxation = LocalSlope.relaxation` and `𝓔^can_μ = 2·Ch_μ` for every finite-dimensional Borel probability law, including singular laws and infinite energies. Dependencies: `Euclidean/Slope/Comparison.lean` (asymptotic Lipschitz constant equals gradient norm for smooth tests; sandwich of three relaxations), `Euclidean/Slope/Recovery.lean` (mollified recovery for globally Lipschitz tests and truncation tools), `Euclidean/Slope/Density.lean` (measurability of local slope, McShane patches, and density of smooth tests in local-slope energy), `Cheeger/Identification.lean` (five identities; `thm:smooth-gradient-relaxation-two-cheeger`, the 26th certificate). The former `WIP/Cheeger.lean` was deleted; `Energy/` has no remaining WIP |
| Covariance-weighted Lipschitz-gradient definitions | `CovarianceGradient/Basic.lean`: pre-energy, sequential relaxation, and `Energy.CovarianceGradient.Intrinsic.energy` on the intrinsic law |
| Operator forms and closability | `Relaxation/LinearPMap.lean` (relaxation of any closable `LinearPMap` equals the squared norm of its closure, `normSqEnergy`; Hilbert selection lemma) → `Euclidean/WeakDerivative.lean` (integration by parts for Lipschitz functions) → `WeightedGradient/Basic.lean`, `Closable.lean`, `Core.lean` (including the ℝ + C_c^∞ core `constantSmoothCore`) |
| Translation invariance | `CovarianceGradient/Translation.lean`: translated laws, L² pullback isometry `L2.Translation.pullbackEquiv`, invariance of variance and covariance, and invariance of covariance relaxation and its optimal constant |
| Transport by general linear equivalences | `CovarianceGradient/LinearEquiv.lean`: image law `KLS.LogConcave.mapContinuousLinearEquiv`, covariance conjugation by the map and its adjoint, gradient composition formula, L² pullback isometry `L2.ContinuousLinearEquiv.pullbackEquiv`, invariance of covariance relaxation and its optimal constant, and images of affine supports; the transport component of whitening |
| Transport by linear isometries | `CovarianceGradient/Isometry.lean`: isometric image law `Probability.mapLinearIsometryEquiv`, covariance conjugation, gradient composition formula, L² pullback isometry `mapL2`, and invariance of covariance relaxation and its optimal constant; together with Translation, this covers arbitrary affine isometries of intrinsic coordinates |

The table gives a reading route; each file's `import` statements specify the exact dependencies.

## Import examples

```lean
import FunctionalInequalities.Energy.Relaxation.Recovery
import FunctionalInequalities.Energy.SmoothGradient.Closed
import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
```

Library modules import the specific files they need. For complete downstream examples, start with
`FunctionalInequalities.Poincare.Foundation` and
[`examples/PoincareFoundation.lean`](../../../examples/PoincareFoundation.lean).

## Placement of future files

- Put foundational definitions for a topic in `Basic.lean`; name subsequent files by responsibility. The directory supplies the shared prefix.
- Put generic energy and closed-quadratic-form interfaces in `Form/`, and general relaxation theorems in `Relaxation/`.
- Put concrete implementations in the corresponding Euclidean topic directory; keep comparisons across implementations in `Euclidean/`.
- Split by mathematical responsibility and dependencies, not proof status, task number, or date.

File paths and declaration namespaces are independent. This reorganization preserves all
mathematical declarations. Closed quadraticity still does not automatically provide the Dirichlet
property or agreement of raw test energy with relaxed energy. For individual replacements of old
import paths, see the [migration record](../../../research/explorations/2026-09-07-energy-module-layout.md).

`Euclidean/LipschitzApproximation/` is divided by responsibility into
[Basic](Euclidean/LipschitzApproximation/Basic.lean) (gradients and truncation),
[Measurable](Euclidean/LipschitzApproximation/Measurable.lean) (measurability),
[Kernel](Euclidean/LipschitzApproximation/Kernel.lean) (kernels and convolution estimates), and
[Approximation](Euclidean/LipschitzApproximation/Approximation.lean) (weighted approximation).
Clients import the earliest layer providing their required interface.
