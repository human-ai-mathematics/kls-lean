# Poincaré foundations: from probability measures to optimal constants

These foundations provide reusable interfaces for Poincaré inequalities on real `L²`. Given a
probability measure `μ` and energy `E`, they define the optimal constant and prove that a finite
constant is valid exactly when it bounds the optimum. The concrete Euclidean implementation
uses smooth-gradient energy on the affine support, relaxes it in `L²`, and pulls it back to the
original space.

**The closed-quadratic-form chain and the ambient/intrinsic and smooth-test/relaxed comparison
bridges are proved.** The accepted Gaussian and tensorization theorems use the smooth-test
interface and transfer to the selected constant through the finite-dimensional bridges.
Equivalence with the literature's locally Lipschitz constant is also proved in Lean. The general
comparison assumes intrinsic absolute continuity; this is proved for log-concave probability
measures, so no extra premise is needed in that case. See the
[literature-constant comparison](LocalSlope/SmoothTestComparison.lean) and
[general log-concave version](../KLS/LogConcave/Poincare.lean). The full Borell density
representative and moment theorems have a separate certificate. Cheeger-energy identification
`Ecan = 2 Ch` (local-slope convention) is proved for every finite-dimensional Borel probability
law, including singular laws; see [Cheeger identification](../Energy/Cheeger/Identification.lean).
This identifies relaxed energies; it supplies neither raw-test-energy agreement nor a finite
Poincaré bound. The dimension-free KLS bound is proved separately in
[the final KLS target](../KLS/Target.lean); the [paper register](../../../research/progress/LITERATURE.md)
records its exact scope and certificates.

Interfaces may evolve with the mathematical design, including already proved interfaces.
Proof work does not require an interface freeze. Certification concerns the current statement
and proof. Changes to assumptions, conclusions, test domains, or normalization must be recorded
explicitly, propagated to dependents, and checked for continued coverage of the original
mathematical target. See the [lifecycle conventions](../../../research/ledger-schema.md#lifecycle).

## Start here

| Purpose | Entry point |
| --- | --- |
| Use the new foundations | [Foundation.lean](Foundation.lean) |
| Understand optimal constants and finite-energy domains | [L2/Energy.lean](L2/Energy.lean) |
| Use the selected Euclidean constant | [SmoothGradient/Intrinsic.lean](SmoothGradient/Intrinsic.lean) |
| Use the affine covariance constant `C_P^aff` (definition; separate theorems give its closed form, ambient translation invariance, and isotropic reduction, without a Poincaré inequality) | [CovarianceGradient/Intrinsic.lean](CovarianceGradient/Intrinsic.lean), [CovarianceGradient/Translation.lean](CovarianceGradient/Translation.lean), [LipschitzGradient/Comparison.lean](LipschitzGradient/Comparison.lean) |
| See complete usage and boundary examples | [PoincareFoundation.lean](../../../examples/PoincareFoundation.lean) |
| Use the proved Gaussian theorems | [Gaussian/README.md](Gaussian/README.md) |
| Find all modules and import rules | [formalization/README.md](../../README.md) |
| Review remaining mathematical bridges and KLS routes | [Blueprint](../../blueprint/README.md) |
| Use the proved constant-comparison bridges | [Euclidean/README.md](Euclidean/README.md) |

The examples cover variance of constants, the direction of energy comparison, the selected
constant, the Dirac raw-energy counterexample, the recovery obstruction for empty test classes,
and numerical and degenerate Gaussian cases. Every `example` is included in the default `lake build`.

## A directly usable interface

```lean
import FunctionalInequalities.Poincare.Foundation

open MeasureTheory FunctionalInequalities

example (μ : ProbabilityMeasure ℝ) :
    Energy.ClosedQuadratic (Energy.SmoothGradient.Intrinsic.energy μ) :=
  Energy.SmoothGradient.Intrinsic.closedQuadratic μ

example (μ : ProbabilityMeasure ℝ) (C : NNReal)
    (h : Poincare.SmoothGradient.Intrinsic.constant μ ≤ (C : ENNReal)) :
    Poincare.SmoothGradient.Intrinsic.Holds μ C :=
  (Poincare.SmoothGradient.Intrinsic.holds_iff_constant_le μ C).mpr h
```

The first result applies to every Borel probability measure, including measures without a density.
The second shows how to use a known constant bound; it does not establish that bound.
The same syntax works for arbitrary finite-dimensional real Borel Hilbert spaces.

The new interface uses `ProbabilityMeasure`. Given `μ : Measure E` and
`[IsProbabilityMeasure μ]`, package them with `Probability.ofMeasure μ`; coercing back to
`Measure E` definitionally recovers the original measure. The legacy interface retains its
`Measure` and probability-instance form, so callers need not migrate accepted proofs.

## Mathematical objects and generality

The foundations have three layers:

1. `L2.mean`, `L2.center`, and `L2.variance` are defined on a.e. equivalence classes in real `L²(μ)` for probability measures on any measurable space. Variance is the squared `L²` norm after centering, with values in `NNReal`.
2. `Energy.Functional X` is `X → ENNReal`. Its finite domain `energy.domain` carries a proof excluding `⊤`; only then does `finiteValue` convert the value to `NNReal`. Infinite energy is never silently converted to zero by `toNNReal` for optimization.
3. `Poincare.TestFamily` records only a test type, finite nonnegative variance, and energy. Its optimum is the supremum of extended Rayleigh quotients; it assumes no measure, smoothness, closedness, or Markov property.

On the finite-energy domain, `Poincare.L2Energy.constant μ energy` and
`Poincare.L2Energy.Holds μ energy C` satisfy

```text
Poincare.L2Energy.Holds μ energy C ↔ Poincare.L2Energy.constant μ energy ≤ (C : ENNReal).
```

The conventions are `0 / 0 = 0` and positive variance divided by zero energy equals `⊤`.
An empty test class has optimal constant zero; a test with positive variance and zero energy
forces the optimum to `⊤`. The theorems in [SmoothTest/Optimal.lean](SmoothTest/Optimal.lean)
explicitly cover these cases.

The [energy-comparison](L2/Comparison.lean) direction is: for the same measure, `lower ≤ upper`
implies `Poincare.L2Energy.constant μ upper ≤ Poincare.L2Energy.constant μ lower`.
Increasing energy both shrinks the finite domain and increases the retained denominators,
so equality of the two domains is not required.

## From concrete tests to closed quadratic forms

[PreEnergy](../Energy/Relaxation/Basic.lean) records concrete tests, their realization
`toAmbient`, and finite energy. Sequential relaxation at `x` is the infimum of energy `liminf`s
over test sequences whose realizations converge to `x`. If no such sequence exists, its value
is `⊤`. The definition needs only topology; lower semicontinuity uses a pseudometric assumption.

```text
Relaxation/Basic
  → Relaxation/Approximation
      → Relaxation/LowerSemicontinuous
      → Relaxation/Recovery
  + QuadraticPreEnergy
      → Relaxation/Quadratic → ClosedQuadratic
```

[Relaxation/Approximation.lean](../Energy/Relaxation/Approximation.lean) collects the selection
steps shared by two proofs: a strict relaxed-energy upper bound is realized by a concrete test
in any sufficiently small neighborhood, and dense realization supplies approximating sequences.
It assumes neither an optimal test nor closability.

The proved analytic results include:

- Sequential relaxation is lower semicontinuous in any pseudometric ambient space, without quadraticity or density.
- Every finite-relaxed-energy point has a recovery sequence whose energies converge to the relaxed energy.
- With dense realization, every point has a recovery sequence, including points of energy `⊤`. The empty-test-class example shows that density cannot be dropped here.
- Relaxation of a quadratic pre-energy satisfies quadratic scaling and the full extended parallelogram identity. Adding dense realization gives `ClosedQuadratic`.

`ClosedQuadratic` includes the value at zero, scaling by nonzero real numbers, the parallelogram
identity, lower semicontinuity, and density of the finite domain. The finite domain is packaged
as a real submodule. Scaling by zero is handled separately, yielding zero energy even when the
original vector has energy `⊤`. The generic quadratic-closure theorem does not require raw
energy to agree on realization fibers.

[Relaxation/Contraction.lean](../Energy/Relaxation/Contraction.lean) gives a separate conditional
transfer: a continuous transformation satisfying `RelaxedContractionBound` on realizations of
concrete tests decreases relaxed energy everywhere. The concrete smooth-gradient implementation
proves this premise for every normal contraction in [Dirichlet.lean](../Energy/SmoothGradient/Dirichlet.lean),
giving the Markov/Dirichlet property for every Borel probability law.

## Euclidean implementation and affine support

[Energy.SmoothGradient.Test](../Energy/SmoothGradient/Basic.lean) consists of globally `C∞`
real functions with proofs of `L²(μ)` membership and integrability of the squared gradient.
Finite energy is `∫ ‖gradient f x‖² ∂μ`.
**In the project's pinned Mathlib v4.33.0, ordinary `C∞` is `ContDiff ℝ ∞`;
`ContDiff ℝ ⊤` means analyticity.**

Quadraticity of the smooth-gradient pre-energy and density of its realization are proved.
Density uses Mathlib's density of compactly supported smooth functions in `L²`, with continuity
and compact support of the gradient supplying energy integrability. This is `L²` density;
no graph-norm-core assertion is added.

The concrete closed quadratic form uses a finite-dimensional real Hilbert space with a Borel
measurable space and second-countable topology. It applies to any probability measure, without
a density, log-concavity, compact support, or nondegenerate covariance assumption.

[AffineSupport.lean](../Probability/AffineSupport.lean) takes the affine span of the topological
support and proves closedness, measurability, full measure, and minimality. After choosing an
origin in the support, the measure is represented on the direction space of its affine support.
[intrinsicL2Equiv](../Energy/SmoothGradient/Intrinsic/Basic.lean) is a linear isometric
equivalence between the original and intrinsic `L²` spaces. Compute smooth-gradient relaxation
in the intrinsic space and pull it back along this equivalence to obtain
`Energy.SmoothGradient.Intrinsic.energy` and its closed-quadratic-form theorem.

This includes proper affine supports and zero-dimensional carriers. It removes normal directions,
but not automatically other singularities within the affine support. Equality of ambient and
intrinsic relaxation energies is proved. Preservation of raw test energy is guaranteed in the
orthogonal-extension construction; pointwise agreement for arbitrary ambient tests cannot be assumed.

## Distinguishing the four interfaces

| Interface | Tests or energy | Status |
| --- | --- | --- |
| `Poincare.SmoothTest.constant` | Globally smooth `L²` tests with finite gradient energy | Used by Gaussian and tensorization results |
| `Poincare.L2Energy.constant μ energy` | Finite domain of any extended energy | Generic optimizer and order law proved |
| `Poincare.SmoothGradient.Intrinsic.constant` | Selected intrinsic-affine relaxation | Energy, closed quadraticity, and order law proved |
| `Poincare.LocalSlope.Intrinsic.constant` | Locally Lipschitz/local-slope tests on the intrinsic law | Definition and general log-concave constant comparison completed |

The Blueprint's `C_P^can` abbreviates the third row. The Lean name `SmoothGradient.Intrinsic`
identifies the energy type and intrinsic coordinates. Constant comparison does not assert
pointwise equality of local-slope energy and gradient relaxation. The covariance-weighted
`C_P^aff` is a different energy constant for the CMH route, not an alias for the unweighted
constant of the same measure.

The proved bridges proceed from ambient/intrinsic equality to smooth-test/relaxed constant
equality, then to the locally Lipschitz literature constant for general log-concave laws
(`KLS/LogConcave/Poincare.lean`). The smooth-test/relaxed bridge uses the relaxation upper bound,
approximating sequences, and `L²` continuity of variance; it does not depend on raw/core
agreement or Cheeger identification.

The first two steps have [12 proved comparison theorems](Euclidean/README.md), exported by
`Foundation`. Two certificates package all conclusions; axiom guards cover the 12 theorems
and the added key helpers.

## Raw energy, agreement, and remaining work

For `μ = δ₀`, the functions `0` and `id` represent the same zero `L²` element, but have raw
gradient energies `0` and `1`. Raw energy therefore cannot agree on `L²` fibers for arbitrary
singular measures.

[FormCore.lean](../Energy/Form/Core.lean) distinguishes:

- `RespectsAmbientFibers`: raw energy agrees on each realization fiber;
- `AgreesOnTests`: a specified ambient energy equals raw energy on every test;
- `SequentiallyGenerates`: that ambient energy equals sequential relaxation;
- `IsSequentialCoreFor`: both agreement and generation.

The last is the project's precise specification; equivalence with the literature's graph-norm
core has not been established. None of these properties is a field of `ClosedQuadratic`.

The Markov/Dirichlet witness for smooth-gradient relaxation and its intrinsic pullback is proved
in `Energy/SmoothGradient/Dirichlet.lean` for arbitrary Borel probability laws. Raw/core agreement
under local density assumptions (`LocalDensity`) is proved in `Energy/SmoothGradient/Core.lean`;
without density it fails for the ambient pre-energy (`Energy/SmoothGradient/NormalDirection.lean`).
The earlier status recorded here established `Ecan = 2 Chμ` in `Energy/Cheeger/Basic.lean` under
intrinsic absolute continuity, using the local-slope convention and covering all log-concave laws;
at that stage, identification for arbitrary singular laws, a self-adjoint generator, a semigroup,
and reciprocal spectral-gap interfaces were incomplete. Whitening and affine/isotropic reduction
are proved in `KLS/LogConcave/Isotropic.lean`. The one-dimensional log-concave bound
`C_P^lit(ν) ≤ 4·Var_ν` is proved in `KLS/LogConcave/Line/SharpPoincare.lean`; the old coefficient-12
bound has an independent proof. `LocalSlope/Basic.lean` includes the zero constant for a
zero-dimensional direction space. Equivalence of the legacy smooth-test, ambient relaxed,
and selected intrinsic-affine constants is proved in Lean. The literature's locally Lipschitz
constant and its comparisons in the absolutely continuous and general log-concave cases are
also formalized. Distinct Blueprint nodes track remaining work. `KLS.Conjecture` in
`KLS/Statement.lean` precisely defines the dimension-free target but does not prove it.

## Sources and checks

Mathematical sources are documented near the declarations. The legacy smooth-test interface
explains the formula from historical manuscript Definition 2.1 and the local choice of test
domain; smooth density cites `Lp.dense_hasCompactSupport_contDiff` in the pinned Mathlib.
The generic relaxation and optimization layers are constructions proved in this project.
The Blueprint separately records the sources and status of literature identifications and long routes.

The organization into mathematical meaning, concrete examples, entry points, scope, and builds
follows a [pinned formech revision](https://github.com/lyw-ops/formech/tree/d0bb1913acc1f710ba6eadf1244b633abbc75fb9).
That reference influences presentation only; it is not mathematical evidence for KLS.

Run from `formalization/`:

```sh
lake build Examples
lake build solutions.FoundationAxiomAudit
lake build
```

In the default build, [FoundationAxiomAudit.lean](../../../solutions/FoundationAxiomAudit.lean)
fixes the transitive axiom sets of eight core declarations to `propext`, `Classical.choice`,
and `Quot.sound`. It supplements the four existing node certificates and Gaussian audit in
this recorded batch without adding a ledger node. The complete build checks Lean proofs;
alignment with the literature still requires reviewing the interface boundaries above.
