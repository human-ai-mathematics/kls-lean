# From smooth tests to the selected Poincaré constant

This batch of proved comparison theorems connects three objects: the smooth-test constant,
the ambient-relaxation constant, and the project's selected intrinsic-affine-relaxation constant.
The existing Gaussian and finite-dimensional tensorization results can now be transferred to
the selected constant through these equalities.

**All 12 comparison theorems are proved. Both certificates pass transitive axiom checks, and
the ledger status is `proved / checked_by: lean`.** The original assumptions and types are
unchanged; the declarations are now exported by `Poincare.Foundation` and the root aggregate.
Later batches also proved the comparison with the literature's locally Lipschitz constant for
general log-concave measures, and Cheeger-energy identification when the intrinsic law is
absolutely continuous. Unconditional Cheeger identification for arbitrary singular laws,
Cheeger–Buser comparison, and KLS remain unproved in this recorded status.

The general log-concave version is in [Poincare.lean](../../KLS/LogConcave/Poincare.lean):
the existing `KLS.LogConcave μ` implies equality of the smooth-test, intrinsic smooth-gradient,
and local-slope constants, hence equality with the selected constant. Intrinsic absolute
continuity is proved in [AbsoluteContinuity.lean](../../KLS/LogConcave/Density/AbsoluteContinuity.lean),
not imposed as an extra assumption. This covers ambient singularity and zero-dimensional support.
The full Borell density representative, local bounds, and moment theorems were also completed by
later certificates.

Public names reflect mathematical roles: `Poincare.SmoothGradient.Intrinsic.constant` is the
selected constant, `Poincare.SmoothGradient.Ambient.constant` is the relaxation constant on the
ambient space, and `Poincare.L2Energy.constant μ energy` is the generic optimizer.
`Poincare.CovarianceGradient.Intrinsic.constant` is the affine covariance constant `C_P^aff`
used by the CMH route; see [Intrinsic.lean](../CovarianceGradient/Intrinsic.lean).
[Translation.lean](../CovarianceGradient/Translation.lean) proves its invariance under ambient
translation for arbitrary Borel laws. [Comparison.lean](../LipschitzGradient/Comparison.lean)
proves that the optimal constant of unit-weight Lipschitz-gradient relaxation equals the legacy
and literature constants. Thus, for identity covariance, `C_P^aff` equals the preceding three
constants; in general, `C_P^lit ≤ ‖Σ‖ C_P^aff`. For `hμ : KLS.LogConcave μ`, use
`hμ.intrinsicSmooth_constant_eq_localSlope` directly. See the [naming conventions](../../../../research/naming.md)
for the scope of the naming cleanup and reasons for retaining longer names.

## Entry points

| Purpose | File | Contents |
| --- | --- | --- |
| Geometric comparison and degenerate cases | [LemAmbientIntrinsicPoincareComparison.lean](../../../../solutions/LemAmbientIntrinsicPoincareComparison.lean) | 5 declarations, 4 applications |
| Abstract comparison and future Gaussian use | [LemLegacyRelaxedPoincareComparison.lean](../../../../solutions/LemLegacyRelaxedPoincareComparison.lean) | 7 comparison declarations, 8 applications |
| Constant comparison for any concrete pre-energy | [Poincare/Relaxation.lean](../Relaxation.lean) | Raw test-family definition, finite-constant equivalence, equality of extended optimal constants |
| Comparing energies in two coordinate systems | [Energy/SmoothGradient/Intrinsic/Comparison.lean](../../Energy/SmoothGradient/Intrinsic/Comparison.lean) | Test restriction, test extension, relaxation equality |
| From energy equality to constant equality | [Comparison.lean](../SmoothGradient/Comparison.lean) | Comparison of the two relaxed `Holds` predicates and constants |
| Connection to the legacy smooth-test interface | [Comparison.lean](../SmoothTest/Comparison.lean) | Identification of the raw test domain and two levels of constant comparison |

## Mathematical statements

For any probability law `μ` and concrete finite pre-energy `P` on real `L²(μ)`, define

```text
TestFamily.ofPreEnergy μ P
  Test     = P.Test
  variance = L2.variance μ ∘ P.toAmbient
  energy   = P.energy
```

The abstract comparison theorem proves that, for every `C : NNReal`, the inequality on the raw
test family is equivalent to the inequality on the finite-energy domain of the relaxation.
The two `ENNReal` optimal constants are equal as well. No density, quadraticity, or raw/core
agreement is required. The test class may be empty, the constant may be zero, and the optimal
constant may be infinite.

The finite-dimensional Euclidean implementation proves exact equality between ambient
smooth-gradient relaxation and intrinsic-affine relaxation pulled back to the original `L²(μ)`.
Their finite-energy domains, valid finite constants, and extended optimal constants therefore
agree. Measures may be singular or have proper affine support or zero-dimensional support;
neither second moments nor log-concavity are required.

The final group identifies SmoothTest `Admissible` with `Energy.SmoothGradient.Test`, giving

```text
Poincare.SmoothTest.constant μ
  = Poincare.SmoothGradient.Ambient.constant μ
  = Poincare.SmoothGradient.Intrinsic.constant μ.
```

The `ProbabilityMeasure → Measure` coercion is omitted here. The actual finite-constant
interface explicitly uses `C : NNReal` and `(C : ℝ)` in the legacy interface; it never converts
an infinite optimal constant to a real number. Both test classes require ordinary `ContDiff ℝ ∞`,
`L²`, and an integrable squared gradient. The normalization is always `Var ≤ C ∫ ‖gradient‖²`.

## A directly usable invocation

The following invocation was compilation-checked in the second certificate entry point, using
the proved Gaussian theorem and comparison bridge:

```lean
import FunctionalInequalities.Poincare.SmoothTest.Comparison
import FunctionalInequalities.Poincare.Gaussian.Real

open FunctionalInequalities

#check (fun (m : ℝ) (v : NNReal) ↦
  (Poincare.SmoothTest.holds_iff_intrinsic
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m v)) v).mp
      (Poincare.SmoothTest.holds_gaussianReal m v))
```

Here `v` is the variance, including the Dirac case `v = 0`. The bridge transfers valid constants
and the exact optimum of the SmoothTest Gaussian result to the selected interface. The entry
point also checks transfer for arbitrary dimension, empty test types, and infinite constants.

## Proofs and sources

1. Restrict an ambient test to the affine support: its gradient projects onto the tangent direction, so raw energy can only decrease.
2. Extend an intrinsic test along orthogonal projection: this eliminates normal variation and preserves raw energy. The off-support branch of the existing `Probability.intrinsicMap` cannot be used here, since that map is only guaranteed to be measurable.
3. Apply both constructions termwise to approximating sequences and use the existing intrinsic `L²` isometric equivalence to obtain energy equality.
4. For any pre-energy, relaxation does not increase energy on raw tests, giving one direction of constant comparison. For the converse, use a recovery sequence and `L²` continuity of variance at each finite-energy point. This also handles `C = 0`, without recovery at infinite-energy points or a density assumption.
5. Identify the legacy test domain using `L2.coe_variance_eq_pointwise`, almost-everywhere equality of representatives, and identical gradient integrals. Valid finite constants are then finite upper bounds for the relaxed optimum. Use its `toNNReal` when finite; when infinite, the valid set is empty. This gives the legacy infimum equality without separately assuming attainment.

The mathematical specifications come from the local Blueprint nodes
`thm:ambient-intrinsic-relaxation-equality`, `cor:ambient-intrinsic-constant-equality`,
`thm:legacy-relaxed-holds-equivalence`, and `thm:legacy-canonical-constant-comparison`.
The abstract pre-energy version and the division into concrete helpers are local design choices.
Definition 2.1 of the historical manuscript supplies only the variance/gradient-energy
normalization; it is not a direct source for these comparison statements for arbitrary Borel measures.

These theorems do not require the raw energy of a test to equal its relaxed energy. Later modules
connect the literature's locally Lipschitz constant, and whitening and affine/isotropic reduction
have also been proved. The Markov/Dirichlet property of smooth-gradient relaxation applies to
every Borel probability law. In this recorded status, `Ecan = 2 Ch` uses the local-slope convention
and is proved when the intrinsic law is absolutely continuous, covering all log-concave laws;
unconditional identification for arbitrary singular laws remains incomplete. `LogConcave` and
the main KLS proposition have public definitions, but KLS itself is unproved. The presentation
follows the project's formech style: purpose and examples first, then exact scope, sources,
and remaining work.

## Build and status

Run from `formalization/`:

```sh
lake build solutions.LemAmbientIntrinsicPoincareComparison
lake build solutions.LemLegacyRelaxedPoincareComparison
lake build
```

The default build in this recorded status checks 24 certificates, axiom guards, and usage examples.
This comparison batch has no proof placeholders. The added variance-continuity theorem and
relaxation comparisons for continuous test maps also have axiom guards. The two nodes' mathematical
specifications are in the [ledger](../../../../research/a-series/ledger.yaml).
