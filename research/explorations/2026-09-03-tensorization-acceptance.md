# Poincaré tensorization proof acceptance

**Date:** 2026-09-03 (Asia/Shanghai).
**Node:** `lem:poincare-tensorization`.
**Issue:** [#6](https://github.com/human-ai-mathematics/kls-lean/issues/6).
**Baseline:** `faf782f97eabefbd3d3f2aed50d2907d07ac7a46` on `main`.

## Approval and delivered scope

The user supplied the completed candidate proofs, requested compilation and semantic review,
and then instructed “synchronize acceptance”. The [freeze record](../decisions/2026-09-03-tensorization-freeze.md)
records this acceptance-time human approval, the baseline, both complete public declaration
types, and the verbatim ledger statement. It does not assert a historical freeze before the
candidate proofs were supplied. The earlier statement-phase records remain unchanged.

The accepted result is the fixed-constant inequality with `max C C'` and the extended optimal
constant upper bound, on `WithLp 2 (E × F)` with the transported product probability law.
The test class remains exactly `Poincare.Admissible`: globally smooth real-valued L² functions
with integrable squared canonical gradient. The
[source correspondence review](2026-09-03-tensorization-source-alignment.md) records BGL
Proposition 4.3.1, Courtade's test-class discussion, the dimension-independent Hilbert argument,
and the binary upper bound's role in the upstream `prop:products` dependency chain.

The lifecycle was advanced from `drafted` to `frozen` after the user instruction, then to
`proved` with `checked_by: lean` after the completed proofs, certificate wrappers, and their
dependencies passed review. The checker verifies the resulting state; this record supplies
the approval chronology it does not infer.

## Certificate and concrete interfaces

- `FunctionalInequalities.Poincare.Holds.prod` and `constant_prod_le` are the unchanged
  reviewed public results.
- `FunctionalInequalities.Project.PoincareTensorization` packages `fixed_constant`,
  `optimal_constant`, and their joint `certificate`.
- Its `euclidean_fixed_constant`, `euclidean_optimal_constant`, and `euclidean_certificate`
  specialize to `EuclideanSpace ℝ (Fin m)` and `EuclideanSpace ℝ (Fin n)` for arbitrary
  `m, n : ℕ`, without positivity hypotheses.
- `Solutions.LemPoincareTensorization.certificate` exposes the full Hilbert claim and
  `euclidean_certificate` exposes its concrete finite-dimensional form. The file imports the
  reusable project certificate and is a root of the default `Issue2Solutions` target.

The joint certificate assumes the two measures are probabilities. This adds no restriction
to the fixed-constant implication: its two `Holds` antecedents already carry those instances.
The separate `fixed_constant` interface retains precisely those antecedents.

During review, the only change to the user's mathematical implementation was:

```lean
omit [SecondCountableTopology E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem energy_prod_eq ...
```

This removes unused section assumptions from the energy identity. It changes neither of the
two frozen public declaration types. The remaining implementation changes add proof wrappers
and concrete specializations; module comments and current documentation now describe proved
results instead of the historical 24-placeholder skeleton.

## Mathematical review

Independent reviews covered product geometry/admissibility and variance/tensorization.
No mathematical discrepancy with the approved statement was found:

1. The Hilbert product uses the sum-of-squares norm, and the two section gradients are the
   corresponding projections of the full gradient, proved by the chain rule and Riesz duality.
2. L² and finite energy restrict almost everywhere by Fubini. No every-section claim or
   differentiability of an averaged function is used.
3. Variance decomposition and Jensen retain square integrability and the hypotheses needed
   for each real-integral manipulation. The proof does not exploit nonintegrable integrals
   being assigned zero.
4. The factor inequalities give `C A + C' B`, with `A, B ≥ 0`; the sum is bounded by
   `max C C' * (A + B)`, and `A + B` equals the product energy.
5. The optimal-constant proof uses the defining infima to contradict a hypothetical strict
   reverse inequality. It works with `⊤` and does not require either infimum to be attained.
6. There is no moment, density, positive-dimension or finite-optimal-constant hypothesis.

This review does not certify equality of optimal constants, a finite-family tensorization API,
Sobolev/Dirichlet/spectral-gap equivalences, or the remaining product-case KLS inputs.

## Machine verification and preservation

Both public results and all eight new project/solution wrapper theorems were inspected with
`#print axioms`. Every one depends on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` or additional project axiom. For example, after the default build:

```lean
import solutions.LemPoincareTensorization
#print axioms FunctionalInequalities.Poincare.Holds.prod
#print axioms FunctionalInequalities.Poincare.constant_prod_le
#print axioms FunctionalInequalities.Project.PoincareTensorization.certificate
#print axioms Solutions.LemPoincareTensorization.certificate
#print axioms Solutions.LemPoincareTensorization.euclidean_certificate
```

In addition to the permanent arbitrary-dimension specializations, explicit applications of
the fixed and optimal bounds to `(0, n)`, `(m, 0)`, and `(0, 0)`, and of the joint solution
certificate to `(0, 0)`, were compiled successfully. The proved-source guard traverses the
certificate's local imports; promotion therefore checks the completed reusable proofs too.

The delivered declaration-type output matches the freeze snapshot byte for byte, and the
ledger's `statement` matches its approved string exactly. Their SHA-256 values are:

```text
public type output: 75e576722a02a1c49588534389331ed1f493fec233ee21756e348c23f8424d0a
ledger statement:   a261a6b244ad4e7ea36dd0478f268e8f2d9fad6b5cd99e22317f36bd99075234
```

`Basic.lean`, `Poincare.lean`, `Project/LinearTestLower.lean`, and
`solutions/LemLinearTestLower.lean` are byte-identical to the baseline. The pinned toolchain
and dependency manifest are also unchanged: Lean v4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The local acceptance commands are:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

The recorded results are a valid ledger with two proved nodes and zero errors, all 24 checker
regression tests passing, and a successful default Lean build without warnings.

## Publication evidence

Follow the existing direct-`main` workflow. Publication acceptance also requires a clean
checkout of the delivered commit, with fresh project build artifacts and only the pinned
third-party dependency cache reused, and a successful GitHub Actions run for that same commit.

The final published SHA, clean-checkout result, repeated frozen-type/ledger comparison and
the exact successful Actions URL are attached to
[Issue #6](https://github.com/human-ai-mathematics/kls-lean/issues/6) when those gates
complete. That commit-specific evidence distinguishes the final publication from an earlier
local build or an earlier successful CI run. The issue's checklist is completed only after
the publication gates pass.
