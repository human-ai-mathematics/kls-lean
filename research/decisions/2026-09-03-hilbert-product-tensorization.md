# Hilbert product encoding and tensorization specification

**Date:** 2026-09-03 (Asia/Shanghai)

**Status:** candidate design audited against the pinned dependency; public statements are
drafted and await human freezing. The deliverable is a compilable declaration skeleton.

## Decision

Use `WithLp 2 (E × F)` for all binary Hilbert products and
`Poincare.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)` for their product laws. Keep the
ordinary product's standard maximum norm intact. Transport measure-theoretic statements through
`MeasurableEquiv.toLp`, and calculus through `WithLp.prodContinuousLinearEquiv`. This avoids
incompatible instances and preserves the exact sum of squared gradient components.

The complete ambient assumptions and both candidate theorem signatures are in `LEAN_DESIGN.md`.
They cover real separable Hilbert spaces with Borel measures, including Euclidean spaces of
dimension zero. Fixed-constant probability/nonnegativity assumptions remain inside `Holds`.
The optimal constants remain extended nonnegative reals, including `⊤`.

## Dependency audit

Audit target: Mathlib v4.33.0, commit `db584cd6d46c92f209a44c0f1c829460d327499d`.

- `Analysis/InnerProductSpace/ProdL2.lean`: Hilbert product inner-product instance and
  `WithLp.prod_inner_apply`.
- `Analysis/Normed/Lp/ProdLp.lean`: `prod_norm_sq_eq_of_L2`, continuous linear equivalence,
  coordinate projections, completeness and second-countability infrastructure.
- `Analysis/Normed/Lp/MeasurableSpace.lean`: transported measurable/Borel structures and
  `MeasurableEquiv.toLp`.
- `Analysis/Calculus/Gradient/Basic.lean`: gradient/Fréchet derivative conversion and uniqueness.
- `MeasureTheory/Integral/Prod.lean`: Fubini, a.e. integrability of sections, and integrability
  of their integrals.
- `Probability/Moments/Variance.lean`: L2 variance formula, transport under measurable maps,
  and variance for additive independent tests. The audited module does not supply the needed
  general nonlinear two-factor variance bound.

## A.e. section contract

The work-package phrase about admissible sections must be understood almost everywhere. It is
false for every section, even for smooth product tests. Take `ν = δ₀` and
`f(x,y) = y² exp(x²)` with a standard Gaussian first factor: the product test and full gradient
are zero almost everywhere, but the section at `y = 1` is not L2. Fubini gives exactly the a.e.
section contract needed by tensorization. Do not strengthen `Admissible` to all-section
admissibility or claim smoothness of a marginal integral from the existing fields.

## Proof plan and module boundary

Reusable product geometry, a.e. section lemmas, the Fubini variance bound, and both public
tensorization theorems are skeletons under `formalization/FunctionalInequalities/`, all ending
with `sorry`. The thin statement entry point under `solutions/` imports and names the two public
declarations and is registered in the default Lake target. It has no proof claim. The ledger
will claim `checked_by: lean` only after human freezing and completion of the separate proof
phase with its certification gates.

No change of normalization, Gaussian analysis, closed Sobolev extension, or optimal-constant
attainment is part of this decision.
