# Literature gap and smooth-model pi Buser bridge

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and mathematical scope

`LogConcave/WeightedGradient/Poincare.lean` owns the identification between the actual closed
unit-gradient form and the literature Poincare optimizer. `HeatSemigroup/Correlation.lean` owns
the Markov indicator correlation/L1 identity and the small-time perimeter combination.
`LogConcave/SmoothBuser.lean` is the geometric conclusion for a full-dimensional law explicitly
represented as `m.tilted (-U)` with a smooth convex `U`. These modules import the already proved
form, heat, perimeter, and Cheeger equalities in that direction. The generic centered-inner-product
identity stays in `L2/MeanVariance.lean`. Existing public signatures are preserved.

## Proved interfaces

- The optimal Poincare constant of `PreEnergy.normSqEnergy` for the actual closed unit gradient
  equals `Poincare.LocalSlope.Intrinsic.constant` in `ENNReal`, including zero and infinity.
  Every finite upper bound gives the form-domain inequality needed for actual heat decay, so the
  previous explicit gap premise is now discharged for the unit gradient.
- Actual centered heat decay and indicator correlation now accept a positive finite upper bound
  on the literature optimum directly, for arbitrary L2 initial data and every nonnegative time.
  The indicator L1 displacement is exactly twice the loss of centered correlation from the
  variance. Markov positivity, preservation of one, and preservation of the mean justify the
  pointwise absolute-value split and the integral identity; masses zero and one are included.
- Combining this identity with the pi-coefficient small-time perimeter bound gives a smooth
  domain inequality. The fixed time `t = 5C/4` has the certified numerical inequality
  `2 sqrt(5/4) <= pi (1-exp(-5/4))`. Its proof uses the first six nonnegative terms of the
  exponential series and the Mathlib lower bound `3.14 < pi`.
- For every smooth convex tilted full-dimensional law, the inverse smooth relative-perimeter
  Cheeger constant and the inverse Minkowski Cheeger constant satisfy the pi squared comparison
  at every positive finite upper bound `C`. An order argument removes `C` and proves
  `minkowskiConstant(ν)⁻¹ ^ 2 <= ofReal pi * C_P^lit(ν)` at the exact extended optimum, including
  optimum zero and infinity. Infinite perimeters and an empty family of intermediate-mass smooth
  domains are handled by the extended-real infimum.

The independent full-signature client is `research/audits/HeatBuserBridgeAudit.lean`; its nine
transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining full comparison

This is a pi Buser theorem for the **smooth convex tilted model's Minkowski constant**. The
target `Isoperimetry.inverseScale μ ^ 2 <= pi * C_P^lit(μ)` for every finite-dimensional
log-concave law is not asserted. A general intrinsic law has a Borell density but need not have
a smooth convex potential (uniform laws on convex bodies are a basic example). The proved
pi heat/perimeter estimate and its use in `SmoothBuser.lean` retain the smooth-potential
assumption. A source-level approximation/stability theorem must pass the heat/perimeter bound
to arbitrary intrinsic Borell laws, or a different general-law Buser proof must replace it.
The affine-support transport of the final isoperimetric scale must then be used with its exact
normalization. The repository already proves equality of the smooth and Minkowski infima for
laws with a Borell density, so that equality itself is not an open gap.

The full Cheeger–Buser Blueprint node remains pending and the dimension-free KLS statement
remains open. No new axiom, `sorry`, hidden `sorryAx`, or conclusion-bearing assumption was added.

## Verification

Strict compilation, the independent client, frozen full verifier receipt, source hashes and
isolated-index progress synchronization are recorded in
`build/audit/heat-buser-bridge/final-snapshot.json` after verification.
