# Affine-support transport of the smooth pi Buser theorem

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proof

`LogConcave/SmoothBuser.lean` owns the geometric conclusion after heat correlation,
relative perimeter and Cheeger infimum equality. The new theorem extends that module
without changing its earlier signatures. For any finite-dimensional log-concave law
`μ`, let `ν = Probability.intrinsicMeasure μ` on the direction of its affine support.
Assume explicitly that `ν = volume.tilted (-U)` for a smooth convex `U`.

The theorem `LogConcave.inverseScale_sq_le_pi_literature_of_intrinsic_smooth_tilt`
proves the exact extended-real conclusion
`Isoperimetry.inverseScale μ ^ 2 ≤ ENNReal.ofReal π *
Poincare.LocalSlope.Intrinsic.constant μ`. It chooses an intrinsic Borell density
from log-concavity, applies the proved smooth-model Minkowski comparison to `ν`,
then uses `Isoperimetry.constant_eq_minkowskiConstant_intrinsic` and both sides of
`LogConcave.smoothTest_constant_eq_intrinsic_and_localSlope` to identify the
literature constant without taking the intrinsic law twice. The statement covers
all affine-support dimensions, including zero, and the zero/infinite optimal
Poincare constants inherited from the smooth theorem.

The separate theorem `inverseScale_sq_le_pi_literature_of_finrank_eq_zero`
proves the same target for every zero-dimensional law, without log-concavity or
smoothness. Here `Isoperimetry.constant μ = ⊤`, hence `inverseScale μ = 0`.

`research/audits/HeatBuserBridgeAudit.lean` contains two new full-signature
clients, for a total of eleven. Their transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Remaining boundary

An arbitrary intrinsic Borell law need not have a globally smooth convex
potential. The present heat gradient and small-time perimeter proofs use that
potential. No smooth-law approximation with the required Poincare and Cheeger
constant stability, or a nonsmooth heat/perimeter transfer, is present. Thus the
unrestricted log-concave pi Buser theorem and dimension-free KLS bound stay open.
The affine-support normalization is now closed once the intrinsic pi estimate
is available; it is not a separate remaining gap.

## Verification

The strict client, full verifier, source hashes, frozen snapshot and isolated-index
progress synchronization are recorded in
`build/audit/affine-smooth-buser/final-snapshot.json` after verification.
