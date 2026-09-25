# General nonsmooth π-Buser comparison through Gaussian smoothing

Date: 2026-09-26. Local continuation; no commit or push.

## Placement and proved scope

`KLS/Geometry/Cheeger/Stability.lean` owns a general stability theorem for the
Minkowski Cheeger infimum. A finite uniform lower bound passes from probability
laws converging on every measurable set to an absolutely continuous limit.
The proof first transports the smooth Lipschitz `[0,1]` test inequality: setwise
convergence controls every superlevel balance, dominated convergence controls
its integral, and the resulting weak convergence controls the bounded
continuous gradient. The converse smooth-test characterization is proved by
distance cutoffs, smooth approximation and the actual Minkowski-content
liminf. This does not claim convergence of the perimeter of each domain.

`KLS/LogConcave/Density/GaussianBuser.lean` applies this theorem to the actual
normalized Gaussian convolution of a Borell probability density. The
approximants have strictly positive `C∞` convex potentials. Their intrinsic
literature Poincaré optima satisfy the previously proved upper bound by the
source optimum plus `1/(2s)`, and their masses converge on every measurable
set. The existing smooth-model π-Buser theorem yields a uniform finite
Cheeger lower bound for every strict finite upper bound on the source
Poincaré optimum. Stability passes it to the source, and a limit over finite
bounds gives the exact extended-optimum statement. An infinite source optimum
is handled directly. No source moment, compact support, smooth density, or
optimal-constant attainment is assumed.

The final theorem
`LogConcave.inverseScale_sq_le_pi_literature` proves, for every
finite-dimensional log-concave probability law `μ`, including every affine
support dimension and dimension zero,

`Isoperimetry.inverseScale μ ^ 2 ≤ ENNReal.ofReal Real.pi *
 Poincare.LocalSlope.Intrinsic.constant μ`.

Together with the existing Cheeger direction, this closes the numerical
comparison in `thm:logconcave-cheeger-poincare-comparison`. The independent
full-signature client `GaussianBuserPassageAudit.lean` checks the stability
bridge, actual Borell source, general affine law and zero-dimensional case.
Strict compilation reports only `propext`, `Classical.choice` and `Quot.sound`
as transitive axioms.

## Remaining boundary

The pointwise relative-perimeter limit of an arbitrary fixed smooth domain
is not asserted; support-boundary terms make that claim inappropriate. The
proved Cheeger-infimum passage is sufficient for the numerical Buser theorem.
Metric BV identification remains a separate literature comparison in the
Blueprint prose. The dimension-free KLS bound and the open conditions in its
four active routes are not proved by Cheeger--Buser alone.

## Source evidence

- Cheeger stability source SHA-256: `590dff793ba5bc212b9dafe4b1fe8ad0e129b53c6c18fb0c597317ebdff798b1`.
- Gaussian Buser source SHA-256: `23d91f98d6a557e154b428e77723cac9923f63fa38b2aab3c01bac0168a580cb`.
- Full-signature client SHA-256: `583c7560c2d616fba6063195311b213631f1b5fc8948b1cb85d0d8e3d82f4575`.
- Frozen full-verifier receipt: `build/audit/nonsmooth-pi-buser/final-snapshot.json`.
