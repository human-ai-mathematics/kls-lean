# Small-time L1 approximation and smooth relative perimeter

## Placement and proved results

The placement plan is in `HANDOFF.md`. The dirty baseline is preserved under
`build/audit/heat-small-time/baseline/`. No existing public signature changes.

- `L2/Duality.lean`: a bounded sign test attains the integral absolute value of any real
  L2 function on a finite measure; bounded pairings control that integral.
- `HeatSemigroup/Approximation.lean`: in the smooth convex tilted-law model, unit weight,
  for all form-domain data and `t >= 0`,
  `integral |f - P_t f| <= sqrt(2t) integral |T f|`.
  The proof differentiates the dual pairing at positive times, compares with `sqrt(2t)`
  on the closed half-line by continuity at zero, and uses the sign test.
  The existing L2 semigroup also contracts L1 distances between L2 inputs.
- The quantitative form approximation bound is
  `integral |f - P_t f| <= 2 integral |f-u| + sqrt(2t) integral |T u|`.
  It gives the explicit recovery criterion: if every positive epsilon admits a form-domain
  approximation with L1 error below epsilon and gradient mass at most `C + epsilon`, then
  `integral |f-P_t f| <= sqrt(2t) C`. This criterion alone is not called a BV theorem.
- `HeatSemigroup/Perimeter.lean` instantiates the actual existing smooth-domain recovery
  sequence, whose members are smooth, globally Lipschitz and between zero and one. It proves
  their weighted-gradient test membership and closed-gradient action, translates the L1
  convergence and the ENNReal gradient limsup, and applies the recovery criterion. Thus for
  a smooth domain `D`, a Borell density `rho` of the same law relative to canonical volume,
  and `t >= 0`,
  `lintegral |1_D - P_t 1_D| <= ofReal(sqrt(2t)) * relativePerimeter rho (interior support) D`.
  The ENNReal version includes infinite perimeter and time zero; the real version requires
  finite perimeter. No compactness or boundedness of the domain is imposed.

No L1 semigroup extension is assumed: all data, including indicators, remain in L2 of the
probability law. The recovery sequence is constructed by the pre-existing theorem
`RelativePerimeter.exists_smooth_recovery_sequence`, not supplied as a new hypothesis of
the perimeter endpoint.

## Constant audit: the sharp BGL input is still missing

The primary source [De Ponti--Mondino, arXiv:1902.03835v2](https://arxiv.org/html/1902.03835v2)
was rechecked during this round. Equations (32)--(33) are stronger than the ordinary reverse
local Poincare inequality proved earlier: they involve the Gaussian isoperimetric profile
`I = gaussianDensity o gaussianCdfInverse`. At K = 0 the profile estimate is
`2t |T P_t f|^2 <= I(P_t f)^2 - (P_t I(f))^2` for `0 <= f <= 1`.
It yields the bounded-data gradient bound `M / sqrt(pi t)` and the small-time coefficient
`2 sqrt(t/pi)` in (8), (48), rather than the present `M / sqrt(2t)` and `sqrt(2t)`.

Consequently, earlier references to the ordinary reverse Poincare result as completion of
Proposition 3.1 (32)--(33) were too strong. The actual Lean statements are correct and unchanged;
this record corrects that route-level identification. The present estimate is a substantive
small-time/perimeter milestone, not the sharp input needed for the target constant pi.

Next: establish the Gaussian-profile BGL estimate (or another rigorously justified route
retaining pi), then strengthen the small-time coefficient. Also open: the nonsmooth/general-law
passage, any required metric-BV/Minkowski/relative-perimeter comparison, spectral-gap decay,
and the exact Buser assembly. The complete Buser node and dimension-free KLS stay open.
Historical decision files are retained unchanged.

## Validation

`research/audits/HeatSmallTimeAudit.lean` checks form-domain data, arbitrary L2 data after positive
heat time, L1 contraction, the finite and extended perimeter statements, and time zero without
a finite-perimeter premise. Ten transitive axiom reports use only standard Lean axioms.
Strict compilation, full build, snapshot-bound audit clients and local-module kernel replay
are recorded in `build/audit/heat-small-time/final-snapshot.json`. Pinned dependency artifacts
are trusted. No commit, push, remote CI or real-index modification is performed.
