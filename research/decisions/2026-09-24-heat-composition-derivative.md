# Nonlinear L2 differentiation and tested Gaussian interpolation

Date: 2026-09-24. Local continuation, with no commit or push.

## Placement

Create `L2/Composition.lean` for generic scalar composition along L2 curves,
using Mathlib LipschitzWith.compLp, dominated convergence and bounded multipliers.
Create `HeatSemigroup/Interpolation.lean` for the interior time derivative of the
tested nonlinear heat interpolation. Extend `HeatSemigroup/GaussianProfile.lean`
at the existing scalar/heat boundary. Preserve all previous public signatures.
The library root imports the generic composition module; the Gaussian module
imports the tested interpolation. No reverse import is introduced.

## Proved scope

For a differentiable Lipschitz scalar Phi with Phi(0)=0, a differentiable L2 curve
F and an L2 class w represented by Phi'(F(t))*F'(t), the composition curve has
derivative w at t. First prove affine-direction difference quotient convergence
by L2 dominated convergence. Then estimate the error from replacing a general
curve by its tangent affine curve, using the Lipschitz bound on compLp.
This is curvewise differentiation; global Frechet differentiability of the
Nemytskii map on L2 is neither assumed nor asserted. No pointwise differentiable
representative of an L2 curve is required.

For the concrete heat semigroup and 0 < s < t, the tested identity is

`d/ds int P_s psi Phi(P_(t-s) f) = int P_s psi Phi''(P_(t-s) f) Gamma(T P_(t-s) f)`.

The assumptions are a C1 tilted potential, a bounded generator-domain test psi,
arbitrary f in L2, and a globally smooth scalar function with bounded value and
first two derivatives and value zero at zero. The inner heat orbit has positive
A derivative because of the reversed time parameter. The outer test orbit has
negative A derivative. Both linear generator terms cancel by the previously
proved tested chain rule. No bound on A psi or convexity of U is added.

For 0 < eps < 1/2 and initial range 0 <= f <= 1-2 eps, the constructed global
extension is removed from the interpolation on a neighborhood of every interior
time. Its actual derivative is

`-int (P_s psi / I(P_(t-s) f + eps)) Gamma(T P_(t-s) f)`.

The initial range is propagated by positivity and the essential-bound estimate.
This tested formula needs only the L1 Gamma pairing, not an L2 Gamma assumption.
Separately, an actual L2 curve equal a.e. to I(P_r f+eps)-I(eps) at every r>0
is constructed, and its derivative at t>0 is represented by
`quantile(P_t f+eps) * A(P_t f)`. That result needs no tilted-potential assumption:
the closed-gradient semigroup and its Markov properties supply its inputs.

## Verification and boundaries

Five independent full-signature clients in
`research/audits/HeatCompositionDerivativeAudit.lean` check affine differentiation,
curve differentiation, generic tested interpolation, actual Gaussian L2 differentiation
and the actual Gaussian tested interpolation. Strict elaboration and standard-axiom
reports precede the full project verifier. Snapshot receipt:
`build/audit/heat-composition-derivative/final-snapshot.json`.
Progress records are generated with an isolated index and object store, preserving
the user's actual index and the pre-existing dirty tree.

Next: the squared BGL interpolation and quantitative differential inequality,
weighted Cauchy-Schwarz and L1 gradient self-improvement, integration in time,
endpoint limits and epsilon/range-margin removal. The first tested derivative
is not the squared BGL estimate. The M/sqrt(2t) gradient constant and sqrt(2t)
small-time perimeter coefficient remain unchanged. General-law passage, pi Buser
and dimension-free KLS remain open. Verification is local, not remote CI.
