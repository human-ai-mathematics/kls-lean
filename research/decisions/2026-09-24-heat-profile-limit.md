# Gaussian BGL inequality without an epsilon range margin

Date: 2026-09-24. Local continuation; no commit or push.

## Placement and convergence

Extend `Probability/Line/GaussianProfile.lean` with continuity of the existing zero
extension on the real line. Compose the continuous profile on [0,1] with the clamp
`max 0 (min 1 x)` and identify this with the zero extension. Both endpoints are
included; no endpoint differentiability or global Lipschitz property is asserted.

Promote the existing `L2/Composition.lean` dominated-convergence lemma to the public
`L2.tendsto_toLp_of_dominated`, keeping its statement and proof. It handles real
L2 classes under an L2 envelope along countably generated filters. No aliases or
module moves are introduced.

At the existing `HeatSemigroup/GaussianProfile.lean` boundary, construct actual L2
classes J_eps(u) represented by `I((1-2eps)u+eps)`. Their uniform bound is the scalar
profile maximum `1/sqrt(2*pi)`. Dominated convergence proves J_eps(u) -> J_0(u)
in L2 as eps -> 0, including values u=0 or u=1. These local implementation helpers
need only the probability measure and measurable-space structure.

For 0<=f<=1, apply the previous integrated inequality to f_eps=(1-2eps)f for
0<eps<1/2. Heat linearity and closed-gradient linearity identify the actual terminal
fields with (1-2eps) times those of f, including their a.e. representatives. Thus
the Gamma integral acquires the exact factor (1-2eps)^2.

The bounded-test quadratic functional is continuous on L2. Apply this both to
J_eps(P_t f) and to P_t J_eps(f), using the continuous heat operator in the latter
case. Pass the scalar inequality to eps -> 0 from the right along a nontrivial
filter. No almost-everywhere subsequence or uncountable full-measure intersection
is needed.

## Proved statement

Let nu be the current full-dimensional log-concave tilted law with smooth convex
potential, unit gradient weight, and its constructed heat semigroup P_t. For any
f in L2 with 0<=f<=1 a.e. and t>0, there exists an actual L2 class g with g=I(f) a.e.
such that

`2t Gamma(T P_t f) <= I(P_t f)^2 - (P_t g)^2` a.e.

The bounded nonnegative-test integrated version is proved first. Representative
uniqueness identifies g across different tests, and the existing smooth-test order
detector proves the displayed a.e. version. Every spatial pairing needed for
subtraction is integrable. No epsilon margin or additional domain assumption on f
remains. The generator-domain membership of P_t f is supplied by positive-time
regularity of the actual semigroup.

This is the Gaussian BGL inequality in the stated smooth convex model. It is not
a theorem for every log-concave law, nor a completed pi Buser or KLS route.

## Validation and remaining work

Four independent full-signature clients in `research/audits/HeatProfileLimitAudit.lean`
check scalar continuity, generic dominated convergence, the integrated inequality
and its a.e. form. Strict compilation, standard transitive axiom checks and full
project verification are required. Receipt:
`build/audit/heat-profile-limit/final-snapshot.json`.

The real Git index and unrelated dirty work remain preserved. Progress regeneration
uses an isolated index and object store. This is local verification, not remote CI.

Next derive the improved bounded-data gradient coefficient from this profile bound,
and feed it through the existing duality and recovery interfaces to prove the
2 sqrt(t/pi) L1/perimeter coefficient. Those public constant statements have not
been changed in this round. General-law passage, remaining perimeter interfaces,
spectral decay, pi Buser assembly and the dimension-free KLS bound remain open.
