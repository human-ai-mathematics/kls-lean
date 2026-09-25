# Strong Gaussian interpolation and the tested square derivative

Date: 2026-09-24. Local continuation; no commit or push.

## Placement and method

Extend `Analysis/Semigroup/Generated/TimeDerivative.lean` with the product rule
for a differentiable Hilbert-space curve F under the generated semigroup:

`d/ds P_s F(s) = P_s F'(s) - A P_s F(s)`.

When F(s) belongs to D(A), generator commutation identifies this as
`P_s(F'(s) - A F(s))`. The proof splits difference quotients and uses contraction
and strong continuity for the varying-datum term. No operator-norm differentiability
assumption is added. Extend `L2/Composition.lean` with differentiation of a bounded-test
quadratic integral: its derivative is the actual L2 mixed pairing.

Reuse the existing tested interpolation module without editing it. Extend
`HeatSemigroup/GaussianProfile.lean` at the scalar/heat boundary. No public names move.

## Concrete results

Work in the full-dimensional log-concave tilted-law model with unit weight and a
smooth convex potential. Let 0 < eps < 1/2, 0 <= f <= 1-2 eps a.e. and 0 < s < t.
The inner heat orbit is in D(A). The previous round supplies both the actual
Gaussian L2 time derivative and its composition-domain generator formula.
Their quantile*AF terms cancel in the product rule.

An L2 curve G(r), identified with I(P_(t-r)f+eps)-I(eps) a.e. for every r<t, and
an actual L2 class z represented by Gamma(T P_(t-s)f)/I(P_(t-s)f+eps), satisfy

`d/dr [P_r G(r)] at s = -P_s z`.

The class z is constructed as A(u)+w using the genuine composition-domain element
u and the inner derivative w; both representatives are proved. No Gamma integrability
or composition-domain assumption is imposed on the client. The earlier bounded-data
regularity theorem discharges those obligations.

Adding the constant I(eps) to G and proving that the heat semigroup fixes it gives
the same derivative for the positive unshifted profile I(P_(t-r)f+eps). This distinction
matters: the shifted profile multiplied by I^{-1} is not 1.

For every a.e. bounded strongly measurable real test beta, the actual unshifted
interpolation Y_r=P_r G(r) satisfies

`d/dr int beta Y_r^2 at s = -2 int beta Y_s (P_s z)`.

The test need not be nonnegative for this identity. The inputs on the right are L2,
so bounded testing gives an integrable mixed pairing. This is an exact derivative,
not a quantitative dissipation estimate or the integrated BGL inequality.

## Validation and next step

Six independent full-signature clients in `research/audits/HeatStrongInterpolationAudit.lean`
check the varying-data product rule, its domain version, bounded-test quadratic
functional, shifted and unshifted strong interpolation, and the squared derivative.
Strict source/client compilation, transitive standard-axiom reports and full project
verification are required. Receipt: `build/audit/heat-strong-interpolation/final-snapshot.json`.
Progress generation uses an isolated Git index and object store, preserving the actual
index and all unrelated dirty work. This is local verification, not remote CI.

Next prove the weighted semigroup Cauchy-Schwarz inequality and use L1 gradient
self-improvement to bound Y_s P_s z below by Gamma(T P_t f). Then integrate the squared
interpolation inequality, establish endpoints and remove the epsilon/range margin.
The M/sqrt(2t) gradient bound and sqrt(2t) perimeter coefficient remain unchanged;
the sharper Gaussian-profile BGL estimate, general-law passage, pi Buser and KLS are open.
