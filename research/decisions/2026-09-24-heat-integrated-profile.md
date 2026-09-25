# Integrated Gaussian profile inequality with a range margin

Date: 2026-09-24. Local continuation; no commit or push.

## Placement and continuity

Extend `Analysis/Semigroup/Generated/TimeDerivative.lean` with
`continuousOn_apply_curve`: a strongly continuous contraction semigroup applied to
a continuous varying datum is continuous on any set of nonnegative times. This
includes time zero. The proof uses the triangle inequality, contraction for the
varying datum and strong continuity for a frozen datum. No operator-norm continuity
is assumed. Extend `L2/Composition.lean` with `continuous_integral_mul_sq`, proved
by the bounded-multiplier inner-product representation of the quadratic functional.

Extend `HeatSemigroup/GaussianProfile.lean` at the existing integration boundary.
Choose one smooth Lipschitz extension Phi of the shifted Gaussian profile and put

`G(r) = compLp Phi(P_(t-r) f) + const(I(eps))`, `Y(r) = P_r G(r)`.

The same G is used throughout [0,t]. Range preservation identifies G(r) with
I(P_(t-r)f+eps) for every r <= t. The inner heat orbit, Lipschitz composition and
outer varying-data semigroup prove continuity on the closed interval. The bounded-test
square Q(r)=int beta Y(r)^2 is therefore continuous at both endpoints.

For each interior time s, the previous local derivative curve agrees with this
fixed curve near s as an L2 class. Eventual equality transfers the derivative and
its quantitative bound. The convex-interval mean-value theorem then integrates the
constant bound without assuming integrability of a time derivative.

## New results

In the full-dimensional log-concave tilted-law model with unit weight, a smooth
convex potential, 0 < eps < 1/2, 0 <= f <= 1-2 eps a.e. and t > 0, construct an
actual L2 class g represented by I(f+eps). For every nonnegative, a.e. bounded
strongly measurable beta,

`2t int beta Gamma(T P_t f)`

`  <= int beta I(P_t f+eps)^2 - int beta (P_t g)^2`.

The two endpoint identities are Y(0)=I(P_t f+eps) and Y(t)=P_t I(f+eps).
The proof retains the terminal square term and does not drop it to claim an
improved heat constant.

A second theorem constructs a single g independent of the test and proves

`2t Gamma(T P_t f) <= I(P_t f+eps)^2 - (P_t g)^2` a.e.

L2 representative uniqueness identifies the initial profile classes produced by
different tests. The terminal profile square is integrable using the actual
composition-domain class plus the constant I(eps). Nonnegative compactly supported
smooth tests detect the a.e. order through the existing TestFunctionOrder theorem.
All spatial pairings used to combine or subtract integrals are proved integrable.
No uncountable intersection of a.e. sets is used.

## Validation and remaining work

Four independent full-signature clients in `research/audits/HeatIntegratedProfileAudit.lean`
check varying-data continuity, quadratic functional continuity, the tested integrated
bound and its a.e. form. Strict compilation, transitive standard-axiom checks and
full project verification are required. Receipt:
`build/audit/heat-integrated-profile/final-snapshot.json`.

Progress views are generated with an isolated Git index and object store. The real
index and unrelated dirty work are preserved. Verification is local, not remote CI.

Next remove the epsilon/range margin for arbitrary 0 <= f <= 1 data, using scaled
inputs and convergence of the actual heat and closed-gradient fields. This needs
explicit L2 convergence of Gaussian compositions and passage of the squared terms.
The unregularized Gaussian BGL estimate, improved 2 sqrt(t/pi) perimeter coefficient,
general-law passage, pi Buser assembly and the dimension-free KLS bound remain open.
