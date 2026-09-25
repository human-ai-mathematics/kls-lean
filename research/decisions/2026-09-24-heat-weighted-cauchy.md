# Weighted heat Cauchy-Schwarz and Gaussian dissipation

Date: 2026-09-24. Local continuation; no commit or push.

## Placement and proof

Create `L2/PositiveMap.lean` in the existing generic L2 family. A positive real
linear map P on scalar L2 preserves the pointwise matrix inequality

`a >= 0, c >= 0, b^2 <= a*c  ==>  (P b)^2 <= (P a)*(P c)` a.e.

Positivity is tested on `q^2 a - 2 q b + c` for rational q. Countability gives
one common full-measure set; density and continuity of each scalar polynomial
then give all real tests. Its discriminant is nonpositive. No uncountable
intersection of full-measure sets is used. The map need not be continuous,
contractive or constant preserving. No division by a or c is used, so zero
weights are included.

Extend `HeatSemigroup/SelfImprovement.lean` with the weighted consequence of its
existing L1 gradient bound. If a,c are nonnegative L2 classes and
`|T f|^2 <= a*c`, then `|T P_s f|^2 <= P_s a P_s c` for s >= 0.
The norm field is constructed in L2; both its representative and the positivity
hypothesis of the actual heat operator are discharged.

Extend `HeatSemigroup/GaussianProfile.lean` with the actual profile specialization
and the tested square differential inequality. Add the SelfImprovement import at
this integration boundary. Existing public signatures are unchanged.

## Concrete result and scope

Work in the full-dimensional log-concave tilted-law model with a smooth convex
potential and unit gradient weight. Assume `0 < eps < 1/2`,
`0 <= f <= 1-2 eps` a.e. and `0 < s < t`. Put

- F = P_(t-s) f,
- a = I(F+eps), z = Gamma(T F)/I(F+eps),
- Y_s = P_s a.

The actual inner range is preserved by the heat operator. The positive profile
has no zeros on that range, hence `a*z = Gamma(T F) = |T F|^2` a.e.
The previous interpolation construction supplies a and z as genuine L2 classes.
The semigroup law identifies the outer-evolved gradient with T P_t f, proving

`Gamma(T P_t f) <= Y_s P_s z` a.e.

For every nonnegative, a.e. bounded strongly measurable real test beta, the
existing exact square derivative and this inequality yield

`d/dr int beta Y_r^2 at s = -2 int beta Y_s P_s z`

`                         <= -2 int beta Gamma(T P_t f)`.

Both pairings are integrable; the sign reversal by -2 is explicit. The theorem
constructs the profile curve and the actual dissipation class together with the
exact derivative and its bound. It does not assume the quantitative conclusion,
a pointwise classical gradient, or extra Gamma integrability.

## Validation and remaining work

Four independent full-signature clients in `research/audits/HeatWeightedCauchyAudit.lean`
check the generic positive-map theorem, weighted gradient consequence, Gaussian
pointwise bound and quantitative tested derivative. Strict source/client compilation,
standard transitive axiom checks and full project verification are required.
Receipt: `build/audit/heat-weighted-cauchy/final-snapshot.json`.

Progress generation uses an isolated Git index and object store. The real index
and unrelated dirty work are preserved. This is local verification, not remote CI.

Next identify one profile interpolation curve over the entire time interval,
integrate the differential inequality, prove the time endpoints and remove the
epsilon/range margin. The integrated Gaussian BGL bound has not yet been proved.
The existing M/sqrt(2t) gradient bound and sqrt(2t) perimeter coefficient remain
unchanged. General-law passage, the improved 2 sqrt(t/pi) coefficient, pi Buser
assembly and the dimension-free KLS bound remain open.
