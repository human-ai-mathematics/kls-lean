# Generator composition and positive-time Gaussian profiles

Date: 2026-09-24. Local proof continuation; no commit or push.

## Placement and scope

Extend `HeatSemigroup/ChainRule.lean`, `ReversePoincare.lean` and
`GaussianProfile.lean` in their existing owning namespace. No API migration.
The first module identifies the concrete generator domain from smooth compact test
pairings using the actual graph core and self-adjointness. The reverse estimate
supplies L2 integrability of the Gamma field for positive-time bounded heat data.
The Gaussian integration boundary consumes both results and the scalar extension.

For A = T* T, a C1 tilted potential, F in D(A), globally smooth Phi with Phi(0)=0
and bounded value and first two derivatives, the additional condition Gamma(TF,TF)
in L2 yields a genuine u in D(A) with representatives

- u = Phi(F);
- Au = Phi'(F) AF - Phi''(F) Gamma(TF,TF).

The L2 condition is substantive: arbitrary D(A) data only supply an L1 Gamma field.
No domain or core conclusion is assumed. The smooth-test identity extends in the
graph norm, witnesses membership in D(A*), and uses self-adjointness to identify A.

For 0 < eps < 1/2 and 0 <= F <= 1-2 eps, the actual shifted Gaussian profile satisfies

`A[I(F+eps)-I(eps)] = -quantile(F+eps) AF + Gamma(TF,TF)/I(F+eps)`.

The constructed smooth extension is eliminated from the conclusion. In the smooth
convex potential model, bounded f at positive time has Gamma(T P_t f,T P_t f) in L2
by the existing M/sqrt(2t) bound. If 0 <= f <= 1-2 eps, positivity and essential-bound
preservation give the range of P_t f. The positive-time frontend therefore needs
neither a separate Gamma integrability nor an evolved-data range assumption.

## Validation and remaining work

Five independent full-signature clients in `research/audits/HeatCompositionDomainAudit.lean`
check recognition, composition, positive-time Gamma integrability, the Gaussian
operator identity and its heat frontend. Strict compilation and transitive axiom
checks precede the full verifier. Snapshot receipt:
`build/audit/heat-composition-domain/final-snapshot.json`.
The actual Git index and all unrelated dirty work are preserved; progress generation
uses an isolated index and object directory.

Next: prove the squared BGL heat interpolation, its time derivative and integrated
estimate, then endpoint limits and epsilon/range-margin removal. Domain membership
alone does not prove time differentiability of the nonlinear composition along heat
trajectories. No coefficient has changed: the bounded-data gradient estimate remains
M/sqrt(2t), and the small-time perimeter coefficient remains sqrt(2t). The sharper
Gaussian-profile estimate, general-law passage, pi Buser and dimension-free KLS remain
open. This local receipt is not remote CI or a completed route certificate.
