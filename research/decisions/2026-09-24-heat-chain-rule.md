# Tested generator chain rule and actual Gaussian profile

## Placement

`Analysis/BakryEmery/WeakGamma.lean` now proves convergence of pairings with uniformly
bounded a.e.-convergent scalar multipliers and two L2-convergent fields. This generic
measure/field result does not assume the Gamma pairing belongs to L2.

`KLS/LogConcave/HeatSemigroup/ChainRule.lean` owns the tested closed-generator scalar
composition identity. It uses the existing smooth generator symmetry, pointwise weighted
Laplacian chain rule and actual operator core. `HeatSemigroup/GaussianProfile.lean` is the
integration boundary with `Probability/Line/GaussianProfile.lean`. Existing APIs are unchanged.

## Proved endpoint

Let `T` be the closed unit-weight gradient, `A = T* T`, and let the full-dimensional
log-concave probability law be `nu = m.tilted (-U)`, with `U` only C1.
For arbitrary `F in D(A)`, bounded `psi in D(A)`, and globally smooth `Phi` with
`Phi(0)=0` and bounded value, first derivative and second derivative:

`int (A psi) Phi(F) = int Phi'(F) psi (A F) - int psi Phi''(F) Gamma(T F,T F)`.

`integrable_chain_pairings` separately proves integrability of all three pairings.
The middle product is represented by `WeakGamma.apply psi (A F)` in the Lean API.
No boundedness of `A psi`, convexity of U, range bound on F, or range-preserving core
sequence is assumed in this generic endpoint.

The proof constructs a genuine smooth operator-core sequence and derives gradient
convergence from `norm(T e)^2 <= norm(A e) * norm(e)`. An a.e.-convergent subsequence
allows continuous nonlinear scalar multipliers to converge. Dominated convergence handles
the fixed fields, and weak-Gamma L1 stability handles the varying fields.

## Gaussian specialization

`integral_adjointComp_mul_shifted_eq` instantiates the actual smooth extension from
`exists_smooth_shifted_extension`, then removes it by neighborhood agreement, including
its first and second derivatives. For `0 < eps < 1/2` and `0 <= F <= 1-2*eps` a.e.:

`int (A psi) shifted(eps,F)
 = int -quantile(F+eps) psi (A F) + int psi Gamma(T F,T F) / I(F+eps)`.

There is no auxiliary extension, approximation-sequence or core premise in this endpoint.
The positive margin keeps the reciprocal profile legitimate. The plus sign of the last
term comes from the nonnegative generator convention `A = -L` and `I'' = -1/I`.

## Remaining work

This is a tested integral identity, not a claim that `Phi(F) in D(A)` for arbitrary F.
In general `Gamma(T F,T F)` is only L1. Next use positive-time bounded-data gradient
regularization where stronger integrability is needed, and prove the time differentiation
and endpoint limits for the BGL interpolation involving
`[P_s(shifted(eps,P_(t-s) f))]^2`. Any required composition-domain identification must be
proved rather than inferred from the scalar or tested identity. Then remove epsilon and
the range margin and derive the sharp gradient and small-time coefficients.
The existing heat bounds remain `M/sqrt(2t)` and `sqrt(2t)`. General-law passage,
full pi Buser and dimension-free KLS remain open.

## Validation

Strict compilation covers the three changed/new production modules and the independent
`research/audits/HeatChainRuleAudit.lean`, which checks integrability, the full D(A) identity,
the actual Gaussian specialization and the generic pairing convergence. Four transitive
axiom reports must contain only `propext`, `Classical.choice`, and `Quot.sound`.
The full build, audit suite, declaration checks, kernel replay and snapshot/index checks
are recorded in `build/audit/heat-chain-rule/final-snapshot.json` after verification.
No commit, push or remote CI is part of this round.
