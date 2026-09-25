# Almost-everywhere heat estimates

## Placement and mathematical scope

The placement plan is in `HANDOFF.md`. This continues the tested inequalities of
[the previous round](2026-09-23-heat-reverse-poincare-self-improvement.md).

`Analysis/TestFunctionOrder.lean` proves order separation for integrable real functions on a
finite-dimensional real normed space with a finite Borel measure. Nonnegative integrals
against all nonnegative smooth compactly supported tests imply a.e. nonnegativity. The proof
first approximates compact indicators by smooth functions, then uses inner regularity on the
negative set of a measurable representative. Subtraction gives the comparison theorem.
No Haar measure, density, probability, positive dimension or semigroup is required.

`HeatSemigroup/ReversePoincare.lean` now proves, for smooth convex potentials in the existing
full-dimensional tilted-law model, unit weight, arbitrary L2 data `f` with `|f| <= M` a.e.,
and `t > 0`:

- `ae_two_mul_weakGamma_le_of_bounded`: `2t |T P_t f|^2 <= M^2` a.e.;
- `ae_norm_gradient_le_of_bounded`: `|T P_t f| <= M / sqrt(2t)` a.e.

Nonnegativity of `M` follows from the bound under the probability law; it is not an extra
premise. The square estimate comes from smooth-test order separation, not a pointwise
representative regularity assumption.

`HeatSemigroup/SelfImprovement.lean` proves for `f` in the whole form domain and `t >= 0`:

- `ae_norm_gradient_le`: `|T P_t f| <= P_t |T f|` a.e.;
- `integral_norm_gradient_le`: `integral |T P_t f| <= integral |T f|`.

The scalar norm of an L2 gradient is itself in L2. Semigroup symmetry moves the heat operator
from the test to this scalar L2 class; mass preservation gives the last inequality. Thus no
L1 semigroup extension is presumed. All original public declarations remain unchanged.

## Validation and remaining work

`research/audits/HeatAlmostEverywhereAudit.lean` independently checks the bounded-data bound,
form-domain self-improvement, total gradient contraction, time zero, and the generic order
lemma on a zero-dimensional atomic space and a zero measure. Its eight transitive axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Strict compilation, full build and snapshot verification are recorded under
`build/audit/heat-ae-estimates/`; `final-snapshot.json` identifies the final verification.
The original Git index and unrelated dirty baseline are preserved; no commit, push or remote
CI is performed.

Next: prove the small-time L1 approximation estimate, first on the form domain, then on the
appropriate BV/perimeter relaxation with exact constants. The nonsmooth/general-law passage,
perimeter interfaces, spectral-gap optimization and Buser with constant pi remain open.
The arbitrary-L2 reverse variance expression and square gradient contraction remain in tested
form; this round claims the two a.e. statements above, not an L1-valued heat operator on every
integrable function. No Buser or dimension-free KLS completion marker changes.
