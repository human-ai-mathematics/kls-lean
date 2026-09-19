# Proof Corrections and Improvements

Consolidated on 2026-09-15 from the repository's dated proof and audit records.
Lean source references were inspected at `e776840`; this document adds no mathematical
results and is not a new kernel-verification receipt.

This register records what changed while turning informal arguments into Lean proofs.
It distinguishes errors in our proof plans, improvements to valid arguments, unresolved
literature provenance, and corrections to our own status reports. It does not assert
that the cited published theorems are false. Historical records remain unchanged;
their progress counts and pending tasks describe their own dates.

## Summary

| Item | Classification | Outcome |
| --- | --- | --- |
| Hardy ground-state boundary terms | Error in an early local proof plan | Enlarge the integration interval and control the endpoint terms |
| One-dimensional Poincaré: 12 to 4 | Stronger bound through a different argument | Full CDF profile estimate plus weighted Hardy |
| Tail limits in the factor-4 argument | Proof simplification | Anchored Hardy estimates and a quadratic splitting inequality |
| Conditional-fiber comparison | Propagation of the stronger input | Factor 4 replaces 12; the frame estimate remains open |
| Distance cutoff | Simpler proof and explicit edge cases | Pointwise gradient control; no Rademacher or density theorem needed |
| Exact coefficient 4 in the literature | Provenance qualification | Local proof separated from historical attribution |
| Cheeger and coarea progress | Status correction and dependency clarification | A proved intermediate result does not close the remaining comparison |

## 1. Correcting the Hardy boundary terms

**Problem.** The first local plan applied the ground-state identity directly on the
clipping interval `[a,b]`. The boundary terms had the opposite signs to those needed
to discard them: `Ξ(a) ≥ 0 ≥ Ξ(b)`. That step could not establish the proposed bound.

**Repair.** Integrate on a larger interval `[c,e]` inside the support. The centered
primitive has explicit tail expressions `h(a) F` and `−h(b)(1−F)`, giving bounds
`Ξ(c) ≤ h(a)² F(c)` and `−Ξ(e) ≤ h(b)² (1−F(e))`. Send the two CDF tails to zero.
This supplies the missing boundary control rather than assuming its sign.

**Evidence.** The [factor-4 proof record](decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md)
explicitly identifies this mathematical correction. The implementation is in
[SharpHardy.lean](../formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpHardy.lean):
`boundaryTerm_le_of_le`, `neg_boundaryTerm_le_of_ge`, `groundState_inequality`, and
`integral_sq_div_le`. This is a correction to our early plan, not an identified error
in a published proof.

## 2. Strengthening the one-dimensional constant from 12 to 4

**Earlier valid route.** With median `m` and density `ρ`, the estimates
`C_P ≤ 1/ρ(m)²` and `Var ≥ 1/(12ρ(m)²)` give `C_P ≤ 12 Var`.
The dated analysis explains that the two steps have different extremal distributions;
their product does not yield coefficient 4. The coefficient-12 proof remains valid.

**Improvement.** Use the entire CDF profile `F(1−F) ≤ σρ`, where `σ² = Var`,
and a weighted Hardy argument to obtain `C_P ≤ 4 Var`. Affine majorants and their
variance estimates supply the profile bound. The Lean proof is organized in the
original spatial coordinate, without introducing a quantile-function API.

**Evidence.** Compare the [coefficient-12 record and its appendices](decisions/2026-09-10-one-dimensional-logconcave-poincare.md)
with the [coefficient-4 alignment table](decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md).
The implementation is in [Profile.lean](../formalization/FunctionalInequalities/KLS/LogConcave/Line/Profile.lean),
[SharpHardy.lean](../formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpHardy.lean), and
[SharpPoincare.lean](../formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean).
The [one-dimensional certificate](../solutions/ThmOneDimensionalLogConcavePoincare.lean)
covers the upper bound, including zero variance. It does not separately certify
optimality of 4 across all laws or a higher-dimensional KLS bound.

## 3. Simplifying the tail-limit argument

**Informal route.** The supplied reconstruction handles endpoint limits by splitting
bounded and unbounded support cases and uses Minkowski in the limiting argument.

**Lean route.** Anchored Hardy estimates control the tails uniformly, avoiding that
support split. A quadratic inequality with a positive parameter replaces the
square-root argument, followed by passage to the limit. These are proof-engineering
improvements to a valid argument, not corrections of its conclusion.

**Evidence.** The tail and limit rows of the
[factor-4 alignment table](decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md)
point to the generalized estimates in
[Hardy.lean](../formalization/FunctionalInequalities/KLS/LogConcave/Line/Hardy.lean)
and their assembly in `SharpPoincare.lean`.

## 4. Passing the improvement to conditional fibers

The stronger one-dimensional input gives a fiber-energy comparison with factor 4
and a conditional implication `C_P ≤ 4C` from the required frame/form bound.
Coefficient-12 consequences remain available as weakenings.

The [registration record](decisions/2026-09-12-conditional-fiber-twelve-bound-registration.md)
supersedes the earlier note that this strengthening was still pending.
[ConditionalFiber.lean](../formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean)
contains `conditionalFiber_fiberBound_four`, `conditionalFiber_energy_le_four_mul`,
and `conditionalFiber_literatureConstant_le_four_mul`.
The [certificate](../solutions/CorConditionalFiberTwelveBound.lean) retains a historical
filename containing “Twelve”; its statement uses 4. The universal frame bound is
still an independent research obligation.

## 5. Simplifying distance-cutoff gradient control

**Earlier dependency estimate.** The proposed route invoked Rademacher, density
arguments, or general almost-everywhere statements about gradients on level sets.

**Simplification.** Outside the transition annulus, the cutoff attains a global
maximum or minimum. Mathlib's local-extremum lemmas give zero `fderiv` there;
its derivative is defined as zero at nondifferentiable points. Inside the annulus,
the Lipschitz estimate gives the pointwise gradient bound. Integrating the annulus
indicator then gives the required difference of measures.

**Edge cases.** `infDist x ∅ = 0`, so the empty-set cutoff is **1**, not 0;
its gradient and the target right-hand side are both zero. The set need not be
measurable: its closure and open thickening provide the measurable annulus.
Endpoint level sets are handled by extrema, without treating them as open sets.
The original Haar and absolute-continuity parameters were retained even though
this proof does not use them. This derivative convention alone does not establish
an energy comparison for arbitrary singular laws.

**Evidence.** The [route correction](decisions/2026-09-13-cutoff-route-audit-correction.md)
is followed by the [completed proof record](decisions/2026-09-13-distance-cutoff-gradient-integral.md).
The implementation is [DistanceCutoff.lean](../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/DistanceCutoff.lean),
especially `lintegral_enorm_gradient_distanceCutoff_le`. The completion record reports
unchanged signatures and standard-axiom checks; its earlier pending status is historical.

## 6. Separating a literature gap from a false theorem

The [literature audit and reconstruction](explorations/2026-09-11-poincare-constant-4-audit.md)
distinguishes an explicit published statement of coefficient 4 from a located,
fully written original derivation. The earlier
[book-check appendices](decisions/2026-09-10-one-dimensional-logconcave-poincare.md)
record that the book states 4 by reference while its displayed one-dimensional
argument gives 12.

These records do **not** establish a false theorem or a published proof error.
Our local one-dimensional proof supplies independent mathematical evidence; it
does not settle who first wrote the complete exact-constant argument. The audit's
higher-dimensional natural-language reconstruction is also distinct from the
one-dimensional Lean certificate and from the dimension-free KLS conjecture.
No new literature search is claimed by this consolidation.

## 7. Correcting status claims and exposing coarea dependencies

The [Cheeger status correction](decisions/2026-09-13-cutoff-route-audit-correction.md)
records that a proof body for equality can still inherit `sorryAx` through an
unproved reverse inequality. At the inspected source revision,
[CheegerInfimum.lean](../formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean)
still leaves `smoothConstant_le_minkowskiConstant` unproved; its equality theorem
uses that direction. Completing the cutoff estimate does not complete this chain.

The [weighted-coarea route audit](decisions/2026-09-15-weighted-coarea-route.md)
identifies additional logical requirements: volume-null exceptional sets need
a slicing theorem; slice integrals need measurability; smooth approximation in
norm does not preserve level sets; and a C¹ graph-area formula cannot be applied
to arbitrary Lipschitz fibers without a bridge. These are dependency findings,
not a claim that every proposed shortcut had appeared in a published proof.

There has been progress since that route audit:
[RegularCoarea.lean](../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Regular.lean)
now proves weighted coarea on regular open C¹ domains (L9). Its module explicitly
separates this result from the full coarea targets in
[AnalyticPrerequisites.lean](../formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean).
The dated route audit should therefore be read as a dependency design, not as a
current list of every unfinished lemma. KLS itself remains open.

## Maintaining this register

For each new entry, record the original argument and its source, the precise
problem or improvement, the repaired argument, the Lean declarations, and the
verification evidence. Identify whether the claim concerns our plan, a supplied
informal proof, published literature, or a status report. Keep proposed routes,
source proofs, axiom checks, local receipts, and remote CI results distinct.
