# Proof path to KLS through BKL

The [paper register](LITERATURE.md) owns source versions and exact coverage.
The [verification guide](../verification.md) separates local checking, kernel replay
and certificate registration. This page adds no certificate.

| Stage | Pinned source | Closed Lean producer |
| --- | --- | --- |
| Compact quadratic variance, exact 8 | Letwin arXiv:2607.24164v1 Theorem 1.2 via Theorem 2.5; BKL Lemma 4.2 input | `KLS.LogConcave.letwinCompactBound` in [CompactBound](../../formalization/FunctionalInequalities/KLS/Letwin/CompactBound.lean) |
| Finite-horizon cutoff localization | BKL arXiv:2610.05474v1 Sections 4-6 and cutoff (95) | [Localization/CutoffEnergy](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy), certificate [LemBklCutoffEnergy](../../solutions/LemBklCutoffEnergy.lean) |
| Universal cumulant bound | BKL Theorem 4.1 | [CumulantInduction](../../formalization/FunctionalInequalities/KLS/BKL/CumulantInduction.lean), certificate [ThmBklCumulantBound](../../solutions/ThmBklCumulantBound.lean) |
| Taylor criterion and suspension | BKL Theorem 3.1 and Proposition 7.1 | [PoissonIterate/Criterion](../../formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean) and [Suspension](../../formalization/FunctionalInequalities/KLS/BKL/Suspension), with their maintained solution clients |
| Source Poincare statement and affine/isotropic reduction | BKL Theorem 1.1 | `KLS.BKL.Localization.conjecture` in [Poincare](../../formalization/FunctionalInequalities/KLS/BKL/Poincare.lean), certificate [ThmBklPoincare](../../solutions/ThmBklPoincare.lean) |
| Covariance-normalized KLS | `KLS.Conjecture` | `KLS.kls` in [Target](../../formalization/FunctionalInequalities/KLS/Target.lean) |

The final conclusion chooses one finite constant before every dimension and
log-concave law with finite second moment. Zero dimension and singular affine
supports are included. The compact constant-8 input is proved, rather than a
remaining premise of the final endpoint.

The separate noncompact Letwin Theorem 1.2 and Lemma A.1 approximation are retained
in [QuadraticBound](../../formalization/FunctionalInequalities/KLS/Letwin/QuadraticBound.lean)
and [Approximation](../../formalization/FunctionalInequalities/KLS/Letwin/Approximation.lean).
The complete merely convex Lemma 2.2 source producer and the uncut Eldan process
remain outside this completed chain. Deferred local UNIT/CNS developments are not
part of this delivery and are not asserted as completed mathematics here.
