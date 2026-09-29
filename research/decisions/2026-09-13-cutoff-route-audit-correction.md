# Distance-cutoff route and status correction

Date: 2026-09-13. This corrects the
[one-sided Cheeger comparison record](2026-09-13-cheeger-infimum-one-sided.md). That historical record is retained;
the following text and the current HANDOFF and status documents supersede its corresponding status and next-route descriptions.

## Verified status

`minkowskiConstant_le_smoothConstant` is proved, with the three standard axioms and no transitive `sorryAx`.
`smoothConstant_le_minkowskiConstant` remains a direct hole;
`minkowskiConstant_eq_smoothConstant` has a `le_antisymm` proof body but inherits `sorryAx` through the reverse direction.
`SmoothDomain.ae_exists_superlevel` remains a direct hole; its body has not been filled.
It is `Analysis.ae_forall_fderiv_ne_zero` whose body has been filled and which inherits `sorryAx` through Sard.
The total number of direct holes remains 13 (3/5/5), and the formal certificate count remains 24.

## Simplified distance-cutoff route

The independent client `build/audit/CutoffRouteReview.lean` was verified with `-DwarningAsError=true`:
`IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` require no differentiability hypothesis;
`norm_fderiv_le_of_lipschitz` also gives a pointwise bound.
This is because Mathlib defines `fderiv` and `gradient` to be zero at points of nondifferentiability.

For nonempty B, the cutoff attains its global maximum 1 on closure B and its global minimum 0 outside the thickening.
Thus the gradient is directly zero at those points, including both endpoint level sets; the existing Lipschitz bound applies within the annulus.
One can then use `lintegral_mono` to integrate the annulus indicator, followed by `measure_sdiff` and
`Metric.closure_subset_thickening` to obtain the required measure difference.
This route needs neither Rademacher, the Lebesgue density theorem, nor `hac`, and does not require a general theorem about gradients on level sets.
Handle the empty set separately: `Metric.infDist_empty` makes the cutoff constantly **1**, and both its gradient and the target right-hand side are zero.

This round verified only the core APIs needed by the route; `lintegral_enorm_gradient_distanceCutoff_le` remains unproved.
The next round should retain the m, Haar, and hac parameters of the original target statement, without unilaterally changing the public interface.
The convention at points of nondifferentiability does not constitute a general comparison result for singular laws.

This round corrects documentation only, with no changes to production Lean source, commit, or push. The complete verification is recorded in the revised
`build/verification/latest.json`.
