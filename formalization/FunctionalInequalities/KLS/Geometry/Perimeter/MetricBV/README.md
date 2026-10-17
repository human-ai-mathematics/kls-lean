# Metric BV perimeter

The test class uses globally Lipschitz bounded functions with **bounded function support**.
On a general metric space this does not assert compact support. No properness assumption is
added. Approximation uses global L¹ convergence for the actual Borel measure.

| Owner | Responsibility and assumptions |
| --- | --- |
| [Basic.lean](Basic.lean) | Tests, sequential relaxation, recovery, lower semicontinuity, support-mass cost bounds and the general infinite-mass obstruction |
| [Finite.lean](Finite.lean) | Finite-carrier and singleton results for arbitrary measures |
| [Complement.lean](Complement.lean) | Complement symmetry on general metric spaces with finite measure |
| [Approximation.lean](Approximation.lean) | Bounded-support reductions of globally Lipschitz approximants; finite-measure and finite-target-mass variants |
| [Transport.lean](Transport.lean) | Subset restriction and closed-support laws, retaining their topology/measurability assumptions |
| [Scaling.lean](Scaling.lean) | Measure scaling, zero/nonzero coefficient cases and probability normalization |
| [Counterexample.lean](Counterexample.lean) | Lebesgue measure on the real line: empty/full complement symmetry fails at infinite mass |

Finite carriers and finite measures are distinct. Infinite perimeter may reflect an empty
approximation class; recovery is asserted only under the original finite-perimeter condition.
Qualified `KLS.MetricBV` names are unchanged. The family stays with its actual KLS perimeter
consumers. See the [layout decision](../../../../../../research/decisions/2026-10-18-stein-metricbv-layout.md)
and [verification scope](../../../../../../research/verification.md).
