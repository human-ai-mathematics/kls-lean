# Scalar coarea

General weighted coarea for real functions on finite-dimensional inner-product spaces.
These modules import no KLS application or Poincaré module. Existing `KLS` and `Analysis`
public namespaces are retained independently of the file ownership.

| Module | Responsibility |
| --- | --- |
| [FiberIntegral.lean](FiberIntegral.lean) | Tonelli and one-dimensional change of variables along fibers |
| [RegularChart.lean](RegularChart.lean) | Coordinate charts at regular points |
| [Regular.lean](Regular.lean) | Weighted coarea on an open regular domain |
| [Smooth.lean](Smooth.lean) | Arbitrary C¹ functions, including null critical slices |
| [Isoperimetry.lean](Isoperimetry.lean) | Full-space C¹ Lipschitz specialization |
| [Lipschitz.lean](Lipschitz.lean) | Globally Lipschitz functions via exact C¹ pieces |
| [LocallyLipschitz.lean](LocallyLipschitz.lean) | Locally Lipschitz functions |

[Hausdorff slice modules](../Hausdorff/Slice/) own critical-slice and measurability inputs.
Regularity, completeness, measurability and dimension premises remain theorem-specific.
Critical-slice nullity is distinct from Sard's critical-value theorem. Vector-valued coarea
remains in [Vector](../Vector/) and [Lipschitz](../Lipschitz/).
