# 2026-10-07 family directories: Bakry–Émery tilts, Bochner, integration by parts; Gaussian smoothing

Fourteen modules move into four family directories. This batch **changes only module paths**:
no namespace or declaration is renamed, and no theorem statement, proof, assumption,
dimensional scope or certificate status changes. The complete map is
[`2026-10-07-family-directories-map.json`](../api-migration/2026-10-07-family-directories-map.json).

## Findings

A filename scan after the two BKL blocks of 2026-10-07 found two violations of rule 1 of
[naming.md](../naming.md#family-names-belong-in-directories-not-filenames) (three or more
modules about one object must form a family directory, without repeating the family term):

- `Analysis/BakryEmery/` held four tilt modules (`Tilt`, `SquareIntegrableTilt`,
  `TemperateTilt`, `TensorTilt`) and four Bochner modules (`Bochner`, `IntegratedBochner`,
  `TemperateBochner`, `TensorBochner`), most added by the BKL foundations block.
- `KLS/LogConcave/Density/` held four modules sharing the namespace
  `KLS.LogConcave.GaussianSmoothing` (`GaussianSmoothing`, `GaussianApproximation`,
  `GaussianPoincare`, `GaussianBuser`).

`TemperateIBP` also abbreviated the mathematical term `IntegrationByParts`, contrary to
[workflow.md §4](../workflow.md#4-name-the-three-layers-separately).

## Placement plan

```text
Object and role:        exponential tilts and tilt averages (BKL (26)-(28), (48), Lemma 3.6,
                        Corollary 3.7); the Bochner identity in its pointwise, integrated,
                        temperate and tensor forms; weighted integration by parts on C_c^inf
                        and on temperate tests; normalized Gaussian smoothing of Borell
                        densities and its approximation, Poincare and Buser consequences.
Exact scope / non-claims: path move only; no statement, assumption or status change.
Existing owner:         Analysis/BakryEmery and KLS/LogConcave/Density (unchanged owners).
Destination:            Analysis/BakryEmery/{Tilt,Bochner,IntegrationByParts}/ and
                        KLS/LogConcave/Density/GaussianSmoothing/; foundational module Basic.
Imports:                unchanged edges, renamed endpoints; no new dependency.
Extend/split/create:    create family directories (rule 1; rule 2 for the
                        IntegrationByParts basic/temperate pair, matching the Tilt/Bochner
                        temperate extensions and restoring the unabbreviated term).
Public API changes:     module paths only (14); namespaces and declarations unchanged.
Validation:             full lake build, research/verify.py, progress regeneration.
```

| Old module | New module |
| --- | --- |
| `Analysis/BakryEmery/Tilt` | `Analysis/BakryEmery/Tilt/Basic` |
| `Analysis/BakryEmery/SquareIntegrableTilt` | `Analysis/BakryEmery/Tilt/SquareIntegrable` |
| `Analysis/BakryEmery/TemperateTilt` | `Analysis/BakryEmery/Tilt/Temperate` |
| `Analysis/BakryEmery/TensorTilt` | `Analysis/BakryEmery/Tilt/Tensor` |
| `Analysis/BakryEmery/Bochner` | `Analysis/BakryEmery/Bochner/Basic` |
| `Analysis/BakryEmery/IntegratedBochner` | `Analysis/BakryEmery/Bochner/Integrated` |
| `Analysis/BakryEmery/TemperateBochner` | `Analysis/BakryEmery/Bochner/Temperate` |
| `Analysis/BakryEmery/TensorBochner` | `Analysis/BakryEmery/Bochner/Tensor` |
| `Analysis/BakryEmery/IntegrationByParts` | `Analysis/BakryEmery/IntegrationByParts/Basic` |
| `Analysis/BakryEmery/TemperateIBP` | `Analysis/BakryEmery/IntegrationByParts/Temperate` |
| `KLS/LogConcave/Density/GaussianSmoothing` | `KLS/LogConcave/Density/GaussianSmoothing/Basic` |
| `KLS/LogConcave/Density/GaussianApproximation` | `KLS/LogConcave/Density/GaussianSmoothing/Approximation` |
| `KLS/LogConcave/Density/GaussianPoincare` | `KLS/LogConcave/Density/GaussianSmoothing/Poincare` |
| `KLS/LogConcave/Density/GaussianBuser` | `KLS/LogConcave/Density/GaussianSmoothing/Buser` |

`TensorEnergy`, `Cumulant`, `Gamma` and `WeakGamma` stay in `Analysis/BakryEmery/`: each is a
separate object, and `Gamma`/`WeakGamma` (classical versus `L¹` carré du champ) are distinct
carriers rather than a basic/extension pair.

## Reviewed and left in place

The same scan flagged shared basename tokens that are not one-object families:

- `KLS/Geometry/Cheeger/{MinkowskiConstant,MinkowskiContent,UpperMinkowskiContent}`: the
  Cheeger infimum and two different contents (outer and upper); different objects.
- `KLS/Geometry/Perimeter/{MetricBVMinkowski,RelaxedMinkowski,UpperMinkowskiRecovery}`: a
  comparison bridge, a relaxed content and a recovery construction around the metric BV
  perimeter; different roles in the `MetricBV` namespace.
- `KLS/LogConcave/Line/{Density,DensityBound,OfDensity}`: the line density structure, a
  balanced-mass bound and the converse from densities; already inside the `Line/` family.
- Optional two-module pairs (`HeatSemigroup/{TestClass,TestClassExtension}` and similar)
  are left as they are; rule 2 permits but does not require a directory.

## Updated consumers

Imports in the library aggregate, library modules and `research/audits/`; evidence paths in
`research/tasks.json` (hashes refreshed); source links in `research/progress/literature.json`
and `nodes.json` and the regenerated progress views; `research/verification.md`, `HANDOFF.md`,
`research/workflow.md` and `research/naming.md`. Historical decisions, handoffs, migration maps
and dated technical-debt inventories keep their original paths.
