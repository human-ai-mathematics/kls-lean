# KLS module organization

Date: 2026-09-19

## Decision

Regroup twelve KLS modules whose family word was repeated in the basename:

- `ConditionalFiber/Basic.lean` joins the existing `ConditionalFiber/{Closed,EnergyComparison,SliceKernel}.lean` family;
- `Geometry/Cheeger/{Equality,Inequality,Infimum}.lean` contains the three Cheeger comparison layers;
- `Geometry/Coarea/{Regular,Smooth,Lipschitz,LocallyLipschitz,Isoperimetry}.lean` contains the scalar weighted-coarea chain;
- `Geometry/Surface/{Measure,Homothety,Slicing}.lean` contains normalized surface measure and its geometric consequences.

The complete old-to-new map is
`research/api-migration/2026-09-19-kls-module-map.json`.

## Deliberate non-moves

`Definitions.lean`, `Statement.lean`, and `Target.lean` remain stable public entry layers: their
basenames are distinct roles, not a repeated family prefix. Two-module pairs such as
`GaussGreen.lean` / `LocalGaussGreen.lean` and `LogConcave/HeatSemigroup.lean` /
`LogConcave/HeatSemigroupMarkov.lean` remain flat under the three-module threshold.

## Compatibility boundary

This migration changes module paths only. Namespaces, declaration names, theorem statements,
proofs, assumptions, dimensional scope, and certificate status remain unchanged. No compatibility
alias modules are retained. Production imports, the root aggregate, live audit clients, canonical
task evidence, current documentation, and generated progress links use the new paths. Dated
decisions and explorations remain frozen and resolve through the migration map.

## Validation

All twelve migrated modules, every changed Lean consumer, the root aggregate, two solution
clients, and twenty-four live audit clients elaborate with `-DwarningAsError=true`. The progress
views were regenerated from the intended canonical working inputs through an isolated temporary
Git index, without changing the repository index.

Canonical evidence paths and hashes in `research/tasks.json` were refreshed. `atlas.py check`
reports no stale KLS or naming evidence; its full check remains stopped by the pre-existing missing
Mathlib evidence path
`Mathlib/MeasureTheory/MeasurableSpace/MeasurablyGenerated/Basic.lean` for
`lem:conditional-fiber-form`. No full `lake build`, `research/verify.py`, Git commit, or push was
performed.
