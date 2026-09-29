# Semigroup module organization

Date: 2026-09-19

## Decision

Regroup the thirteen repeated-family modules under
`FunctionalInequalities/Analysis/Semigroup/` into four directories:

- `Resolvent/{Form,Basic,Limit}.lean` for the weak form, resolvent construction, and its limit;
- `Exponential/{Contraction,MeanValue,Limit}.lean` for generic bounded-operator exponential facts;
- `Yosida/{Approximation,Family,Limit}.lean` for the actual Yosida approximation and its limit;
- `Generated/{Basic,Laws,Generator,Markov}.lean` for the generated semigroup and its properties.

`AdjointComp.lean` and `VonNeumann.lean` remain flat because their family has only two modules.
The complete old-to-new map is
`research/api-migration/2026-09-19-semigroup-module-map.json`.

## Rationale

This applies the repository rule “Family names belong in directories, not filenames”. In particular, the former
`Yosida.lean` was not about the Yosida approximation itself: it proves a generic contraction
bound for exponentials of bounded nonnegative operators, so its mathematical home is
`Exponential/Contraction.lean`.

The migration changes module paths only. Namespaces, declarations, theorem statements, and
mathematical scope remain unchanged. No compatibility alias modules are retained.

## Consumers and historical records

Production imports, the root aggregate, live audit clients, and canonical task paths use the new
module paths. Dated decisions and explorations are frozen at their historical paths and are
resolved through the migration map rather than rewritten.

## Validation

All fifteen semigroup source modules, both concrete heat-semigroup modules, the root aggregate,
and the seventeen live semigroup/heat-semigroup audit clients elaborate with
`-DwarningAsError=true`. This was a targeted migration validation; no full `lake build`,
`research/verify.py`, Git commit, or push was performed.

Canonical evidence paths and hashes in `research/tasks.json` were refreshed. `atlas.py check`
reports no stale semigroup or naming evidence; its full check remains stopped by the pre-existing
missing Mathlib evidence path
`Mathlib/MeasureTheory/MeasurableSpace/MeasurablyGenerated/Basic.lean` for
`lem:conditional-fiber-form`.
