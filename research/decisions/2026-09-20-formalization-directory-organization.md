# 2026-09-20 formalization directory organization

71 modules under `formalization/FunctionalInequalities/` move into family directories.
This round **changes only module paths**: no namespace or declaration is renamed, and no theorem statement,
proof, assumption, dimensional scope, or certificate status changes.

## 1. New global directory rules

The rules are recorded in the “Family names belong in directories, not filenames” section of
[`research/naming.md`](../naming.md). From this date they apply across the library, not only to `Analysis/`:

1. **Three or more** modules concerning the same mathematical object must enter a family directory, dropping the family word from basenames.
2. Two modules may form a family directory when they have a clear “foundation + extension/properties” relationship.
3. `X.lean` and `X/` must not coexist internally; move the foundational module to `X/Basic.lean` in that case.
4. The root retains only cross-family infrastructure, stable public entry points, or modules that genuinely cannot belong to one object.
5. Classify directories by **main mathematical object**, not a one-off proof route.
6. File migration must not change namespaces, declaration names, theorem statements, proofs, assumptions, dimensional scope, or certificate status.
7. Do not provide compatibility modules or aliases for old paths.

### Why clear two-module families are allowed (rule 2)

The three-module threshold in rule 1 prevents grouping modules merely because they happen to be adjacent.
“Basic definitions + their properties” is an established structural relationship: the extension exists to develop
objects in the foundational module, and a third module will eventually belong in the same place.
This round has two examples:

- `KLS/LogConcave/HeatSemigroup/{Basic,Markov}.lean`: `Basic` specializes the abstract semigroup construction
  to the weighted gradient operator; `Markov` proves the Markov properties of that concrete semigroup.
- `Energy/Cheeger/{Basic,Identification}.lean`: `Basic` defines metric Cheeger energy;
  `Identification` proves its identification with smooth-gradient relaxation.

Conversely, this round does **not** create directories for pairs that merely share a prefix without a foundation/extension relationship.
`Poincare/L2/{Energy,Comparison}.lean` share a directory because both concern the single mathematical object `L2Energy`
(the energy definition and comparison of its optimal constant), not merely because their basenames shared `L2`.

### Why `FunctionalInequalities.lean` and `FunctionalInequalities/` may coexist (rule 3)

Rule 3 concerns **internal library modules** named `X.lean` alongside `X/`.
That arrangement makes `X` both a module and a name prefix, obscuring whether its content consists of basic definitions
or a directory index. This round's sole instance, `Energy/Cheeger.lean` plus `Energy/Cheeger/`,
becomes `Energy/Cheeger/Basic.lean`.

`formalization/FunctionalInequalities.lean` is the **library root** of a Lake `lean_lib`
(`[[lean_lib]] name = "FunctionalInequalities"` in `lakefile.toml`). The standard Lean 4 and Mathlib layout
requires the aggregate root and same-named directory to coexist (`Mathlib.lean` plus `Mathlib/`).
It is the whole library's public entry point, resolved by name by `lake build`, rather than the foundational module
of one mathematical object inside `FunctionalInequalities/`.
Changing it to `FunctionalInequalities/Basic.lean` would change the library root, beyond directory organization.

### Why retain `Poincare/Euclidean/`, `Poincare/FiniteProduct/`, and `Poincare/LipschitzGradient/`

These three existing exceptions to rule 5 remain unchanged:

- `Poincare/Euclidean/` is organized by **domain** (concrete counterexamples and obstructions in Euclidean space),
  with namespace `Poincare.Euclidean`, paired with `Energy/Euclidean/`.
- `Poincare/FiniteProduct/` is organized by **model** (tensorization and geometry of finite product laws),
  with namespace `Poincare.FiniteProduct`, separate from the countable case in `Poincare/Product/`.
- `Poincare/LipschitzGradient/` is organized by **test class**, with namespace
  `Poincare.LipschitzGradient`, alongside `SmoothGradient` and `CovarianceGradient`.

All three directory names match their namespaces, and each has only one or two modules.
They distinguish the mathematical object's **ambient space or test class**, not a one-off proof route,
so rule 5 requires no change.

## 2. Migration scope

Three batches, 71 files in total. Complete mappings:

- [`research/api-migration/2026-09-20-analysis-module-map.json`](../api-migration/2026-09-20-analysis-module-map.json) (30)
- [`research/api-migration/2026-09-20-foundation-module-map.json`](../api-migration/2026-09-20-foundation-module-map.json) (20)
- [`research/api-migration/2026-09-20-kls-module-map.json`](../api-migration/2026-09-20-kls-module-map.json) (21)

Each supplies both a dotted module map and a filesystem path map.

| Batch | Family directories |
| --- | --- |
| Analysis | `Analysis/Coarea/`, `Analysis/Hausdorff/`, `Analysis/Vector/Coarea/`, `Analysis/Vector/Slice/`; all of `Analysis/RankDeficient/` moves into `Analysis/Vector/RankDeficient/`; `AreaFormula`/`SubgraphDivergence` join the existing `Analysis/Graph/`, `QuadraticCover`/`TaylorRemainder` join `Analysis/Sard/`, `FirstOrderJet` joins `Analysis/Whitney/`, and `LipschitzC1Pieces`/`LipschitzJet` join `Analysis/Lipschitz/` |
| Energy / Probability / Poincare | `Energy/Form/`, `Energy/Euclidean/Slope/`, `Probability/Covariance/`, `Probability/Domination/`, `Poincare/L2/`; `Energy/Cheeger.lean` becomes `Energy/Cheeger/Basic.lean`, and `HaarLine` joins the existing `Probability/Line/` |
| KLS | `KLS/Geometry/Perimeter/`, `KLS/Geometry/Slice/`, `KLS/Geometry/SmoothDomain/`, `KLS/LogConcave/Density/`, `KLS/LogConcave/HeatSemigroup/`; four supporting modules join the existing `KLS/Geometry/Cheeger/` |

No empty directories remain under `formalization/FunctionalInequalities/` after migration.
The three historical empty directories under `Energy/Euclidean/` (`SmoothGradient/`, `IntrinsicAffine/`,
`CovarianceGradient/`) disappear together with the emptied `Analysis/RankDeficient/`.

## 3. Invariants

- **Only module paths change.** Namespaces, short declaration names, theorem statements, proofs,
  parameter explicitness and order, assumptions, dimensional scope, and certificate status remain unchanged.
  Directories provide grouping only.
- In particular, the following namespaces are independent of their new directory names and are **not** rewritten:
  `FunctionalInequalities.Energy.Cheeger` (module now `Energy/Cheeger/Basic.lean`),
  `FunctionalInequalities.Energy.Functional` (`Energy/Form/Functional.lean`),
  `FunctionalInequalities.Poincare.L2Energy` (`Poincare/L2/Energy.lean`),
  `FunctionalInequalities.Probability.Covariance` (`Probability/Covariance/Basic.lean`),
  `FunctionalInequalities.Analysis.LipschitzJet` (`Analysis/Lipschitz/Jet.lean`),
  `FunctionalInequalities.KLS.ConditionalFiber`.
  Modules under `Analysis/` retain namespace `FunctionalInequalities.Analysis` regardless of subdirectory.
- **No compatibility modules remain.** Old paths cease to exist; there are no forwarding-import shims or aliases.
  Old references resolve through this round's three mapping tables only.
- **Historical records remain frozen.** `research/decisions/**` and `research/explorations/**` retain their original path spellings,
  without retroactive rewriting. Existing maps under `research/api-migration/`, including
  `2026-09-19-kls-module-map.json`, are unchanged; this round adds three separate files.
- The statement-snapshot golden has one change: the `module` field of `FunctionalInequalities.Covariance.operator`
  changes from `FunctionalInequalities.Probability.Covariance` to
  `FunctionalInequalities.Probability.Covariance.Basic`. Dependencies, type, and value remain verbatim unchanged.
- `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the library's sole intentionally retained target hole.
  This round leaves it untouched, adds it to no `\lean` tag or certificate closure,
  and introduces no direct `sorry`/`admit` or transitive `sorryAx`.

## 4. Synchronization scope

Production imports, aggregate root `FunctionalInequalities.lean`, `solutions/`, `research/audits/`,
README / HANDOFF / LEAN_DESIGN / `research/verification.md`, `\path{}` references in current Blueprint chapters,
`research/progress/nodes.json` and its generated README / STATUS / TREE / LITERATURE,
evidence paths and sha256 in `research/tasks.json`, and `research/proof-corrections-and-improvements.md`
are all synchronized. Blueprint `\lean{}` declaration tags contain no module paths and remain unchanged.
