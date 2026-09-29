# Exit raw T2 entry: last coarea hole closed

2026-09-16. This round moves the direct proof hole `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
from `KLS/WIP/AnalyticPrerequisites.lean` **out** to module hole-free
`KLS/Geometry/LipschitzCoarea.lean`, `pp.all` signature **byte-by-byte unchanged**, and proven at `S = Set.univ` by the previous round's L12
(`KLS.coarea_of_lipschitz`). The direct proof hole is reduced from **9(2/2/5) to 8(1/2/5)**. No new theorems are proven, no commit, no push, no rewriting of historical decisions.

Head and `origin/main` are both `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`; initial verification receipt is
`build/verification/20260916T072336.749178Z/report.json`: 10 gates, 198 local module kernel replays,
492 entries, snapshot `87051db917d503cf61aa3d227baa3e102ce22627679b47372ca65ab8e15e487e`.
The initial workspace contains changes from previous rounds that have not yet been commit, and this round continues on top of them, preserving all changes.

## Content Migration and Signature Verification

The new position is the end of `KLS/Geometry/LipschitzCoarea.lean`, immediately followed by the consumption of L12:

```lean
theorem FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (KLS.coarea_of_lipschitz (S := univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa only [setLIntegral_univ, univ_inter] using h
```

**Signature byte-by-byte unchanged, verified by two machine checks, not by eye comparison nor defeq assertion**

* Before migration, print the constant type with `set_option pp.all true` in the import WIP environment, and save it as
  `build/audit/t2-migration/signature-before.raw`; after migration, print again in the environment of importing a new module and save as
  `signature-after.raw`. Two files `cmp` passed, SHA256 is the same.
  `9e2121c254f66ed331b0f8fbb6b7ca7955f277f3f66705d7ed21a6ff490786a9`.
`#check @` will rename the full-quantifier level to `u_1`, so there is once again a program probe at the single level directly reading from the environment.
  `ConstantInfo`: `binders-before.raw` and `binders-after.raw` show the storage on both sides
  `levelParams` are `[u]`, the names of twelve binders are completely consistent with `BinderInfo`,
  Type hashes are also `2073454840`. The only difference is the module hygiene tag inside anonymous instance binders.
  (inst._@.<module name>...), it is inherently the module name itself, and is an inaccessible name, not part of the public interface;
  After normalizing the tag, the two reports are byte-for-byte identical (`binders-*.normalized`).

Thus retained: the same universe parameter `u`; the same **six** instance parameters in order, where `CompleteSpace V`
is exactly the instance to which `gradient` in the statement resolves (`@gradient.{0,u_1} … inst_2 u x`), so it is not an unused parameter;
The same implicit bindings `u`, `K`, `g` and the same hypothesis name `hu`, `hg`; the same `LipschitzWith` hypothesis;
The same `KLS.surfaceMeasure` normalization and unbounded `ℝ≥0∞` weight range.
**No** increase in C¹, positive dimension, finite volume, integrability, or SFinite assumptions, **no** new compatible alias,
**No** repeated proof of coarea. Document comments are preserved verbatim.

Declare retention of `FunctionalInequalities.Analysis` namespace (public name must remain unchanged), file placed at
`KLS/Geometry/` alongside the coarea layer it consumes; `KLS/Geometry/LevelSetMeasurable.lean` and
`KLS/Geometry/IsoperimetryCoarea.lean` follow the same arrangement. New position opens `namespace FunctionalInequalities.Analysis` after `L12`, in a separate section, no reuse of L12 section variable.

## Changes to WIP files

`KLS/WIP/AnalyticPrerequisites.lean` Only removed this statement and accordingly updated the file header description of the obligation;
After deletion, `section Coarea` contains only title comments and a single line of `variable` that is no longer used by any declaration, and both are removed together
(Pure scaffolding, containing no declarations, without changing any signature).
**`Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero` statements, proofs, and positions remain unchanged**
The original text prior to migration is saved as `build/audit/t2-migration/AnalyticPrerequisites.before.lean`,
The `LipschitzCoarea.lean` prior to migration is saved as `LipschitzCoarea.before.lean` in the same directory.

## Consumers and import

On the Lean side, only two audit clients reference this name, and no module in the library consumes it. Both added a line
`import FunctionalInequalities.KLS.Geometry.LipschitzCoarea`, **the client statement unchanged in a single character**:

* `research/audits/LevelSetMeasurableAudit.lean`
* `research/audits/IsoperimetryCoareaAudit.lean`

The local import closure of the new module includes 29 modules, none of which are WIP modules, and no reverse dependencies are introduced.

## Change in hole count and holes that remain open

* `KLS/WIP/AnalyticPrerequisites.lean`: **2 → 1** direct proof holes, the remainder is sharp `C^(finrank)`
  `Analysis.sard`.
* `KLS/WIP/CheegerInfimum.lean`: 2 (invariant), i.e., two Cheeger comparisons.
  `Energy/WIP/Cheeger.lean`: 5 (invariant).
* Total **9 → 8**. Certification remains **24**, perimeter infrastructure remains **missing**.

T1 (`Analysis.aemeasurable_lintegral_levelSet`), T2 (this round), T3 (`KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`) three original goals have now been officially connected to the hole-free module, and the three migrated `pp.all` signatures are all machine-verified byte-by-byte identical.

## Audit

New client `research/audits/LipschitzCoareaMigrationAudit.lean` **simultaneously imports** new modules and **two**
WIP files, so the following 16 reports come from the same environment, and the migration names therein are resolved to only one declaration.
Twelve are only dependent on `propext`, `Classical.choice`, `Quot.sound`:

* `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (original declaration migrated out);
* `KLS.coarea_of_lipschitz` (L12, proof source);
* `Analysis.aemeasurable_lintegral_levelSet` and `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (neighbors from the first two rounds migrated out);
* Eight clients: verbatim reproduction and **named arguments** instantiation of `client_migrated_t2` (renamed binder or assumption swapping, which is not achieved via elaboration here), proposition text writing following the original route and only instantiated at the migration entry point of `original_T2`, `client_L12`, synthesis of the two halves into original two-segment conclusions of `client_both_halves`, a norm function indeed non-differentiable at 0, `norm_not_contDiff`, constant ∞ weight `infinite_weight`, zero-dimensional `zero_dimension`, and the previous C¹ specialization of `client_contDiff_specialization`.

Four still contain `sorryAx`, all of which are open holes not yet touched in this round: `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero`, `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`, `Isoperimetry.smoothConstant_le_minkowskiConstant`.

Two reports from consumers show expected changes, neither regression nor complete reset:

* `LevelSetMeasurableAudit`: Two coarea reports
  (`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and `client_coarea_statement`)
  are free of `sorryAx`; `Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero` still retain `sorryAx`.
* `IsoperimetryCoareaAudit`: Two Lipschitz coarea reports
  (same name and `client_lipschitz_coarea_statement`) are free of `sorryAx`;
  `Analysis.sard`, two Cheeger comparisons, and `minkowskiConstant_eq_smoothConstant` still retain `sorryAx`.

## What was not done in this round

* **No proof of any new theorems**; this round involved only one migration and interface connection.
* No extension to Cheeger or sharp Sard, no proof of sharp `Analysis.sard`, two Cheeger comparisons, equality of two Cheeger constants, five holes in Energy, or dimension-free KLS.
* No expansion of certification or Blueprint `leanok` scope; no mislabeling of coarea completion as KLS completion.
* **No commit, no push**, the real Git index remained unchanged.

## Verification

* `KLS/Geometry/LipschitzCoarea.lean` compiles successfully with `-DwarningAsError=true` alone, without `sorry`.
* The new client compiles successfully with `-DwarningAsError=true`, and 16 `#print axioms` provides the boundary from the previous section.
* Signature `cmp` passed, binder/universe probe normalized byte-by-byte identical.
* Redo all 24 audit client instances (`research/audits` 17 of them, already have `build/audit` 7 of them),
  All strictly compiled successfully.
* Three WIP files were successfully compiled in practice, with direct proof holes respectively **1/2/5**, total **8**.
* Default `lake build` is connected to the root directory `python3 research/verify.py`. Final verification receipt is
  `build/verification/latest.json`, exactly consistent with the final full code snapshot; evidence JSON is
  `research/explorations/2026-09-16-t2-coarea-migration.json`, final verification and save
  `build/audit/t2-migration/final-snapshot.json`, avoid creating cyclic hashes for the verification receipt itself.
