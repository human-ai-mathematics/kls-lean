# Migrating level-set measurability: the first coarea hole is closed

2026-09-15. This round **moves** the direct hole `Analysis.aemeasurable_lintegral_levelSet` from
`KLS/WIP/AnalyticPrerequisites.lean` to the hole-free module `KLS/Geometry/LevelSetMeasurable.lean`,
with a **byte-identical** `pp.all` signature, and supplies the proof using L5 from the preceding round.
Direct holes decrease from **11 (3/3/5) to 10 (2/3/5)**. No commit, push, or changes to historical decisions.
Starting HEAD: `2965b32bc79bdb24921c633df12102450eaedcc4`; starting passed receipt:
`build/verification/20260915T033803.710026Z/report.json` (byte-identical to `build/verification/latest.json`).
The recomputed full snapshot matches the receipt: 421 files, SHA256
`8abb1b22ab2ebac05aac28d7ac32536dba0dc2d40da4a1e1109f285d50ed60f8`.
This comparison checks per-file SHA256, including deletions, and the complete snapshot structure, not just HEAD.

## Migrated content and signature comparison

New module `formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean`:

```lean
theorem FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) := by
  have h := KLS.aemeasurable_setLIntegral_inter_levelSet (S := Set.univ) hu.continuous
    hu.lipschitzOnWith MeasurableSet.univ hg
  simpa using h
```

**Byte-identical signatures**, verified mechanically rather than visually: before migration, print
`@FunctionalInequalities.Analysis.aemeasurable_lintegral_levelSet` with `set_option pp.all true` in an environment
importing WIP, saving it to `build/audit/migration-signature-before.log`. After migration, print it in an environment
importing the new module, saving it to `build/audit/migration-signature-after.log`. Their `diff` is empty.
The signature includes the same universe, six instance parameters in the same order (including the **unused**
`CompleteSpace V`), implicit binders `u`, `K`, `g`, hypothesis names `hu`, `hg`, and conclusion.

Unused section variables are retained to preserve the interface. Following the repository's existing practice
when moving `ae_exists_superlevel` into `Geometry/RegularSuperlevel.lean`, use
`set_option linter.unusedSectionVars false in` to silence the linter, **without** narrowing the signature with `omit`.
The docstring is also unchanged.

The declaration retains namespace `FunctionalInequalities.Analysis` (the public name must not change),
while the file lives under `KLS/Geometry/` because its statement uses `KLS.surfaceMeasure` and does not belong
in the KLS-independent `Analysis/` layer. The replaced WIP file used the same arrangement.

`KLS/WIP/AnalyticPrerequisites.lean` only loses this declaration and updates its module header.
**No other declaration changes**: the statements, proofs, and positions of
`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, `sard`, and `ae_forall_fderiv_ne_zero` are unchanged.

## Hole counts and remaining holes

* `AnalyticPrerequisites.lean`: **3 → 2** direct holes.
* `KLS/WIP/CheegerInfimum.lean`: 3 (unchanged). `Energy/WIP/Cheeger.lean`: 5 (unchanged).
* Total: **11 → 10**. This is the only count change this round; certificates remain **24**,
  and perimeter infrastructure remains **missing**.

`build/audit/LevelSetMeasurableAudit.lean` imports **both** the new module and WIP file, so the reports below
come from one environment, where the migrated name resolves to exactly one declaration:

* `Analysis.aemeasurable_lintegral_levelSet`: `propext, Classical.choice, Quot.sound`, **no `sorryAx`**.
* `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (weighted coarea **equality**):
  still contains `sorryAx` and remains a direct hole.
* `Analysis.sard` (sharp `C^(finrank)`): still contains `sorryAx`, remains a direct hole, and has no downstream consumers.
* `Analysis.ae_forall_fderiv_ne_zero`: still inherits `sorryAx` from `sard`.

The client also restates the two statements as theorems and calls the library declarations with named arguments:
`client_aemeasurable_lintegral_levelSet` compiles without `sorryAx`; `client_coarea_statement` compiles
**with `sorryAx`**. It merely restates the unproved equality and does not prove it.

## Work excluded from this round

* **No proof of weighted coarea equality**. `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  and `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` remain direct holes.
  Targets T2/T3 and L6–L12, including the Whitney C¹ extension in L6, are untouched.
* No proof of sharp `C^(finrank)` `Analysis.sard`.
* No proof of `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, or equality of the two Cheeger constants.
* No proof of sharpness of the Eilenberg constant.
* No new mathematical content: this round contains no new theorem, only one migration and interface connection.
* No expansion of certificate or Blueprint `leanok` scope.

## Validation

* `KLS/Geometry/LevelSetMeasurable.lean` compiles separately with `-DwarningAsError=true`.
* `build/audit/LevelSetMeasurableAudit.lean` compiles with `-DwarningAsError=true`;
  its 6 `#print axioms` reports establish the boundaries above.
* Signature `diff` is empty (`migration-signature-before.log` and `migration-signature-after.log`).
* Reran `BorelSliceAudit`, `CompactSliceAudit`, `EilenbergMajorantAudit`, `NullSlicingAudit`,
  `WeightedCoareaRouteStatements`, `WeightedCoareaInfrastructure`, `AreaFormulaAudit`,
  `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`,
  and `SmoothSardRouteStatements`; all passed strict compilation unchanged.
* The three WIP files compile separately, with **2/3/5 direct holes, total 10**.
* Default `lake build` and root-level `python3 research/verify.py` pass. Final receipt:
  `build/verification/latest.json`, matching the complete final source snapshot exactly. Evidence JSON:
  `research/explorations/2026-09-15-levelset-measurable-migration.json`; final snapshot check:
  `build/audit/migration-final-snapshot.json`. Since `build/` is gitignored, the evidence JSON separately binds
  the hashes under `build/audit`. The original WIP file is saved unchanged as
  `build/audit/migration-AnalyticPrerequisites.before.lean`.
