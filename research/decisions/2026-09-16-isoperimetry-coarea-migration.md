# Migrating C¹ weighted coarea: the second coarea hole is closed

2026-09-16. This round **moves** the direct hole `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
from `KLS/WIP/CheegerInfimum.lean` to the hole-free module `KLS/Geometry/IsoperimetryCoarea.lean`,
with a **byte-identical** `pp.all` signature, and supplies its proof using L11 from the preceding round.
Direct holes decrease from **10 (2/3/5) to 9 (2/2/5)**. **No new theorem is proved**;
no commit, push, or rewriting of historical decisions.

Starting HEAD: `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`; starting passed receipt:
`build/verification/20260915T161514.695618Z/report.json`, matching the starting worktree exactly:
467 files, SHA256 `5994b4b4758eeb95e354bd1b081cc22919a4dea1e02ab7188bf1c035790be0bb`.
The starting worktree contains uncommitted changes from the preceding two rounds; this round builds on them.

## Migrated content and signature comparison

New module `formalization/FunctionalInequalities/KLS/Geometry/IsoperimetryCoarea.lean`:

```lean
theorem FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (coarea_of_contDiff (S := Set.univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa using h
```

**Byte-identical signatures, checked mechanically**: before migration, print the constant's type with
`set_option pp.all true` in an environment importing WIP and save it to `build/audit/iso-signature-before.log`.
After migration, print it in an environment importing the new module and save it to `build/audit/iso-signature-after.log`.
Their `diff` is empty. The signature has the same universe, the same **seven** instance parameters in the same order
(including the **unused** `CompleteSpace V` and `SecondCountableTopology V`), the same implicit binders `u`, `K`, `g`,
the same hypothesis names `hu`, `hK`, `hg`, and the same conclusion.

To preserve the interface, the unused section variables and hypothesis name `hK` remain unchanged.
Use `set_option linter.unusedSectionVars false in` and `set_option linter.unusedVariables false in`
to silence the two linters, **without** narrowing the signature with `omit` or renaming `hK` to `_`.
The docstring is unchanged. The declaration retains namespace `FunctionalInequalities.KLS.Isoperimetry`
(the public name must stay unchanged), and the file sits in `KLS/Geometry/` beside the coarea layer it uses,
following the same arrangement as `KLS/Geometry/LevelSetMeasurable.lean`.

**The Lipschitz hypothesis `hK` is entirely unused**: the declaration already assumes `ContDiff ℝ 1 u`,
and L11 needs no Lipschitz bound.

## WIP file changes

`KLS/WIP/CheegerInfimum.lean` only loses this declaration and updates the corresponding module-header description.
After removal, `section Coarea` contains only an empty `namespace Isoperimetry` and an unused `variable` line;
these are removed together (scaffolding only, containing no declaration and changing no signature).
**All other statements, proofs, and declaration positions remain unchanged**. The original file is saved as
`build/audit/iso-migration-CheegerInfimum.before.lean`.

## Hole counts and remaining holes

* `KLS/WIP/CheegerInfimum.lean`: **3 → 2** direct holes, precisely the two Cheeger comparisons
  `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le` and
  `Isoperimetry.smoothConstant_le_minkowskiConstant`.
* `KLS/WIP/AnalyticPrerequisites.lean`: 2 (unchanged). `Energy/WIP/Cheeger.lean`: 5 (unchanged).
* Total: **10 → 9**. Certificates remain **24**; perimeter infrastructure remains **missing**.

`research/audits/IsoperimetryCoareaAudit.lean` imports **both** the new module and **two** WIP files.
The following reports therefore come from one environment, where the migrated name resolves to exactly one declaration:

* `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`: the standard three axioms, **no `sorryAx`**.
* `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (the **Lipschitz** case, without a `C¹` assumption):
  still contains `sorryAx` and remains a direct hole. **The migrated result is its `C¹` specialization and does not imply it.**
* `Analysis.sard` (sharp `C^(finrank)`): still contains `sorryAx`.
* `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`,
  `Isoperimetry.smoothConstant_le_minkowskiConstant`, and
  `Isoperimetry.minkowskiConstant_eq_smoothConstant`: all still contain `sorryAx`.

The client restatement of the Lipschitz case, `client_lipschitz_coarea_statement`, compiles **with `sorryAx`**;
a restatement is not a proof.

## Work excluded from this round

* **No new theorem is proved**; this round only migrates and connects one result.
* **No proof of the Lipschitz case**. It requires **L12 → L7 (exact C¹ pieces) → L6/L6a
  (Whitney first-order jet extension from closed sets and compact jet extraction)**, all unproved.
* No proof of sharp `Analysis.sard`, the two Cheeger comparisons, equality of the two Cheeger constants,
  or sharpness of the Eilenberg constant.
* No expansion of certificate or Blueprint `leanok` scope.
* **No commit or push.**

## Validation

* `KLS/Geometry/IsoperimetryCoarea.lean` compiles separately with `-DwarningAsError=true`.
* `research/audits/IsoperimetryCoareaAudit.lean` compiles with `-DwarningAsError=true`;
  its 8 `#print axioms` reports establish the boundaries above.
* Signature `diff` is empty.
* All other 18 audit clients were rerun and passed strict compilation without changes.
* The three WIP files compile separately, with **2/2/5 direct holes, total 9**.
* Default `lake build` and root-level `python3 research/verify.py` pass. Final receipt:
  `build/verification/latest.json`, matching the complete final source snapshot exactly. Evidence JSON:
  `research/explorations/2026-09-16-isoperimetry-coarea-migration.json`; final snapshot check:
  `build/audit/iso-migration-final-snapshot.json`.
