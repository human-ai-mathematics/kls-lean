# Moving superlevel-set packaging out of WIP and eliminating sorryAx

2026-09-15, following the same day's [C^∞ Sard result](2026-09-15-smooth-sard.md). The starting receipt
`build/verification/latest.json` (`20260914T171940.461693Z`) passed; recalculation confirmed
byte-for-byte equality with the workspace. HEAD remains `2965b32`; no commit or push.

## Completed scope

Added the hole-free module `formalization/FunctionalInequalities/KLS/Geometry/RegularSuperlevel.lean`,
with two declarations moved from `KLS/WIP/CheegerInfimum.lean` **without changing their statements**:

* `SmoothDomain.frontier_superlevel_subset` (already hole-free; its proof is unchanged verbatim);
* `SmoothDomain.ae_exists_superlevel` (**statement unchanged verbatim**, with the proof reconnected to the proved
  `Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`).

Both `pp.all` signatures are **byte-for-byte identical** before and after the move (checked with `diff`; see
the migration logs in `build/audit/`). After the move:

```
'FunctionalInequalities.KLS.SmoothDomain.ae_exists_superlevel' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

Thus **`ae_exists_superlevel` no longer inherits `sorryAx`**. This is the first conclusion in the KLS chain whose
Sard-induced `sorryAx` dependency has actually been removed.

## Placement and dependencies

The documentation of `Geometry/SmoothDomain.lean` explicitly describes it as a "foundational layer independent of perimeter recovery, coarea, and Sard."
The packaging was therefore **not** placed back in that module; instead, a new layer `Geometry/RegularSuperlevel.lean`
imports `Geometry/SmoothDomain` and `Analysis/SmoothSard`.

Corresponding changes to `WIP/CheegerInfimum.lean`: removed the two relocated declarations and the empty `namespace SmoothDomain` block,
and replaced `import FunctionalInequalities.KLS.WIP.AnalyticPrerequisites` with
`import FunctionalInequalities.KLS.Geometry.RegularSuperlevel`.
The module still compiles after removing that import, demonstrating that its **only** actual dependency on `AnalyticPrerequisites` was the
Sard consequence. Now **no module imports `KLS/WIP/AnalyticPrerequisites.lean`**;
the sharp Sard and coarea holes are isolated in a file with no importers.

Documentation synchronization: the module comment in `WIP/CheegerInfimum.lean` was corrected from "four `sorry` proofs" to three
(the count was already stale before the previous round), and the entire paragraph describing the Sard route was rewritten.
`build/audit/SuperlevelSardScope.lean` was updated to record the new boundaries.

## Verification and axiom boundaries

* `Geometry/RegularSuperlevel.lean` passed strictly with `-DwarningAsError=true`.
* `build/audit/SuperlevelSardScope.lean` passed strictly; its 6 axiom reports show the boundaries side by side:
  `client_ae_superlevel`, `ae_exists_superlevel`, `frontier_superlevel_subset`, and
  `Analysis.sard_smooth` use only the three standard axioms;
  `Analysis.ae_forall_fderiv_ne_zero` and `Analysis.sard` **still contain `sorryAx`**.
* After updating `SmoothSardAudit`, all 12 reports contain only the three standard axioms, with no `sorryAx`.
* `SmoothSardIngredientsAudit`, `SuperlevelDomainAudit`, `QuadraticRemainderAudit`,
  `QuadraticCoverAudit`, `PlanarSardAudit`, `HigherSardAudit`, `SardLowDimAudit`,
  `AreaFormulaAudit`, `CheegerInfimumAudit`, and `MinkowskiConstantAudit`
  all passed strict rechecking, **without changes**.
* Each of the three WIP files was actually compiled: direct holes remain **3/3/5**, totaling **11**.
  The moved declaration had a **filled proof body**, rather than a direct hole, so the hole count is unchanged.
  This distinction matters: the round reduced transitive `sorryAx` dependencies, not the number of holes.
* Certificates remain **24**, and perimeter infrastructure remains **missing** (its gaps are determined by
  coarea and the reverse comparison, neither addressed in this round).
* The default `lake build` passed (3393 jobs). The final snapshot receipt for root `python3 research/verify.py` is
  `build/verification/latest.json`. Evidence hashes are recorded in
  `research/explorations/2026-09-15-superlevel-rewire.json`.

## Explicitly incomplete

* **Sharp `C^(finrank)` Sard**: `Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero`
  remain, respectively, a direct hole and a filled proof body containing `sorryAx` in `WIP/AnalyticPrerequisites.lean`.
  Their statements are unchanged; the `n = 4, j = 2` obstacle is untouched. They now have **no downstream consumers**.
* **Weighted coarea** `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`,
  its level-set measurability result, and the `C¹` specialization in `Isoperimetry`: three untouched holes.
* **Reverse Cheeger comparison** `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, and equality of constants remain unproved
  and transitively depend on `sorryAx`; only the direction `h_M ≤ h_S` has been proved.

The complete chain is **not** closed. The next blocker is weighted coarea.
