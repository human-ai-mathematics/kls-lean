# R10 proved: the equidimensional degenerate case; N2 found false as stated

2026-09-17. This round **proves a new theorem**: the **`R10`** of rank-deficient paths (in the same-dimensional degeneration case, `n = m`),
i.e., almost no level is a critical value. Out of thirteen numbered statements, eleven have been fulfilled.

This round also discovered and proved in Lean: route diagnosis `N2` is false by literal statement (counterexample on zero-dimensional space),
and proved the corrected version after adding `0 < finrank ℝ V`. `N1` remains unproven.

**`R10` is not any general Sard theorem, nor a step toward `R0`.** See “Work excluded from this round” below.
No migration hole, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`; start verification receipt
`build/verification/20260917T080255.188361Z/report.json`: 10 gates, 222 local module kernel replay,
603 entries, snapshot
`bce9cda59abe8b2674cb72ce76c02b4e21d7adf9abcb97361a542a6f21a2e530`.
The start workspace drift is empty, with no commit outcomes 27 items, all retained.
During this round, concurrent sessions (Haocheng Wang's line) **made no changes to the workspace, and also did not commit**: at closeout
`HEAD = origin/main` remains `e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`.

## Boundary

Log-concave Cheeger–Buser inequality—alignment of several definitions of isoperimetric constants, up to bidirectional comparison with Poincaré constants,
containing `KLS/WIP/CheegerInfimum.lean` two remaining holes—attributed to author **Haocheng Wang**, untouched in this round.
Sharp finite regular Sard (direct proof hole `Analysis.sard`), five holes in Energy, dimension-free KLS also untouched.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/EquidimensionalSard.lean`
(ROW 123, local import closure of 18 modules, no WIP, no `sorry`, no `axiom`).

* **`ContinuousLinearMap.det_eq_zero_of_not_surjective`**: If a linear endomorphism of a finite-dimensional space is not surjective, then its determinant is zero.
  Mathlib has only the reverse (`LinearMap.range_lt_top_of_det_eq_zero`); the forward direction requires an injection,
  And injectivity is equivalent to surjectivity only in finite dimensions.
* **`measure_image_critical_eq_zero`**: `finrank ℝ V = finrank ℝ W` when `C¹` maps `u` to
  The image of the critical set is a Lebesgue null set. The proof uses the self-mapping lemma from Mathlib
  `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` along this repository's
  `isometryEquivOfFinrankEq` Transport: **pre**-compositional inverse isometry rather than post-compositional,
  Thus, anything that was already inside `W` does not need to be moved again.
* **`ae_critical_inter_levelSet_eq_empty` (`R10`)**: In the same dimension, almost every level set completely avoids the critical set.
  Fiber dimension `k = 0`, `μH[0]` zero measure implies the empty set, so `R0`'s conclusion degenerates to "the slice is empty".

## `R10` and the boundary with general Sard (a section that must be read)

`R10` Indeed, it is the only statement among the thirteen axioms of the rank-deficient guiding principles concerning a **critical value**, and thus most susceptible to misinterpretation. The dividing line is as follows.

* **Sard's theorem** states that the set of critical values of `ℝⁿ → ℝᵐ` has zero measure. Here we prove only the case of `n = m`,
  And that situation holds purely because the singular linear map compresses volume—the Mathlib already has a version for self-maps.
  At `n > m`, the set of critical values of the map of `C¹` can have positive measure (Whitney), and no statement below contradicts this.
* **Direct proof hole `FunctionalInequalities.Analysis.sard`** (`KLS/WIP/AnalyticPrerequisites.lean`)
  It says: real-valued `u`, **arbitrary** dimension `n`, domain with `C^n` regularity.
  This round and its entire overlap is `finrank ℝ V = 1` (`r10_reaches_only_dimension_one` notes this point),
  And that case `Analysis.sard_of_finrank_le_one` has already been conditionally proven, using the same Mathlib lemma.
  The audit `sard_dimension_one_recovered` makes this overlap instead of asserting it.
  `n ≥ 2` No word was said in this round. **`Analysis.sard`'s direct proof hole status remained completely unchanged.**
* Not progress toward a program. The route exploration round has explicitly written `R10` is not on the path to `R0`; `R0` is now handled by layered routes
  proved independently; that route never specializes to `n = m`. `R10` is a subsequent corroboration/consistency check.
  `Analysis/EquidimensionalSard.lean` **do not import any part of rank-deficient paths**,
  So this check is truly independent: the audit's `equidimensional_R0_of_R10` and
  `equidimensional_R10_of_R0` is mutually implied at `n = m` — the `μH[0]` of a non-empty set is at least `1`,
  So the two statements are equivalent in this case—two independent proofs yield the same conclusion.

## `N2` Literally false

The route statement of `N2` is

  `volume S ≠ 0 → 0 < r → μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤`,

Here `finrank ℝ V - r` is **truncated** natural-number subtraction. Set `finrank ℝ V = 0`: the space is a point,
The only non-zero measure set is this point, with truncation exponent being `0` rather than a negative number, and the `μH[0]` of a singleton set is `1`, not `⊤`.

* `ExponentObstructionAudit.N2_counterexample` List three things separately: `finrank ℝ Pt = 0`,
  `volume univ ≠ 0`, `μH[((0 - 1 : ℕ) : ℝ)] univ = 1`.
* `route_N2_is_false` This leads to a contradiction. It negates the `Type` instance of the route statement;
  The `Type*` version in the path entails this instance, so denying this one negates it.

**The correction restores the positivity of the dimension and has been proven.**
`hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos` is simply adding `0 < finrank ℝ V` to `N2`.
This assumption is **necessary**, as evidenced by counterexamples, not merely weakening the conclusion; it remains **free** in the actual route where it is referenced `N2`:
there, `r` is the rank satisfying `1 ≤ r < finrank ℝ W ≤ finrank ℝ V`, and the dimension is inherently positive,
`N2_repair_is_free_on_the_route` records this implication. Thus, `N2` retains its **diagnostic role** in the route record.

The route statement file `research/audits/RankDeficientRouteStatements.lean` preserves **bytes unchanged**,
wherein `N2` remains an undelivered—and, according to this round's record, false—obligation.

## What remains unproved

* **No proof of any general Sard theorem.** See the previous section. The sharp finite regular Sard remains a direct proof hole, untouched.
* **`N1` unproven.** It serves as a diagnosis of "what the small Lipschitz method actually yields," requiring the Eilenberg good function machinery, which was not carried out in this round; it is not a step, `R0` is not dependent on it.
* **`N2` unproven, and has been proven to be false;** the correct version was established and is now properly distinguished from `N2` in naming.
* No proof holes, no addition of certificates, no expansion of Blueprint `leanok` scope, no addition of compatible aliases,
  no weakening of already proven conclusions, no introduction of unnecessary assumptions. dimension-free KLS remains open.

## Boundary cases

Audit coverage per item: `zero_dimensional` (both spaces are trivial: any linear map is surjective, the critical set is empty), `constant_map` together with its accompanying `constant_map_critical_everywhere` (the derivative is identically zero, everywhere critical in positive-dimensional target spaces, the conclusion still holds because the image of the entire map consists of a single point—this boundary case is not hollow), `regular_map` (`n = m` and the differential is invertible everywhere, the critical set is empty, the conclusion holds for each level, not just almost every level).

## Verification

* The new module and two new audit clients have passed `-DwarningAsError=true`,
  **No `sorry`, no `axiom`, no placeholder, no weakening**.
* `EquidimensionalSardAudit.lean` (row 208, closure of 37 modules, no WIP):
  **13 Standard Three Axiom Report**, where `route_R10` is the word-for-word replication and proof of the route statement
  (Verified by script to be identical character by character when blank spaces are removed).
* `ExponentObstructionAudit.lean` (row 119, closure of 3 modules, no WIP):
  **4 Standard three axioms report**. Among them, the proposition and route of `route_N2_is_false` are identical word for word after blank removal, and match `N2`.
  Only replace `Type*` with `Type` (otherwise it is impossible to negate a universally quantified universe-polymorphic statement in Lean).
* Restart **52** audit client(s) (`research/audits` 45 , `build/audit` 7),
  All passed strictly via `-DwarningAsError=true`, **0 failed**.
* Library axioms report **665 items** (previous round 648 + current round 17), among which **12 items `sorryAx` remain unchanged**,
  Still entirely falls within the four clients that intentionally reported unresolved WIP results
   (`LevelSetMeasurableAudit`, `IsoperimetryCoareaAudit`, `LipschitzCoareaMigrationAudit`,
  `build/audit/SuperlevelSardScope`).
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports **24** certificates.
* Modified no existing `.lean` files; aggregate import unchanged.
* The default `lake build` is connected to the root directory `python3 research/verify.py`;
  Evidence JSON is `research/explorations/2026-09-17-equidimensional-sard.json`,
  Local logs at `build/audit/equidimensional-sard/`,
  Final verification and save `build/audit/equidimensional-sard/final-snapshot.json`.
* **No commit, no push**, the real Git index remains unchanged.

---

## Addendum (2026-09-17, later the same day; main text unchanged)

The note "**`N1` unproven**" recorded in the previous section was true at the time of writing, but has since ceased to hold:
A subsequent round of proof established `N1`, see `research/decisions/2026-09-17-exponent-obstruction-n1.md` and `research/explorations/2026-09-17-exponent-obstruction-n1.json`.
This addendum does not alter any other record in the previous text: the boundary between `R10` and general Sard remains unchanged,
`N2` remains unproven and is known to be false (corrected version has been proven), `Analysis.sard` is still a direct proof hole,
the direct proof hole still 8 (1/2/5), the certificate still 24.
The proof of `N1` is **not an advancement of the program**—it merely verifies the statement of the obstacle itself, with exponent `k + r` rather than `k`.

## Note 2 (2026-09-17, same-day file management rotation, main text unchanged)

The two statements mentioned above have been renamed, **types and proofs unchanged**:

* `ContinuousLinearMap.det_eq_zero_of_not_surjective` → `Analysis.det_eq_zero_of_not_surjective`.
  Previously nesting `ContinuousLinearMap` namespace inside `Analysis`, dot notation would not resolve to it
  (Point notation only recognizes root's `ContinuousLinearMap`), is equivalent to blindly reinserting the namespace into the short name,
  Hit `research/naming.md` First.
* The previous "revised version" `hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos` has been moved into the module,
  Now is `Analysis.hausdorffMeasure_finrank_sub_eq_top`.

`R10` and the general Sard boundary, `N2` is false, direct proof hole 8 (1/2/5) and certification 24 are both unaffected.
