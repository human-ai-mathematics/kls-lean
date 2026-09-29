# R8, R0, R9 Proved: Rank Deficiency Critical Sets and Co-dimension m Coarea Formula

2026-09-17. This round of **proving a new theorem**: the **`R8`** (local to global) of rank-deficient paths, **`R0`** (the target itself), and **`R9`** (the codimension m coarea formula without the critical set assumption).

Together with `R1`–`R7`, ten out of thirteen numbered statements have been fulfilled.

The rank deficiency gap of the m-codimensional coarea program is now closed: the general m-codimensional coarea formula for `C¹` map has been established.

**This is not any Sard theorem**: It says nothing about the measure of the critical value set.
No hole, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`; start verification receipt
`build/verification/20260917T074617.481735Z/report.json`: 10 gates, 221 local module kernel replay,
599 entries, snapshot
`3ae6039e5db626e1937bb51bcf07cefc99e07e399abb199b8136007b30fbf279`.
Start workspace drift is empty. No changes to workspace in this round of concurrent session.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/RankDeficientCoarea.lean`
 (204 line, local import closure 35 modules, no WIP).

* **`ae_hausdorffMeasure_inter_levelSet_eq_zero_of_local` (`R8`)**:
  Local zero-measure sections can be extended to global sections. `V` Second-countable, the neighborhood family has a countable subcover, and almost everywhere quantifiers withstand countable intersections.
  Without using `u` regularity, nor `A` measurability.
* **`ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero`**: By `R7` + `R8`, each layer has overall zero measure.
* **`ae_hausdorffMeasure_critical_inter_levelSet_eq_zero` (`R0`, route's goal)**:
  The **entire** critical set `{x | fderiv ℝ u x is not surjective}` of a `C¹` map has zero `ℋ^k` measure on almost every level.
  By taking the finite union of the layer-wise conclusions to `r < m` (the decomposition of `R1`), we obtain.
  **No need for positive codimension**: When the target space is zero-dimensional, each linear map is surjective, and the critical set is empty, so the statement is vacuously true rather than false.
* **`coarea_of_contDiff` (`R9`)**: The m-codimensional coarea formula, **with no assumptions on the critical set**.
  `VectorCriticalSlice.lean` Previously, the proof was carried out under the assumption that "the derivative is zero at differential non-surjective points"—`m ≥ 2` at that time that was indeed a restrictive condition,
  Its own audit using a rank-one projection on the plane provides a counterexample; `R0` remove this assumption entirely.
  Lack of finiteness, boundedness, integrability, or regular value assumptions, `S` any Borel, `g` any measurable `ℝ≥0∞` weight,
  There is no need for the codimension to be positive.

## How is the path made feasible (in one sentence)?

`R1` Divide the critical set into finitely many measurable sheaves according to the exact rank of the differential.
On sheaves: `R2` says the differential vanishes along the regular components `P ∘ u` in the fiber direction, `R3` quantifies it using a uniformly bounded right inverse bound in neighborhoods,
`R4` Combine the two such that the fiber direction is proportional to the Lipschitz constant `ε`.
`R7` Run approximation of piecewise on `u` itself, and use Eilenberg bound—inside the fiber.
There `k + (m − r) = n − r` is exactly the correct exponent—then integrate the established regular coarea formula along the fiber parameter;
This gives the zero measure property of the layer in a neighborhood of each of its points.
`R8` uses second countability to assemble these neighborhoods; taking a finite union over `r < m` gives `R0`,
The critical part vanishes on both sides of the coarea equation, yielding `R9`.

**The error index is fixed within the fiber**: the same Eilenberg bound is forced to apply to the ambient space, resulting in an index `k + r`;
forcing a return to `k` makes the right endpoint a `μH[n−r] = ∞` of positive Lebesgue measure sets (this is precisely the route diagnosis `N2`).

## What remains unproved

* **No proof of any Sard theorem.** `R0` speaks about the measure of the critical set **within a level**;
  it says nothing about the measure of the critical **value** set, merely asserting that the measure of the critical value set can be positive according to `C¹`.
  The sharp finite regular Sard remains a direct proof hole, untouched.
* **`R10`** (in the co-dimension degenerate case, a cheap side argument) remains unproven;
  **`N1`, `N2`** are diagnostic statements for obstructions, not steps, and remain unproven.
* The map assumption is `C¹`, **not** Lipschitz; the fiber measure is the **normalized** Hausdorff measure,
  following the existing convention in repository.
* No migration holes; no expansion of certification or Blueprint `leanok` scope; no new compatible alias added; no weakening of previously proven conclusions.
* No modification to `FunctionalInequalities.lean`, nor any modification to any existing `.lean`.
* **No commit, no push**, the real Git index remains unchanged.

## About `RankDeficientRouteStatements.lean`

This file **preserves the original bytes**. Its header status statement (added by collaborators in `e7c4403`) is now outdated—
it previously stated that `R0`, `R4`–`R10` are still open, while in fact `R4`–`R9` and `R0` have all been proven.
This round **did not modify it**: it is a historical snapshot marked as commit, and collaborators previously exercised editing on it;
by the agreement in repository, "duties have been fulfilled" is recorded by the audit client performing a verbatim copy and proof of its propositions,
as exemplified by `research/audits/RankDeficientCoareaAudit.lean`'s `route_R8`, `route_R0`, and `route_R9`.
To refresh the file's status statement, leave it to the current maintainers.

## m = 1 rollback of the scalar case

The audit `scalar_L10` and `scalar_L11` are retrieved from the m-codimensional version,
along with `KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` and `KLS.coarea_of_contDiff`,
both of which require an additional `1 ≤ finrank V`—the same **accurate difference recorded** as in the previous rounds.

## Verification

* The new module and new client have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **14 Axiom Report** of `research/audits/RankDeficientCoareaAudit.lean` only uses
  `propext`, `Classical.choice`, and `Quot.sound`; among these, `route_R8`, `route_R0`, and `route_R9`
  It is the statement of `RankDeficientRouteStatements.lean` copied word for word and proved.
* Retest all **49** existing audit client instances plus new clients, totaling **50**; all strictly passed, 0 failures;
  The axioms report 648 items, among which 12 items `sorryAx` are still entirely within the client side of four intentionally reported unresolved WIP results.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-rank-deficient-coarea.json`,
  Final verification and save `build/audit/rank-deficient-coarea/final-snapshot.json`.
