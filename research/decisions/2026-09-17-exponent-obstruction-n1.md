# N1 Prove: The actual exponential given by the small Lipschitz method

2026-09-17 (on the same day, following `2026-09-17-equidimensional-sard.md`'s round).
This round proves a new theorem: the diagnostic term of rank-deficient paths **`N1`**.
Together with `R0`–`R10`, twelve out of thirteen numbered statements have been verified;
the remaining `N2` was proven false in the previous round, and its corrected version has now been established.

**`N1` is a diagnosis, not an advancement of the program.** It proves exactly the statement that "this path does not work":
The exponential is `k + r`, not `k`. See below "why proving N1 is not an advancement."
No hole, no commit, no push. The direct proof hole remains **8 (1/2/5)**, and the certificate remains **24**.

Start `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`;
Previous round closeout verification receipt `build/verification/20260917T084846.473181Z/report.json`:
10 gates, 223 local module kernel replay, 608 entries, snapshot
`bbc6729f41d7c11b2ef7b9a3c919b5f40ad495a2edf549280f42183dfcd6125b`, drift is empty.
During this round, concurrent sessions (Haocheng Wang's line) **did not modify workspace, and also did not commit**.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard (direct proof hole `Analysis.sard`), five holes of Energy, dimension-free KLS
all untouched. **This round is unrelated to Sard**: `N1` only discusses the Hausdorff measure of a fiber of some map,
mentioning nothing about the critical value set.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/ExponentObstruction.lean`
(ROW 179, local import closure of 2 modules, no WIP, no `sorry`, no `axiom`).

* **`hausdorffMeasure_truncated_add_le`**: `μH[((n − m : ℕ) : ℝ) + m] S ≤ μH[n] S`.
  Truncated subtraction in `ℕ` satisfies `(n − m) + m ≥ n` regardless of whether `m ≤ n`; Hausdorff measure decreases with the exponent.
  This axiom makes the entire proof **not require** `finrank ℝ W₂ ≤ finrank ℝ V`——
  It is precisely `N2` that holds at the point on truncated subtraction, `N1` withstands.
* **`exists_measurable_majorant_of_lipschitz_pieces`** (single scale):
  Given `S`'s countably measurable piecewise, each piece with `Q ∘ u` being `ε`-Lipschitz,
  For each slice using the proven co-dimension `m₂` Eilenberg good function `exists_measurable_majorant_vector`,
  Sum the convex function. Obtain a measurable convex function `G ≥ τ ↦ μH[n − m₂](S ∩ {Q∘u = τ})`,
  and `∫⁻ G ≤ C · ε^{m₂} · μH[n] S`.
  The slice function itself is not measurable (`u` without any regularity assumptions), so one must resort to a majorizing function.
  The measurability and disjointness of piecewise are used here only once: the countable additivity gives
  `∑ᵢ μH[n−m₂+m₂](S ∩ Tᵢ)` composition `μH[n−m₂+m₂](S)`.
* **`ae_hausdorffMeasure_inter_levelSet_eq_zero_of_lipschitz_pieces` (`N1`)**:
  For `ε_j = (j+1)⁻¹`, take majorants `G_j`, then the pointwise infimum `H = ⨅ⱼ Gⱼ` (measurable and still a majorant),
  Then `∫⁻ H ≤ C · ε_j^{m₂} · μH[n] S` holds for each `j`;
  `m₂ > 0` and `μH[n] S < ∞` make the right-hand side tend to `0`, so `∫⁻ H = 0`,
  Since `H` is measurable, it vanishes almost everywhere; it dominates the slices, so the slice is null for almost every `τ`.

Audit `research/audits/ExponentObstructionAudit.lean` (row 244, closure 5 modules, no WIP)
Currently **11 standard three-axiom reports**, among which `route_N1` is a word-for-word replication and proof of the route statement
(script verification, after removing blanks, exactly identical to the route document).

## Why proving `N1` is not progress

The route record had already qualified `N1` as a **statement of an obstacle**, and this round merely formalized it as a theorem without changing this characterization.

* **The exponent is `k + r`, not `k`.** The route `W₂` is the orthogonal complement of the image of rank `r`, `dim W₂ = m − r`,
  hence the exponent `n − dim W₂ = k + r` given by `N1`.
  The audit's `N1_exponent_is_k_add_r` lists this arithmetic separately to prevent misinterpretation.
* **Weakness is in directions with no use.** When `r ≥ 1`, `μH[k+r]` zero measure **does not imply** any information about `μH[k]`:
  On the exponent `k = n − r`, the Hausdorff measure of any Lebesgue measure set is `∞`
  (`N1_null_at_higher_exponent_says_nothing_at_k`, i.e., a special case of the corrected version `N2` proven in the previous round).
* **`R0` does not depend on it.** `R0` has already been independently proven via stratified routes by slicing **within the fiber**
  (`Analysis/StratumSlicing.lean`), where `k + (m − r) = n − r` is indeed the correct exponent.
  `Analysis/ExponentObstruction.lean` has no downstream consumers.

## Side conditions are necessary

`0 < finrank ℝ W₂` is not decorative. The audit of `N1_needs_positive_codimension`
Negates the `N1` after **removing this assumption** (`Type` instance; the route's `Type*` version entails it),
counterexamples are `V = W = ℝ`, `W₂` zero-dimensional, `Q = 0`, `u = id`, `S = [0,1]`:
The piecewise assumption holds trivially (`Q ∘ u` is constant), and the only fiber is the entire `S`, `μH[1] S = 1 ≠ 0`.
In zero dimension, the Eilenberg constant `ε^{dim W₂} = 1`, nothing tends to zero.

`S` Measurability is also genuinely used, see above.

## What remains unproved

* **No proof of any Sard theorem**, unrelated to `Analysis.sard` this direct proof hole, its status remains unchanged.
* **`N2` remains unproven and is known to be false**; what has been proven is its corrected version (from the previous round).
* No migration holes, no new certificate, no expansion of Blueprint `leanok` scope, no new compatible alias,
  no weakening of already proven conclusions, no addition of unnecessary assumptions. dimension-free KLS remains open.
* No modification to any existing `.lean` file (this round only adds one module, and expands **this round's own** previous step newly created `ExponentObstructionAudit.lean`); the route statement file `RankDeficientRouteStatements.lean`
  remains **byte-for-byte unchanged**.

## Verification

* The new module and audit client have both passed `-DwarningAsError=true`.
* Retested **52** audit clients (`research/audits` 45 and `build/audit` 7), all strictly passed, **0 failures**.
* The full library axioms report **672** entries (previous round 665 + current round 7), of which **12** entries `sorryAx` remain unchanged, still all within the four intentionally reported WIP pending results clients.
* Each of the three WIPs was compiled in practice, direct proof hole **1/2/5**, total count **8**, unchanged; `check_ledger.py` issued **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` passed;
  JSON evidence is `research/explorations/2026-09-17-exponent-obstruction-n1.json`,
  local logs are at `build/audit/exponent-obstruction-n1/`,
  final reconciliation saved to `build/audit/exponent-obstruction-n1/final-snapshot.json`.
* No commit, no push; the real Git index was not modified.

---

## Addendum (2026-09-17, later the same day; main text unchanged)

On the same day, a round of file management adjusted the two mentioned locations/names, **the mathematical content and types remained unchanged**:

* Revised version `N2` has been moved from audit client to module, now is
  `Analysis.hausdorffMeasure_finrank_sub_eq_top` ( `Analysis/ExponentObstruction.lean` ),
  previously named `ExponentObstructionAudit.hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos`.
  The module thus gains `import Analysis.LevelSet`, local import closure changes from 2 to **4**, still no WIP.
  Audit retains only route accounting item `N2_repair_is_free_on_the_route` and counterexample `route_N2_is_false`.
* `ExponentObstructionAudit` originally declared zero-dimensional space twice ( `Pt₀` and `Pt` ), now merged into one `Pt`;
  client has been reorganized with `N1` all at the front and `N2` all at the back.

The rest of the above records remain unchanged: `N1` is still a verified diagnostic item, the exponent remains `k + r` rather than `k`,
it is still **not progress toward the program**; `N2` remains unproven and known to be false; `Analysis.sard` is still a direct proof hole.
