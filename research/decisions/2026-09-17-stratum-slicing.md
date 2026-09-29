# Layer-wise local slicing R7: Local bundles and target space decomposition proven, **R7 itself unproven**

2026-09-17. The goal of this round is `R7`. **`R7` has not been proven**, and `R0` remains open.
This round proves two components of `R7`: the **local patch** (assembling the already proven `R2`, `R3`, `R4` into a neighborhood with a **uniform constant**) and the **integral form of target space decomposition** (change of variables + Tonelli). The remaining gaps are precisely written as `R7b`, `R7c`, containing only `#check`, one unproven statement.
This round **does not prove any coarea formula, any slicing theorem for critical sets, or any Sard theorem**.
No hole migration, no commit, no push. The direct proof hole remains **8 (1/2/5)**, and the certification remains **24**.

Start `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`; start verification receipt
`build/verification/20260917T065323.126590Z/report.json`: 10 gates, 220 local module kernel replay,
592 entries, snapshot
`b9df57d18dfff53fae863419fc7ad261a19b37889026c1d14a1cc8c57969f03a`.
Start workspace drift is empty. No changes to workspace in this round of concurrent session.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## This round modified an existing `.lean`—record it faithfully

`formalization/FunctionalInequalities/Analysis/TangentialLipschitz.lean` (from the previous `R4` round of module,
not yet commit) is changed into the form of **explicitly providing constants**
`lipschitzOnWith_of_ker_bound`, while the original existence form `exists_lipschitzOnWith_of_ker_bound`
(i.e., the route's `R4` statement) is **retained exactly** and directly derived from the explicit form.
This is a **strict strengthening**, neither weakening any previously proven conclusions nor altering the route statement of `R4`.

The reason is rigid: assembly requires the **same constant** to hold on all pieces in the piecewise approximation.
The existential constant depends on each piece’s linear model `fderiv ℝ u y`, so no uniform bound can be extracted.
This is also where the rationale for listing the *neighborhood-consistent version* of `R3` as a hard requirement in the previous round is fulfilled.

## What is proved

New module `formalization/FunctionalInequalities/Analysis/StratumSlicing.lean`
 (209 line, local import closure 25 modules, no WIP).

* **`exists_stratum_local_data` (local bundle)**: Let `x₀` be on a rank `r` stratum,
  `K = range (Du x₀)`, `P`, and `Q` are orthogonal projections onto `K` and `Kᗮ`. Then there exists
  an open neighborhood `U` of `x₀` with compact closure and **one** constant `c`, such that
  * `P ∘ u` is regular everywhere on `closure U` (`coareaJacobian ≠ 0`);
  * For **every** `y` in the stratum lying in `U`, **every** `ε`, **every** set `S`
    approximated by `fderiv ℝ u y` within `ε`, and **every** fiber `s`,
    `Q ∘ u` is `c ε`-Lipschitz on `S ∩ {P ∘ u = s}`.

  **Uniformity of `c` over `y` is the main difficulty**: piecewise approximation provides different linear models on each piece, and the constant of `R4` through `‖fderiv ℝ u y‖` and the right inverse bound depends on this model.
The unified constant is given by `R2` (the kernel lemma), the **neighborhood version** of `R3`, and the bound of `‖fderiv ℝ u‖` near a point.

* **`lintegral_split_target` (integral form of target space decomposition)**:
  The integral over the target space equals the iterated integral along an orthogonal decomposition. This is the **integral version** of `R6`'s action on null sets, and also the shape that successive-scale estimates are ultimately integrated against. Using Mathlib's `LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_toLp`, and Tonelli, it is only required that the integrand be measurable almost everywhere.

* Supporting lemmas `fderiv_clm_comp` (the chain rule for continuous-linear postcomposition) and `surjective_proj_comp`
  (the regular component at the base point is indeed immersive), `finrank_tangentRange_eq` (the dimension of the layer is equal).

## Nothing proven—`R7` itself

**`R7` unproven.** Missing are two steps, precisely written in `#check` under `research/audits/StratumSlicingRouteStatements.lean`, **one unproven**:

* **`R7b` (scale-by-scale estimate)**: On a fixed scale `ε`, the total fiber measure of the stratum over the entire target space
  The integral multiplied by `ε^{m−r}` is controlled by the regular component coareaJacobian; the constant is independent of `ε`.
  The path is: perform a approximation partitioning on `u` itself (a set of partitions serving two components simultaneously);
  On each piece, obtain a fiber-direction `c ε`-Lipschitz using local packages; in the **interior of the fiber** using
  The Eilenberg bound of `Analysis/VectorHausdorffSlicing.lean`, taking the exponential `k` and target dimension `m − r`,
  At this point `k + (m − r) = n − r` holds exactly; then integrate along the fiber parameter using the **already proven** regular coarea formula
  Replace the fiber measure with a regular integral of the coarea Jacobian; finally read off the integral over the target space using `lintegral_split_target`.
* **`R7c` (`ε → 0`)**: This bound has the shape valid at each scale, finite at the right end, and positive exponent (i.e. `r < m`),
  Forces the integral to be zero, hence almost everywhere zero. This is a pattern already used twice in repository
  (`VectorHausdorffSlicing.lean` and `VectorCriticalSlice.lean`).

Before these two are completed, **`R7` is open, `R0` is open, the general coarea formula for codimension m is open**.

## What hasn't been done in this round

* **No proof `R0`**; `R8`–`R10`, `N1`, `N2` are also unproven.
* **No proof of any coarea formula**; the scope of proven formulas has not been expanded in the slightest.
* **No proof of any Sard theorem**; nothing is asserted about the measure of the critical value set.
* Aside from the strengthening of `TangentialLipschitz.lean` noted above, no other existing `.lean` has been modified
  (`FunctionalInequalities.lean`, `RankDeficientRouteStatements.lean`, `AreaFormulaRouteStatements.lean` remain unchanged); no holes have been migrated; no extension of certification or Blueprint `leanok` scope; no new compatible alias added; no weakening of established conclusions.
* **No commit, no push**, the real Git index remains unchanged.

## Verification

* The new module and two new clients have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **11 Axiom Report** of `research/audits/StratumSlicingAudit.lean` only uses
  `propext`, `Classical.choice`, `Quot.sound`.
  `research/audits/StratumSlicingRouteStatements.lean` Contains only **2 `#check`**, no declarations.
* Retest all **47** existing audit clients plus two new clients, totaling **49**; all strictly passed, 0 failed;
  The axioms report 629 items, among which 12 items `sorryAx` are still entirely within the client side of four intentionally reported unresolved WIP results.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-stratum-slicing.json`,
  Final verification and save `build/audit/stratum-slicing/final-snapshot.json`.
