# R7 Prove: Layer-by-layer local slice

2026-09-17. This round's **proof of a new theorem**: the **`R7`** of rank-deficient paths—layer-by-layer local slices.
Together with `R1`–`R6`, seven out of thirteen statements have been fulfilled.
**`R0` remains open**: it still requires `R8` (extending `R7` from a neighborhood to the entire layer) and a finite union over `r < m`.
This round **proves no coarea formula in new settings, no slicing theorem for the full critical set, and no Sard theorem**.
No hole migration, no commit, no push. The direct proof hole remains **8 (1/2/5)**, and the certification remains **24**.

Start `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`; start verification receipt
`build/verification/20260917T072259.478204Z/report.json`: 10 gates, 221 local module kernel replay,
597 entries, snapshot
`05569e6d2c0537b968c5a57d17df14c5e3aee6a49541e5713afcabc3608be01f`.
Start workspace drift is empty. No changes to workspace in this round of concurrent session.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Exact Results

On `formalization/FunctionalInequalities/Analysis/StratumSlicing.lean` (row 489,
local import closure 34 modules, no WIP), proceed with:


* **`lintegral_hausdorffMeasure_stratum_le` (`R7b`, scale-by-scale estimate)**:
  For each `ε ≠ 0`,
  `∫⁻_W μH[k](Σ_r ∩ U ∩ u⁻¹(t)) dt ≤ Cst · (c ε)^{m−r} · ∫⁻_{Σ_r ∩ U} coareaJacobian(D(P∘u))`,
  **`Cst` is unrelated to `ε`**.
  The proof is the route written in the previous round: run Mathlib's approximation partition once on `u` itself; a set of partitions serves two components simultaneously.
  On each piece, obtained from local packages `Q ∘ u` is `c ε`-Lipschitz along the fiber;
  In the **fiber interior** using Eilenberg's bound `VectorHausdorffSlicing.lean`,
  Take exponential `k`, target dimension `m − r`, at this point `k + (m − r) = n − r` is exact;
  When integrating along fiber parameters, use the **already proven** regular coarea formula (with weight `1`) to replace the fiber measure with an ordinary integral of the coarea Jacobian;
  Finally read the integral over the target space using `lintegral_split_target`.
* **`exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero` (`R7`)**:
  `ε → 0`. The right-end factor is finite (the neighborhood closure is compact, the integrand is continuous and bounded),
  The exponential `m − r` is positive precisely because `r < m`, so the integral over the target space is zero, and the integrand is almost everywhere zero.
* Corresponding `hausdorffMeasure_eq_inv_mul_normalized` (interchange between raw and normalized Hausdorff measures)
  And `finrank_tangentRange_eq_of_mem`.

## Where is the error index fixed?

The one-step method forces the Eilenberg bound into exponential `k + r`; forcing a return `k` yields the right-hand side as
a `μH[n−r]` of a positive Lebesgue measure set, i.e., `∞` (which is exactly `N2`).
**Within the fiber** the same bound is applied to exponential `k`, with the right-hand side replaced by a finite `ℋ^{n−r}` measure of the fiber itself—matching the dimensions.
This is also the setting for `R5` (fiber finiteness) and `R6` (target space decomposition):
The current application employs the same two engines (the established regular coarea formula, measure-preserving change of variables plus Tonelli), appearing in integral form rather than as a zero-measure set.

## This round modified two existing `.lean`—recorded accurately

Both are in their own session files, not yet commit, and both **do not decrease**.

* `Analysis/StratumSlicing.lean`: Add the three theorems above, and **rewrite the module documentation stream** —
  It previously stated "`R7` unproven", which is no longer valid and must be changed. The original
  `exists_stratum_local_data` and `lintegral_split_target` **remain unchanged in wording**.
* `research/audits/StratumSlicingRouteStatements.lean`: Add a status statement at the file header
  (`R7b` and `R7c` are now proven, `R0` remains open), **the two `#check` propositions remain unchanged in wording**.
  This is consistent with the collaborator's previous handling of `RankDeficientRouteStatements.lean`.

`research/audits/RankDeficientRouteStatements.lean` and `AreaFormulaRouteStatements.lean`
**Not modified in this round**.

## What was not done in this round

* **No proof `R0`**. `R7` is a statement about **a stratum of rank, a neighborhood**;
  reaching `R0` still lacks `R8` (second countable ⟹ countable subcover, locally patching up to the full stratum)
  and a finite union over the layers of `r < m` (the decomposition of `R1` is already prepared).
* No proof of `R8`, `R9`, `R10`, `N1`, `N2`.
* **No coarea formula proved in new settings**; the scope of proven formulas has not expanded at all.
* **No Sard theorem proved**; no claim about the measure of the critical value set.
* No modification to `FunctionalInequalities.lean`; no migration of holes; no expansion of certification or Blueprint `leanok` scope;
  no new compatible aliases added; no weakening of established conclusions.
* **No commit, no push**, the real Git index unchanged.

## Next step

**`R8`** (local to global completion, estimate 90 line, low to medium risk), then `R0` is
the finite union of `R1` plus `R8`; further on comes `R9` (the coarea formula without the dichotomy assumption of codimension m).

## Verification

* The module and both clients compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **16 Axiom Report** of `research/audits/StratumSlicingAudit.lean` only uses
  `propext`, `Classical.choice`, and `Quot.sound`; `route_R7` is
  The `RankDeficientRouteStatements.lean` `R7` statement is **verbatim copied and proven**.
* Retest all **49] audit clients**, all strictly passed, 0 failed; axiom report 634 items,
  All 12 reports containing `sorryAx` still come from four clients that **deliberately** report unresolved WIP results.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-stratum-slicing-complete.json`,
  Final verification and save `build/audit/stratum-slicing-complete/final-snapshot.json`.
