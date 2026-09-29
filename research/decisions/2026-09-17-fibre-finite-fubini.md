# Finiteness of fibers and target space Fubini: R5 and R6 for rank-deficient paths

2026-09-17. This round's **proof of a new theorem**: the obligations on the rank-deficient path checklist for **`R5`** and **`R6`**, following the suggested order's fifth step
(two independent paths, parallelizable). Together with `R1`–`R4`, six out of thirteen numbered statements have been fulfilled.
**Only `R5` and `R6` have been proven**; `R0`, `R7`–`R10`, `N1`, `N2` remain unproven,
the rank-deficient part of coarea dimension m is still open.
This round **proves no coarea formula in the new setting, proves no slicing theorem for critical sets, proves no Sard theorem**.
No hole-filling, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`; start verification receipt
`build/verification/20260917T063346.288828Z/report.json`: 10 gates, 218 local module kernel replay,
586 entries, snapshot
`48d51f94be3b32ff9459acee074af1301a84518c7eb05cc2104187f1d0e28c3e`.
Start workspace drift is empty; start has not commit item exactly equal to the previous round's (`R4`) result. The current round's **concurrent sessions did not modify the workspace**.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## `R5`: The fibers of the regular part have finite measure

New module `formalization/FunctionalInequalities/Analysis/RegularFibreFinite.lean`
 (103 line, local import closure 22 modules, no WIP).

**Purpose.** The route applies the Eilenberg bound internally to the fiber, taking `d = k`, the target space dimension `m − r`,
thus `d + (m − r) = n − r`. For this bound to yield meaningful information, the fiber must carry a **finite** `ℋ^{n−r}` measure—
otherwise the right-hand side is `∞`, the estimate is hollow, precisely the failure noted by `N2` in the one-step method.

* **`hausdorffNormalized_ne_top_iff`**: The normalization constant is positive and finite, so the normalized measure is finite iff the original measure is finite.
  This is the companion lemma for `hausdorffNormalized_eq_zero_iff` that has been proven.
* **`ae_hausdorffMeasure_fibre_ne_top`** (`R5`): if `v` is `C¹` and regular everywhere on the open set `O`,
  and `S` is measurable with compact `closure S` contained in `O`, then on **almost every level**
  `μH[n−r] (S ∩ v⁻¹(s)) ≠ ⊤`.

**This is a consequence of the regular coarea formula, not new analysis**: take weight `1`,
`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` says the integral of the fiber measure equals `∫ coareaJacobian`,
and the latter is finite on relative compact slices (the integrand is continuous on an open set, bounded on the compact closure, and `volume S < ∞`).
Functions with finite integrals are almost everywhere finite.

**Relative compactness is a true assumption; provide a counterexample instead of asserting.** Audit of `relative_compactness_necessary`:
The first coordinate functional on the plane is everywhere immersive, take `S = univ`, then all assumptions except compactness hold,
but each fiber is the entire line, with `ℋ^1` measure `∞`, the conclusion fails on **each** level (not just on a set of measure zero).

**Says nothing about sets outside the regular set**: `R5` Assume the differential is surjective throughout `O`, and the critical set of `v` lies outside its range—
this is precisely why the path still requires the remaining obligations.

## `R6`: Fubini on orthogonal decompositions of target spaces

New module `formalization/FunctionalInequalities/Analysis/TargetSplitFubini.lean`
(91 line, **only depends on Mathlib**, local import closure **1 modules**, no WIP).

**Purpose.** Two slicings yield "almost every `s ∈ W₁`, almost every `τ ∈ W₁ᗮ`",
while the conclusion requires "almost every `t ∈ W`". `R6` connects the two layers.

* **`measurableSet_splitPreimage`**: The preimage under the decomposition is measurable.
* **`measure_eq_zero_of_ae_slice_eq_zero`** (`R6`): If almost every first-coordinate slice of `N` has zero measure, then `N` has zero measure.

**It's an assembly task, but repository had none before.** Mathlib's
`LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_toLp`, `Measure.prod_apply`
are all in place, and this module merely connects them. The decomposition is given abstractly via an isometry `W ≃ₗᵢ WithLp 2 (W₁ × W₂)`, provided by the caller; the audit `orthogonal_decomposition` is instantiated using `Submodule.orthogonalDecomposition`—**the instance can be computed, so the abstract statement can be used directly**, which is exactly the form needed when performing decomposition along the image of a differential.

The audit also recorded the **opposite direction** (slices of zero-measure sets are almost everywhere zero-measure), to prevent treating `R6` as the easy half:
The route requires the direction proven within this module, both stemming from the same product measure machinery.

## What was not done in this round

* **No proof `R0`**: The rank-deficient part remained unchanged by a inch.
* **No proof `R7`** (layer-by-layer local assembly, estimate rows 450–600, **the only high-risk term**), `R8`–`R10`, `N1`, `N2`.
* **No proof of any coarea formula in the new setting**: `R5` is a consequence of the established regular formula, and the scope of applicable formulas has not been extended in any way.
* **No proof of any Sard theorem**; no assertion is made regarding the measure of the critical value set.
* No modification to any existing `.lean` (including `FunctionalInequalities.lean`, `RankDeficientRouteStatements.lean`, and `AreaFormulaRouteStatements.lean`); no hole migration; no expansion of certification or Blueprint `leanok` scope; no new compatible alias added; no weakening of established conclusions.
* **No commit, no push**, the real Git index remained unchanged.

## Next step

Only **`R7`** (layered local assembly) stands between `R0`, followed by `R8` (local to global) and `R9` (consumer).
`R7` remains the only high-risk item: it must perform an approximation patch on `u` itself while simultaneously supplying `P ∘ u` and `Q ∘ u`, and can only take neighborhoods from points on the layer, with constants required to be consistent across patches.

## Verification

* Two new modules and two new clients compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The two clients collectively produce **14 axiom reports** (`R5` 8, `R6` 6), using only
  `propext`, `Classical.choice`, `Quot.sound`.
* Re-running all **45 existing audit clients** plus the two new clients, a total of **47**, all pass strictly, with 0 failures;
  the axiom report consists of 618 entries, of which 12 are `sorryAx` still entirely within the four clients intentionally reporting unresolved WIP results.
* Each of the three WIPs is compiled in practice, with direct proof holes **1/2/5, total 8**, unchanged; `research/check_ledger.py` issues **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` pass; the evidence JSON is
  `research/explorations/2026-09-17-fibre-finite-fubini.json`,
  finally verified and saved as `build/audit/fibre-finite-fubini/final-snapshot.json`.
