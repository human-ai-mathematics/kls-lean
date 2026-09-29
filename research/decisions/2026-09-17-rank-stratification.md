# Rank layers and kernel lemma: R1 and R2 for rank-deficient paths

2026-09-17. This round's **proof of new theorems**: the **`R1` (rank-deficient path obligations list) (rank stratification measurability + finite decomposition of critical sets)**
and **`R2` (core lemma)**, following the first two items in the main attack order recommended in the previous round.
**Only these two have been proven**; `R0`, `R3`–`R10`, `N1`, `N2` remain unproven,
the rank-deficient part of coarea dimension m is still open. This round **does not prove any coarea formula, any slice theorem, or any Sard theorem**.
No hole migration, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260917T044025.829812Z/report.json`: 10 gates, 215 local module kernel replay,
573 entries, snapshot
`f500b26955fdb2cd97ba613222e82b08a54fd44d66f8c2a88fdd974084a79058`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Correction of a factual error in the previous record

The previous round's (`2026-09-17-rank-deficient-route.md`) reason for "proving nothing in this round" was:
New library modules must be included in the aggregated import of `formalization/FunctionalInequalities.lean` to be defaultably built and covered.
And that would require modifying the existing `.lean`. This reason is wrong.
The `research/verify.py`'s `replay_sources` is computed from the **source tree** for build and kernel replay scope,
Its `build_replay_inputs` annotation original text is indeed
"Build the exact replay scope, **including modules outside default import closures**",
And build one by one using `lake build +Module…`. The existing `Analysis/Vector*.lean` over ten modules are also not included in the aggregated import,
Similarly covered by 215 replay gates.
So the new `Analysis/` module **does not need** to modify the aggregate import. In this round, adding the module accordingly, **without modifying `FunctionalInequalities.lean`**.

The previous round's decision record, probe JSON, and verification receipt are **not rewritten**; corrections are made based on this record, and are explicitly noted in the current round's new sections at `HANDOFF.md`, `research/verification.md`.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/RankStratification.lean`
(**Only depends on Mathlib**, local import closure **1 modules**, no WIP).

### `R2` Core Lemma (Pure Linear Algebra)

* **`ker_comp_eq_ker_of_finrank_range_eq`**: If `P.comp L` is surjective, and
  `finrank W₁ = finrank (range L)`, then `ker (P ∘ L) = ker L`.
  Proof: `range (P ∘ L) = P '' (range L)`, so the restriction of `P` to `range L` is surjective;
  the dimensions on both sides are equal, and in finite dimensions, surjectivity implies injectivity; thus `P (L z) = 0 ⟹ L z = 0`.
* **`apply_eq_zero_of_comp_apply_eq_zero`**: The route consumes directly in the form,
  `∀ z, P (L z) = 0 → L z = 0`—**on sheaves, the differential along the fiber direction of the regular part is zero**.

**The dimension assumption is necessary, and is used to provide counterexamples rather than assertions.** Audit of `rank_hypothesis_necessary`
Remove the dimension assumption: in the plane take `L = id`, `P =` first coordinate functionals, `P ∘ L` surjective onto `ℝ`,
but `rank L = 2 ≠ 1 = finrank ℝ`, the second basis vector lies in `ker (P ∘ L)` and not in `ker L`.
Thus `R2` is **not** a statement about the surjectivity of composition; it precisely asserts that `P` does not collapse any part of `range L`.

`R2` **Do not** use inner product, do not use measure, do not use completeness; as long as `V` and `W₁` are finite dimensional, `W` can be any normed space.

### `R1` Rank stratification

* **`setOf_rank_eq`**: `{f | rank f = r} = {f | r ≤ rank f} \ {f | r+1 ≤ rank f}`,
  The rank in finite dimensions is an integer.
* **`measurableSet_rank_fderiv_eq`**: The rank stratification of the `C¹` map is measurable.
  Mathlib's `isOpen_setOfPred_nat_le_rank` gives the rank's lower semicontinuity,
  Pull the difference of two open sets via the continuous derivative. **No measurable structure is required on the operator space,**
  The target space also does not need to be finite-dimensional (audit `stratum_measurable_without_target_finrank`).
* **`setOf_not_surjective_fderiv_eq_iUnion`**:
  {x | Du x is not a surjection} = ∪_{r < m} {x | rank(Du x) = r}, a finite union.
  **Without any regularity from `u`**, it is pointwise linear algebra.

## m = 1 rollback of the scalar case

Audit placeholder: `codimension_one_collapse` at `finrank W = 1`
{ x | Du x is not a surjection } = { x | Du x = 0 } —— the stratification reduces to one layer, and in the codimension-one layer, nothing was added in this round.
Thus `codimension_one_critical_slices` **derives** (not asserts) the still unproven `R0` in the `m = 1` case,
using the already proven `ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`.
**This does not close any part of the rank deficiency issue**: at `m = 1`, the rank deficiency part is empty, and what remains open is `m ≥ 2`.

## Boundary cases

* **Zero-dimensional target space**: Each map is surjective, the critical set is empty, and `⋃_{r<0}` is also empty (`zero_dimensional_target`). This is precisely why `R0` does not require the "positive codimension" assumption.
* **Zero-dimensional domain**: All ranks are zero (`zero_dimensional_domain`).
* **Hierarchical index exceeding the target space dimension**: The layer is empty (`stratum_empty_of_le`).
* **Degenerate instance of `R2`**: Under a zero-dimensional projection target space, the composite surjection holds, and the conclusion is vacuously true (`zero_map_zero_target`).
* No assumptions of finiteness, inner product, completeness, or measure enter `R2`.

## What was not done in this round

* **No proof `R0`**: The rank-deficient part (intermediate rank of `m ≥ 2`) remains unchanged.
* **No proof `R3`–`R10`, `N1`, `N2`**. Following the previous round's order, the next step is `R3` (approximate right inverse, pointwise and locally consistent), then the **non-regular point `R4`** (a small Lipschitz estimate on the fiber).
* **No proof of any coarea formula**, nor any improvement to the applicability range of the coarea for codimension m.
* **No proof of any Sard theorem**; no assertion is made regarding the measure of the critical **value** set.
* No modification to any existing `.lean` (including `FunctionalInequalities.lean` and `research/audits/RankDeficientRouteStatements.lean`, the latter continuing to **preserve original bytes**); no hole migration; no expansion of certificate or Blueprint `leanok` scope; no new compatible alias added; no weakening of established conclusions.
* **No commit, no push**, the real Git index remains unchanged.

## Route statement file

`research/audits/RankDeficientRouteStatements.lean` **Preserve original bytes**: It is the historical record of the route.
`R1` The two statements together with `R2`'s statement are verified by the new client
`research/audits/RankStratificationAudit.lean` **byte-for-byte replication and proof**
(`route_R1_measurable`, `route_R1_decomposition`, `route_R2`),
this is the existing agreement of this repository on "route obligations have been fulfilled".
This round also re-ran `AreaFormulaRouteStatements.lean`, **no new errors were found**, it too preserves original bytes.

## Verification

* The new module and new client have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **20 Axiom Report** of `research/audits/RankStratificationAudit.lean` only uses
  `propext`, `Classical.choice`, `Quot.sound`: 8 is the complete declaration of the new module,
  3 is a word-for-word fulfillment of the route statement, the rest are counterexamples to the necessity of core forms and dimension assumptions, four boundary cases,
  The target space does not require a strengthened finite-dimensional version, nor the two statements of `m = 1`.
* Retest all **42** existing audit client instances plus new clients, totaling **43**; all strictly passed, 0 failures;
  There are 578 axiom reports. As in the preceding round, all 12 containing `sorryAx` come from four clients that **deliberately** report unresolved WIP results.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-rank-stratification.json`,
  Final verification and save `build/audit/rank-stratification/final-snapshot.json`.
