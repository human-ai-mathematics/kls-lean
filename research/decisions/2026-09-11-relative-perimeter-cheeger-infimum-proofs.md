# 2026-09-11 — `lem:relative-perimeter-cheeger-infimum`: Proof progress (appendix-style record)

## Decision

- In two WIP files (`formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean`,
   (`formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean`) fill in sorry, do not modify any
  The type signature of `theorem`/`def`, no registration, no commit, no pushing, no modification of shared files.
- `CheegerInfimum.lean` Originally 25 `sorry` obligations: **13 proved** (including 3 pure gluing/assembly lemmas, whose proofs themselves
  `sorry`-free, but the transitive dependency still carries `sorry` from the downstream lemma (see below); **12 remains `sorry`**, all have been annotated in the code
  Clarify the bottleneck. `RelativePerimeter.lean` The newly added 1 item `hausdorffNormalized_finrank_eq_volume` remains `sorry`
  (Already annotated with notes on bottlenecks), the rest of the file remains unchanged.
- No proof was found that needed to be forged/evaded the intent of the statement in order to eliminate `sorry`; two instances where the statement might be incorrect or have gaps (see the section "Statement Issues")
  Following rule 1, retain `sorry` and record the counterexample here, without unilaterally changing the type.

## Per-step state

### `CheegerInfimum.lean` (25 axiom)

| Name | Status | Key API | Bottleneck |
|---|---|---|---|
| `SmoothDomain.ae_exists_superlevel` | incomplete | — | Sard theorem: Mathlib has only the same-dimensional `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (`Jacobian.lean`), no general-dimensional Sard (critical value set has zero measure). Leave `sorry`, specify missing infrastructure. |
| `SmoothDomain.frontier_superlevel_subset` | **Completed** | `frontier_subset_closure`, `closure_lt_subset_le`, `isOpen_lt` | — |
| `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (weighted coarea formula) | incomplete | — | Mathlib only has area formulas for same-dimensional cases, lacking a coarea formula (the route using local straightening + implicit function theorem has not been implemented; see `{∇u≠0}`). Left as `sorry`. |
| `minkowskiConstant_eq_top_of_subsingleton` | **Completed** | `iInf_eq_top`, `iInf_pos`, `iInf_neg`, `measure_univ` | — |
| `smoothConstant_eq_top_of_subsingleton` | **Completed** | Same as above | — |
| `measure_closure_eq_of_minkowskiContent_ne_top` | **Completed** | `Metric.closure_subset_thickening`, `tsub_le_tsub_right`, `ENNReal.tendsto_ofReal_nhds_top`, `tendsto_inv_nhdsGT_zero`, `ENNReal.Tendsto.const_mul`, `liminf_le_liminf`, `Filter.Tendsto.liminf_eq` | — |
| `lintegral_measure_symmDiff_superlevel` | **Completed** | `lintegral_lintegral_swap` (Tonelli), `lintegral_indicator_one`, `Set.Ioo_inter_Iio`, `measure_sdiff`, `ENNReal.ofReal_sub`, `Real.enorm_eq_ofReal_abs` | Longest pure Mathlib proof; the core is to exchange t-integral and x-integral via the product measure Fubini, then compute the length of each interval pointwise. |
| `min_measure_le_add_measure_symmDiff` | **Completed** | `measure_union_le`, `measure_compl`, `compl_symmDiff_compl` | Private auxiliary `hbasic` (`ν C ≤ ν D + ν(C∆D)`) used once for `(A,B)` and once for `(Aᶜ,Bᶜ)`, then split according to the two branches of `min`. |
| `tendsto_lintegral_min_superlevel` | **Completed** | `Antitone.measurable` (reduces the measurability of `t ↦ ν{t<u_j}` to its monotonicity), `Measurable.min`, `setLIntegral_mono'`, `lintegral_add_left`, `ENNReal.Tendsto.sub`, `Tendsto.const_add`, `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (squeezing) | Must prove that `min(ν{t<u_j x})(...)` is measurable with respect to `t` using its anti-monotonicity; otherwise `lintegral_add_left` cannot extract this term. |
| `distanceCutoff_mem_Icc` | **Completed** | `le_max_left`, `max_le`, `Metric.infDist_nonneg` | — |
| `lipschitzWith_distanceCutoff` | **Completed** | `Metric.lipschitz_infDist_pt`, `abs_max_sub_max_le_abs`, `LipschitzWith.of_dist_le'` | Proved directly using the definition of `dist ≤ K*dist`, avoiding the need to find the combination of `LipschitzWith.const_sub`/`const_max`. |
| `distanceCutoff_eq_one_of_mem_closure` | **Completed** | `Metric.mem_closure_iff_infDist_zero` | — |
| `distanceCutoff_eq_zero_of_notMem_thickening` | **Incomplete (statement problem)** | — | **`B = ∅` the statement is false**, see below "statement problem". |
| `tendsto_distanceCutoff_indicator` | **Incomplete (statement/assumption issue)** | — | Lacks `MeasurableSet B` (or `NullMeasurableSet B ν`) premise, see below "statement issue". |
| `lintegral_enorm_gradient_distanceCutoff_le` | Incomplete | — | Needs Rademacher (`LipschitzWith.ae_differentiableAt`) and an argument that gradients vanish a.e. on level sets (no direct Mathlib lemma found; would need Lebesgue density points or a dedicated construction); not developed within the time available |
| `exists_smooth_approximation_lipschitz` | Incomplete | — | Needs the mollification operator in `Energy/Euclidean/LipschitzApproximation.lean`, a gradient/mollification interchange lemma, and uniform-continuity arguments; not developed within the time available |
| `smoothConstant_mul_lintegral_min_superlevel_le` | incomplete | — | depends on Sard (`ae_exists_superlevel`) and coarea formula (`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`), both of which are incomplete. |
| `lintegral_minkowskiContent_superlevel_le` (ADG 2017 Lemma 3.2) | incomplete | — | Requires an elementary but tedious argument for "thickened closed superlevel sets ⊆ narrow bands with locally Lipschitz constant control", together with monotone convergence/Fatou interchange of limit and integral; not expanded due to time constraints. |
| `minkowskiConstant_mul_lintegral_min_superlevel_le` | incomplete | — | depends on the previous one. |
| `minkowskiConstant_le_smoothConstant` | incomplete | — | depends on `RelativePerimeter.exists_smooth_recovery_sequence` (itself incomplete in `RelativePerimeter.lean`) and `minkowskiConstant_mul_lintegral_min_superlevel_le`; assembly itself (`limsup`/`le_iInf` operations) is also not expanded. |
| `smoothConstant_le_minkowskiConstant` | incomplete | — | depends on `lintegral_enorm_gradient_distanceCutoff_le`, `exists_smooth_approximation_lipschitz`, `smoothConstant_mul_lintegral_min_superlevel_le`, and requires handling diagonalization of `Filter.exists_seq_tendsto_liminf`; not expanded due to time constraints. |
| `minkowskiConstant_eq_smoothConstant` | **Completion (gluing)** | `le_antisymm` | The proof itself is pure gluing (`le_antisymm (minkowskiConstant_le_smoothConstant hρ) (smoothConstant_le_minkowskiConstant hρ)`), with no `sorry` appearing literally, but the two invoked lemmas are still `sorry`, thus `#print axioms` shows `sorryAx` (see below). |
| `constant_eq_minkowskiConstant_intrinsic` | Incomplete | `Probability.coordinateEquiv`, `Probability.intrinsicMap`, `AffineIsometryEquiv.toIsometryEquiv`, `EMetric.infEDist_image`, `Metric.mem_thickening_iff_infEDist_lt` | The mathematics is clear (see the long code comment: use the isometry `coordinateEquiv μ` to prove `e '' thickening r B' = thickening r (e '' B')`; use `ProbabilityMeasure.toMeasure_map` + `Measure.map_map` to prove `intrinsicMeasure μ = (carrierMeasure μ).map (coordinateEquiv μ).symm`; then reindex the four nested `⨅` in `constant`/`minkowskiConstant` along the bijection `B' ↦ coordinateEquiv μ '' B'`). However, no single Mathlib combinator was found to reindex four nested `⨅` along a bijection; the layers need to be handled individually, and the formalization was not completed within the time available |
| `constant_eq_smoothConstant_intrinsic` | **Completion (gluing)** | `rw [constant_eq_minkowskiConstant_intrinsic, minkowskiConstant_eq_smoothConstant hρ]` | Same as above, pure gluing, transitively dependent `sorryAx`. |
| `inverseScale_eq_inv_smoothConstant_intrinsic` | **Completion (gluing)** | `unfold inverseScale; rw [constant_eq_smoothConstant_intrinsic hμ hρ]` | Same as above, pure gluing, transitively dependent `sorryAx`. |

There are 13 genuine `sorry`-free (whose proof terms contain no `sorry`), of which 10 are "leaves" (neither the entity itself nor its call chain contains any `sorry`, and `#print axioms` only has `propext`/[`Classical.choice`]/`Quot.sound`), and 3 are composition lemmas (the lemma's own proof is `sorry`-free, but the other lemmas it references are `sorry`, hence `#print axioms` will display `sorryAx`).

### `RelativePerimeter.lean` (new 1 entries)

| Name | Status | Bottleneck |
|---|---|---|
| `KLS.hausdorffNormalized_finrank_eq_volume` | incomplete | requires the "isodiametric inequality" (each set of diameter `d` has Lebesgue measure `≤ ω_n (d/2)^n`, with equality achieved only by balls) to determine the proportion constant in Haar uniqueness; retrieval confirms that the identifiers `isodiametric`/`isoperimetric` do not exist in the current pinned Mathlib snapshot. Comments have been added in the code indicating critical points (including a sketch of the route to `Measure.addHaarMeasure_unique`/`InnerProductSpace.volume_ball`). |

## `-DwarningAsError=true` Compilation result

```
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/CheegerInfimum.lean
```

Output exactly 12 `error: declaration uses 'sorry'`, line numbers are
`87,112,448,462,472,485,500,512,520,533,540,566`, corresponds one-to-one with the 12 items marked "incomplete" in the above table; **no other
Warning/error** (`unusedSectionVars`, `unusedVariables`, etc. lemmas deprecated generated warnings during the sorry filling process have already
Cleanup: Added 10 at `omit [...] in`, replaced `Set.mem_setOf_eq`/`Set.mem_diff` with `Set.mem_ofPred_eq`/
`Set.mem_sdiff`, rename the two unused assumptions `hr`, `hμ` to `_hr`, `_hμ`).

`lake build FunctionalInequalities.KLS.WIP.RelativePerimeter` and
`lake build FunctionalInequalities.KLS.WIP.CheegerInfimum` (normal mode, without `-DwarningAsError`) both
`Build completed successfully`, respectively remaining 5 and 12 `declaration uses 'sorry'` warnings, with no other warnings.

## `#print axioms` Result

Execute the 13 sorry-free statements one by one using `#print axioms`:

- The following 10 statements only depend on `[propext, Classical.choice, Quot.sound]`:
  `SmoothDomain.frontier_superlevel_subset`,
  `Isoperimetry.minkowskiConstant_eq_top_of_subsingleton`,
  `Isoperimetry.smoothConstant_eq_top_of_subsingleton`,
  `Isoperimetry.measure_closure_eq_of_minkowskiContent_ne_top`,
  `Isoperimetry.lintegral_measure_symmDiff_superlevel`,
  `Isoperimetry.min_measure_le_add_measure_symmDiff`,
  `Isoperimetry.tendsto_lintegral_min_superlevel`,
  `Isoperimetry.distanceCutoff_mem_Icc`,
  `Isoperimetry.lipschitzWith_distanceCutoff`,
  `Isoperimetry.distanceCutoff_eq_one_of_mem_closure`.
- The following 3 statements (gluing lemma, proof terms themselves `sorry`-free) additionally depend on `sorryAx` (since they invoke still `sorry` versions of
  `minkowskiConstant_le_smoothConstant`, `smoothConstant_le_minkowskiConstant`,
  `constant_eq_minkowskiConstant_intrinsic`):
  `Isoperimetry.minkowskiConstant_eq_smoothConstant`,
  `Isoperimetry.constant_eq_smoothConstant_intrinsic`,
  `Isoperimetry.inverseScale_eq_inv_smoothConstant_intrinsic`.
  **These 3 statements should not be reported as "fully proved"**: their proof strategies are correct and the assembly is correct, but the entire theorem chain is only truly free of `sorry` when all three components `minkowskiConstant_le_smoothConstant`, `smoothConstant_le_minkowskiConstant`,
  `constant_eq_minkowskiConstant_intrinsic` are completed.

## Statement of the problem

1. **`distanceCutoff_eq_zero_of_notMem_thickening` is false when `B = ∅`.** Statement:
   `∀ B r (hr : 0 < r) x, x ∉ Metric.thickening r B → distanceCutoff B r x = 0`. Take `B = ∅`:
   `Metric.thickening r ∅ = ∅` (`Metric.thickening_empty`), so for any `x`, the premise
   `x ∉ Metric.thickening r ∅` is always true; but `Metric.infDist x ∅ = 0` (Mathlib's convention for the empty set `infDist`,
   `Metric.infDist_empty`), hence `distanceCutoff ∅ r x = max 0 (1 - 0/r) = max 0 1 = 1 ≠ 0`. The proposition holds for
   `B` non-empty (in this case, `x ∉ thickening r B ↔ r ≤ infDist x B`
   `Metric.mem_thickening_iff_infDist_lt` takes the contrapositive, directly yielding `1 - infDist x B / r ≤ 0`), but the statement lacks
   `B.Nonempty` premise, and rule 1 does not permit adding a premise to make it provable. `sorry` has been retained and a counterexample is explicitly written in the code.

2. **`tendsto_distanceCutoff_indicator` lacks the premise `MeasurableSet B` (or `NullMeasurableSet B ν`),
in general, it may not be provable.** This lemma requires that for each `r`, the integrand
`x ↦ ‖distanceCutoff B r x - B.indicator 1 x‖ₑ` is measurable (to apply theorem dominated convergence
`tendsto_lintegral_filter_of_dominated_convergence`), while `distanceCutoff B r` is continuous (hence Borel measurable), and `B.indicator 1` is generally not measurable when `B` is not Borel, and their difference is generally not measurable. A more fundamental issue: the proof relies on "`hcl : ν(closure B) = ν B` ⟹ `ν(closure B \ B) = 0`", but this step fails for non-measurable `B`—take a Vitali/Bernstein-type set `B ⊆ closure B` (for example, `closure B` is a closed ball, and `B` and `closure B \ B` are both non-measurable subsets with outer measure equal to `ν(closure B)`, a standard operation in the classical Bernstein set construction) such that `ν(closure B) = ν(B)` (outer measure) holds while `ν(closure B \ B)` simultaneously achieves full outer measure (`≠ 0`). The proposition holds for Borel (or `ν`-null completion measurable) sets `B`, but the statement does not include this premise. `sorry` has been retained and explained in the final report.

## Environment

Carry over the previous day's diagnosis of Command Line Tools / x86_64 lake and arm64 xcrun incompatibility issue; all `lake`/`lean` calls have a single `exec` `/Library/Developer/CommandLineTools/usr/bin/git` inserted before PATH and explicitly set the packaging script directory under `GIT_EXEC_PATH`/`GIT_TEMPLATE_DIR`, without modifying repository content.

## Not done / Future work

- Not registered into `research/tasks.json`, `research/a-series/ledger.yaml`; unchanged Blueprint's `\lean{}` / `\leanok`; not `git commit`, not `git push`; unchanged `FunctionalInequalities.lean`, `lakefile.toml`, `solutions/README.md`, etc. shared files.
- If anyone continues later: "reindexing nested `⨅` via bijection" in `constant_eq_minkowskiConstant_intrinsic` is the next most promising single point (once completed, `constant_eq_smoothConstant_intrinsic`, `inverseScale_eq_inv_smoothConstant_intrinsic` will only depend on `minkowskiConstant_eq_smoothConstant` chain). `lintegral_minkowskiContent_superlevel_le` (ADG Lemma 3.2) and Sard/coarea are the next three most labor-intensive nodes, each potentially requiring independent large-scale development.
