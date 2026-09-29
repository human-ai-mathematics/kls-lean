# 2026-09-12 — `KLS/WIP/CheegerInfimum.lean`: Fill another sorry and fix two erroneous statements

Take over [2026-09-11's proof record](2026-09-11-relative-perimeter-cheeger-infimum-proofs.md) (in 25 item, 13 item has been proven,
12 item left `sorry` and clearly listed the bottlenecks). This round only modifies this one WIP file, no registration, no commit, no push.

## Result

`sorry` Reduced from 12 to **11**; file has no warnings under `-DwarningAsError=true`.

### 1. `constant_eq_minkowskiConstant_intrinsic` —— proven

The reason for leaving `sorry` in the previous round was "the steps along the bijection reindexing two `⨅`s were not yet completed, requiring a sequence of aligned four-layer binder `iInf` congruences, rather than a single Mathlib combinator". This round takes a different route to bypass this difficulty: **using preimages instead of images throughout**.

- Added private lemma `thickening_preimage_of_isometry`: surjective isometry implies `thickening r (f ⁻¹' B) = f ⁻¹' thickening r B`
  (`Metric.infEDist_image` + `Set.image_preimage_eq`). Using preimages instead of images avoids the extra burden of "whether the image is measurable".
- Added private lemma `measurePreserving_coordinateEquiv`:
  `MeasurePreserving (coordinateEquiv μ) (intrinsicMeasure μ) (carrierMeasure μ)`,
  obtained from `intrinsicMap = (coordinateEquiv μ).symm ∘ retraction` and `Measure.map_map`.
- Thus, for each measurable `B ⊆ affineSupport μ`, `minkowskiContent (intrinsicMeasure μ) (g ⁻¹' B) = boundaryContent μ B`
  and mass equality are pointwise modifications; the mutual dominance of two `⨅`s is written once each using `le_iInf` + `iInf_le_of_le`,
  taking `B' := g ⁻¹' B` and `B := g.symm ⁻¹' B'`, no combination of relabeling subtrees is needed.
- The `finrank = 0` branch yields `Subsingleton` from `Module.finrank_zero_iff`, then connects to the existing
  `minkowskiConstant_eq_top_of_subsingleton`.

Signature unchanged. `CompleteSpace E` After filling in the proof, it becomes an unused variable, handled in the same way as
`ae_conditionalFiber_logConcave`, with warnings eliminated by successive declarations of `set_option linter.unusedSectionVars false in`, rather than adding `omit` (adding `omit` would change the signature).

### 2. Two erroneous statements: supplement with a corrected version, retain the original statement unchanged

The two entries marked as "statement problem" in the previous round were not changed in type this round (those are records left for the owner to review),
but each was supplemented with a proven fixed version for downstream use:

| Original statement (still `sorry`) | Defect | Newly proven version |
|---|---|---|
| `distanceCutoff_eq_zero_of_notMem_thickening` | false at `B = ∅` | `distanceCutoff_eq_zero_of_notMem_thickening_of_nonempty` (with `B.Nonempty`) |
| `tendsto_distanceCutoff_indicator` | missing `MeasurableSet B` | `tendsto_distanceCutoff_indicator_of_measurableSet` (with `MeasurableSet B`) |

This round of independent verification checked the counterexample for the first statement and confirmed that the previous judgment was correct: `distanceCutoff B r x = max 0 (1 - infDist x B / r)`,
and by Mathlib's convention `Metric.infDist x ∅ = 0`, it follows that `distanceCutoff ∅ r x = 1`; meanwhile `thickening r ∅ = ∅`
makes the premise vacuously true, so the conclusion `1 = 0` is false. Additionally, it was confirmed that this lemma has **no usage points anywhere in the entire repository**, so in the future, if the owner decides to directly correct its type, no downstream impact will be caused.

Proof route for Clause 2: pointwise `‖w_r x − 1_B x‖ₑ ≤ (thickening r B \ B).indicator 1 x` (three branches: `x ∈ B`, `x ∈ thickening r B \ B`, `x ∉ thickening r B`; the third branch is exactly the patched version added above), integrate to get `≤ ν(thickening r B) − ν B`; then by `Metric.closure_eq_iInter_thickening` and `tendsto_measure_iInter_atTop` along radius `1/(n+1)` with upper semicontinuity, combined with `hcl` to squeeze it down to 0, finally `ENNReal.tendsto_nhds_zero` + squeezing.

## The remaining 11 items and critical points

Maintain the previous round's judgment; no bypassable issues were found during this round of review:

- Missing Mathlib theory: `ae_exists_superlevel` (general dimension Sard), `lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (coarea formula), `KLS.hausdorffNormalized_finrank_eq_volume` (isodiametric inequality).
- Requires large-scale analysis work: `lintegral_enorm_gradient_distanceCutoff_le` (Rademacher + gradient on level sets a.e. zero), `exists_smooth_approximation_lipschitz` (convergence of gradient integral after smoothing, not just bounds), `lintegral_minkowskiContent_superlevel_le` (ADG 2017 Lemma 3.2; note that a rough global Lipschitz estimate only yields `≤ K`, to obtain `≤ ∫‖∇u‖dν` a narrow-band argument for local Lipschitz constants is required).
- Pure downstream dependencies: `smoothConstant_mul_lintegral_min_superlevel_le`, `minkowskiConstant_mul_lintegral_min_superlevel_le`, `minkowskiConstant_le_smoothConstant`, `smoothConstant_le_minkowskiConstant`.
- Retain as defect records: the two original statements in the above table.

The other two WIP files remain unchanged in this round: `KLS/WIP/RelativePerimeter.lean` (5 items, stalled at the local finiteness of the area measure on C¹ hypersurfaces and the Gauss–Green formula), `Energy/WIP/Cheeger.lean` (5 items, reduced to 2 items of singular measures under the AGS-type open comparison).

## Check

`lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/CheegerInfimum.lean`: No output except for 11 item `declaration uses 'sorry'`. This module is not included in aggregated imports and does not affect `lake build` or any certification.

## Supplement (same day, owner's instruction): Two defective statements are directly corrected and false propositions are no longer retained

The owner explicitly requires that the repository not retain false propositions, thus revoking the previous handling of "the original statement is retained as is" and instead adopting a **direct correction of type**:

- `distanceCutoff_eq_zero_of_notMem_thickening`: Add `(hB : B.Nonempty)`, the proof is the original patched version, `sorry` is eliminated.
- `tendsto_distanceCutoff_indicator`: Add `(hBm : MeasurableSet B)`, the proof is the original patched version, `sorry` is eliminated.

The two temporary versions with suffixes (`..._of_nonempty`, `..._of_measurableSet`) are subsequently deleted, and the sole reference point inside the file is updated to point to the original name.
Before the change, it was confirmed that neither of these two has any external usage points throughout the entire repository, and `KLS/WIP/CheegerInfimum.lean` is not imported by any module, is not included in any aggregated imports, and is not present in the lakefile `Solutions`, ledger, `CERTIFICATES`, or Blueprint `\lean{}`, thus the type change does not affect any certification.

Counterexamples were already machine-verified in independent Lean files (`B = ∅`, `r = 1`, `x = 0`: the premise due to `Metric.thickening 1 ∅ = ∅` holds, while `Metric.infDist 0 ∅ = 0` yields `distanceCutoff ∅ 1 0 = 1`), not merely by inference judgment.

`sorry` reduced from 11 to **9**; no warnings in the file under `-DwarningAsError=true`.
Also verified the entire repository: no annotations indicating statement defects in `.lean` file (e.g., `STATEMENT ISSUE`),
decided that only two instances of previously recorded statement issues remain, both of which have been corrected.
