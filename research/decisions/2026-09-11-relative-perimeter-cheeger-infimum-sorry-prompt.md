# 2026-09-11 — Prompt for proof session: replace the sorry placeholders in `KLS/WIP/CheegerInfimum.lean` with proofs

Copy the code block below to the proof session. Preliminary note: `KLS/WIP/RelativePerimeter.lean` has been corrected tonight in two statements (see [Smooth Lemma Record Addendum](2026-09-11-relative-perimeter-smoothing-statement.md), where 13 has been proven unaffected; the 0-level of this prompt currently handles the new obligations of the file.

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/)

Environment note: This machine was updated today with Command Line Tools (only arm64), and the ~/.elan lake is x86_64, causing git operations through lake to fail and delete .lake/packages/checkdecls. Before running any lake command, place a directory containing a wrapper script named git at the front of PATH. The script content:
    #!/bin/sh
    export GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core
    export GIT_TEMPLATE_DIR=/Library/Developer/CommandLineTools/usr/share/git-core/templates
    exec /Library/Developer/CommandLineTools/usr/bin/git "$@"
If .lake/packages/checkdecls is missing, the wrapped lake will automatically reclone according to manifest.

Task: Fill in sorry (in formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) for 25 entries, and add the 1 entry (hausdorffNormalized_finrank_eq_volume, see layer 0) to formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean.
CheegerInfimum is the statement skeleton of Blueprint lem:relative-perimeter-cheeger-infimum (formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex) and thm:klartag-density-frontend-identification (45 chapter) under the clause h_μ = h^{sm,rel}_ν; design and sentence-by-sentence alignment are specified in research/decisions/2026-09-11-relative-perimeter-cheeger-infimum-statement.md. First read these files and the target .lean module documentation.

Rules:
1. Do not alter any statement (type) of theorem/def. If a statement is confirmed false or unprovable, retain sorry and note a counterexample/obstacle in the report.
   Auxiliary lemmas with private and import are allowed.
2. Naming follows research/naming.md.
3. Work only within two WIP files. Do not add FunctionalInequalities.lean, lakefile Solutions root, research/a-series/ledger.yaml,
   research/check_blueprint.py, research/tasks.json, Blueprint \lean{}/\leanok. Do not git commit, do not git push.
   Decision records are only appended: create a new research/decisions/2026-09-1X-relative-perimeter-cheeger-infimum-proofs.md.
4. Compile (in formalization/ with PATH already including packaging git):
     lake build FunctionalInequalities.KLS.WIP.RelativePerimeter      # Import CheegerInfimum; after modifications, rebuild olean is required
     lake env lean FunctionalInequalities/KLS/WIP/CheegerInfimum.lean
   Goal: No errors, completed declarations have no "declaration uses 'sorry'", no unusedSectionVars or other warnings (using omit/include ... in).
   Closeout uses -DwarningAsError=true compilation, and for completed top-level theorems #print axioms, only propext / Classical.choice / Quot.sound are allowed.
5. Syntax: `∞` requires `open scoped ContDiff`; `∆` requires `open scoped symmDiff`; `μH[d]` requires `open MeasureTheory`; `volume` comes from
   `measureSpaceOfInnerProductSpace` (Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean); `push_neg` is deprecated and uses `push Not`.

Do it layer by layer, starting with easier problems; leave stuck points with a "sorry" and clearly specify the bottleneck.

Layer 0 (RelativePerimeter.lean new obligations; difficult, can be postponed)
- KLS.hausdorffNormalized_finrank_eq_volume: `(ω_n/2^n) • μH[n] = volume` on Euclidean V. This is the isodiametric inequality
  (Lebesgue measure of each set ≤ ω_n(diam/2)^n) plus the comparison between `μH[n]` and `volume` missing in Mathlib.
  Mathlib has `hausdorffMeasure_pi_real` (sup norm), `Measure.addHaar` uniqueness (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul` / `Measure.addHaarMeasure_unique`): first prove `μH[n]` is a translation-invariant locally finite positive measure ⇒ `μH[n] = c • volume`, then by `InnerProductSpace.volume_ball` (Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean) and the ball's `μH[n]` (this step requires the isodiametric inequality, which is absent in Mathlib) to determine c. If unable to proceed, leave as sorry, explicitly noting the missing isodiametric inequality.

Layer one (pure Mathlib, should be completed entirely)
- SmoothDomain.frontier_superlevel_subset: `frontier_subset_closure`, `closure_lt_subset_le` (`{t<u} ⊆ closure ⊆ {t ≤ u}`)
  With `interior` containing an open set `{t<u}` (`isOpen_lt continuous_const hu`): boundary points satisfy `t ≤ u x` and are not inside the open set ⇒ `u x = t`.
- minkowskiConstant_eq_top_of_subsingleton / smoothConstant_eq_top_of_subsingleton: on a one-point space `ν B ∈ {0,1}`
  (`Set.eq_empty_or_univ`/`Subsingleton.set_cases`), contradiction of premises, `iInf` empty ⇒ `⊤` (`iInf_eq_top`, `ENNReal.iInf_eq_top`).
- measure_closure_eq_of_minkowskiContent_ne_top: `closure B ⊆ thickening r B` (`self_subset_thickening`/`closure_subset_thickening`,
  r > 0 gives `ν(closure B) − ν B ≤ ν(B^r) − ν B`; if `ν(closure B) > ν B`, then the difference `δ > 0` makes `(ν(B^r) − ν B)/r ≥ δ/r → ⊤`,
  Contradicts `liminf ≠ ⊤` (`Filter.liminf_eq_top`/`le_liminf_of_le`, `ENNReal.div_eq_top`, `tendsto_inv_zero_atTop`).
- lintegral_measure_symmDiff_superlevel: for `x` fixed, `{t ∈ (0,1) : x ∈ {t<u} ∆ B}` is `Ioo 0 1 ∩ Ico (u x) 1` (x ∈ B)
  Or `Ioo 0 (u x)` (x ∉ B), one-dimensional length is `|u x − 𝟙_B x|`; using `lintegral_lintegral_swap` (measurability: `measurableSet_lt`,
  `MeasurableSet.symmDiff`)certifies `∫⁻ t, ν(...) = ∫⁻ t ∫⁻ x 𝟙 = ∫⁻ x ∫⁻ t 𝟙`, then `Real.volume_Ioo`/[`Real.volume_Ico`],
  `Real.enorm_eq_ofReal_abs`.
- min_measure_le_add_measure_symmDiff: `ν A ≤ ν B + ν(A ∆ B)` (`measure_le_measure_union_symmDiff`?: using `A ⊆ B ∪ (A ∆ B)` +
  (`measure_union_le`) with symmetric forms, then `min_le_min`, `tsub_le_iff_right`, note that in ENNReal `1 − ν A`.
- tendsto_lintegral_min_superlevel: by the previous lemma, pointwise `t` has `|min(ν{u_j>t}) − min(ν B)| ≤ ν({u_j>t} ∆ B)`, then integral yields
  `lintegral_measure_symmDiff_superlevel` the difference between the two sides ≤ `∫⁻ ‖u_j − 𝟙_B‖ₑ → 0`; `ENNReal.Tendsto` by squeezing
  (ε-form of `tendsto_of_tendsto_of_tendsto_of_le_of_le'` or `ENNReal.tendsto_nhds`). Note that `∫⁻ t in Ioo 0 1, min(...)` ≤ 1 is finite.
- distanceCutoff_mem_Icc: `le_max_left`, `max_le`, `Metric.infDist_nonneg`, `div_nonneg`.
- lipschitzWith_distanceCutoff: `Metric.lipschitz_infDist_pt` (constant 1), `LipschitzWith.const_max`/[`LipschitzWith.max_const`],
  `LipschitzWith.const_sub`, `LipschitzWith.const_mul`/`div` combination; constant `Real.toNNReal r⁻¹`.
- distanceCutoff_eq_one_of_mem_closure: `Metric.mem_closure_iff_infDist_zero hB`, `div_zero`.
- distanceCutoff_eq_zero_of_notMem_thickening: `Metric.mem_thickening_iff_infDist_lt` (requires B to be non-empty; when empty, `thickening r ∅ = ∅`,
  `infDist x ∅ = 0`, is the conclusion false? —— Check: when B = ∅, `distanceCutoff ∅ r x = max 0 (1 − 0) = 1 ≠ 0`, while `x ∉ thickening r ∅` holds.
  **The statement is false when B = ∅**: It was reported that, leave sorry; or suggest adding a premise `hB : B.Nonempty` (do not modify the statement on your own).
- tendsto_distanceCutoff_indicator: `tendsto_lintegral_filter_of_dominated_convergence` (dominated by 1, `𝓝[>] 0` countably generated),
  Pointwise: `x ∈ closure B` ⇒ value constantly 1; `x ∉ closure B` ⇒ `infDist x B > 0` (`Metric.infDist_pos_iff_notMem_closure hB`),
  `r < infDist` time value 0; `hcl` reduces `closure B \ B` to `ν`-zero measure (`measure_diff_null`/[`ae`]).
- constant_eq_minkowskiConstant_intrinsic: expands `KLS.Isoperimetry.constant`'s `if`: `finrank = 0` ↔ direction space `Subsingleton`
  ↔ `minkowskiConstant = ⊤` (zero-dimensional lemma); otherwise change variables in `⨅`: `B ↦ intrinsicMap μ '' B` (or use the `retraction`/`coordinateEquiv`
  (`AffineIsometryEquiv`), `carrierMeasure μ = intrinsicMeasure μ` pushed forward along isometries ((`Probability.measurePreserving_intrinsicMap`),
  `Probability.coe_retraction_ae`), isometry preserves `thickening` (`IsometryEquiv.image_thickening` or `Metric.thickening` of `infDist`
  Characterizes + `Isometry.infDist_image`?), `boundaryContent` and `minkowskiContent` term by term equal. This is the longest statement in this layer.

Layer two (Mathlib + repository input, should be able to complete)
- lintegral_enorm_gradient_distanceCutoff_le: Rademacher `LipschitzWith.ae_differentiableAt` (Mathlib/Analysis/Calculus/Rademacher.lean)
  For `m`, transferred via `hac` to `ν`-a.e; on the open set `thickening r B \ closure B`, `‖∇w‖ ≤ 1/r`
  (`LipschitzWith.norm_fderiv_le`/`norm_gradient_le_of_lipschitz`, repository `Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz`);
  On the open set `(closure B)ᶜ ∩ (thickening r B)ᶜ` (value constantly 0) and `interior (closure B)` (value constantly 1), `∇w = 0`; the remainder
  `frontier (closure B) ∪ frontier (thickening r B)` On top, "the gradient of a Lipschitz function on a level set a.e is zero":
  Available `w` on `{w = 1}` a.e. the derivative at a differentiable point is 0 (if the point x ∈ {w=c} is a density point of the set, then ∇w x = 0; Lebesgue density theorem)
  (`Besicovitch.ae_tendsto_measure_inter_div`) or `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`; or bypass:
  By `lintegral_mono` + block `lintegral_union`, handle the contributions outside `thickening r B \ closure B` according to a.e. set them to zero.
- exists_smooth_approximation_lipschitz: `u_j := LipschitzApproximation.mollify m (radius j) w`
   (FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean: `contDiff_mollify`, `lipschitzWith_mollify`,
  `mollify_le`/`le_mollify` gives `[0,1]` and `norm_mollify_sub_le` uniform convergence ⇒ `L¹(ν)` convergence); gradient: `∇(mollify) = mollify(∇w)`
  By `Energy.Euclidean.WeakDerivative.integral_mul_inner_gradient` (Lipschitz partial integration) or directly differentiating `mollify_apply`
  + `hasFDerivAt_kernel`; `mollify(∇w) → ∇w` m-a.e. ( `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` or
  (Lebesgue point argument), bounded `K`, `ν` finite ⇒ `tendsto_lintegral_of_dominated_convergence`.
- lintegral_minkowskiContent_superlevel_le (ADG 2017 Lemma 3.2): for `r > 0`, `x ∈ thickening r {u ≥ t}` ⇒ ∃ y, `u y ≥ t`,
  `dist x y < r` ⇒ `u x ≥ t − r·Lip_{B(x,r)}(u)`; Fubini: `∫ (ν({u≥t}^r) − ν({u≥t})) dt ≤ ∫ ν{t − r L_r(x) ≤ u < t} dt
  = ∫ r L_r(x) dν(x), where L_r(x) = sup_{B(x,r)} ‖∇u‖` (`C¹ ⇒ continuous ⇒ L_r → ‖∇u‖ pointwise decreasing, monotonically convergent
  (`lintegral_tendsto_of_tendsto_of_antitone`); then exchange the integral and `liminf` using Fatou `lintegral_liminf_le`.
- minkowskiConstant_mul_lintegral_min_superlevel_le: `{u>t} ⊆ {u≥t}`, `ν{u = t} = 0` except countably many `t`
  (`Measure.countable_meas_level_set_pos`/`Measure.finite_meas_level_set_pos`) ⇒ both a.e. same measure; for each `t` there is `0<ν<1` when
  `minkowskiConstant ν ≤ ν⁺({u≥t})/min(...)` (`iInf_le`), multiply back, `lintegral_mono` followed by the previous one.

Layer 3 (lacking infrastructure, best effort)
- SmoothDomain.ae_exists_superlevel (Sard): for `t` regular values (`∀ x, u x = t → fderiv ℝ u x ≠ 0`), `U := {t<u}` is open,
  define function `φ := u − t`, `W := {x | fderiv ℝ u x ≠ 0}` (open, `ContDiff.continuous_fderiv`), `frontier_superlevel_subset` on boundary points ∈ `{u = t} ⊆ W`, `{t<u} ∩ W = {φ<0} ∩ W` is obvious. The remaining "critical value set `u '' {fderiv = 0}` has Lebesgue measure zero" is Sard; Mathlib only has the same-dimensional version `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (Mathlib/MeasureTheory/Function/Jacobian.lean).
  `n = 1` can be used directly; generally `n` requires Sard's theorem (`C^n` case), Mathlib lacks this—leave sorry to indicate.
- lintegral_enorm_gradient_mul_eq_lintegral_levelSet (coarea): Mathlib has the area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (same dimension), lacks coarea. Local route: on an open subset of `‖∇u‖ ≠ 0`, use implicit function to locally straighten `u` into coordinate projection (`HasStrictFDerivAt.implicitFunction`), area formula + Fubini yields local coarea; on `{∇u = 0}`, left side is 0, right side by Sard is 0. This is the heaviest obligation of this node.
- smoothConstant_mul_lintegral_min_superlevel_le: given the two above: coarea takes `g := ofReal ∘ ρ` (`hρ.withDensity_eq` transforms `∫‖∇u‖dν` into `∫‖∇u‖ ρ dvolume`), for a.e. `t`: `{t<u}` is a smooth region (Sard), `frontier ⊆ {u=t}` (`frontier_superlevel_subset`) ⇒ `relativePerimeter ρ Ω {t<u} ≤ ∫_{u=t} ρ dsurfaceMeasure`; when `0<ν{t<u}<1`, `smoothConstant ≤ P/min` (`iInf_le`), otherwise `min = 0`; `lintegral_mono_ae` + `ENNReal.mul_le_of_le_div'`.

Layer 4 (Assembly)
- minkowskiConstant_le_smoothConstant: for each selectable `U`: `RelativePerimeter.exists_smooth_recovery_sequence hρ U hU`
  Given `u_j`; `minkowskiConstant_mul_lintegral_min_superlevel_le` for each `u_j` (using `ContDiff ℝ ∞ → ℝ 1` with `.of_le le_top`);
  `tendsto_lintegral_min_superlevel` is given as approaching `h_M · min(ν U)` from the left; approaching `limsup ≤ P_ρ(U)` from the right; `le_of_tendsto_of_tendsto'` +
  `ENNReal.Tendsto.const_mul`; then `le_iInf` + `ENNReal.le_div_iff_mul_le` (for `min ≠ 0`, `≠ ⊤`). If `P_ρ(U) = ⊤` is trivial.
- smoothConstant_le_minkowskiConstant: for each Borel selectable `B` (where `minkowskiContent ν B = ⊤` is trivial): `measure_closure_eq_...`,
  take `r_j → 0` to realize `liminf` (either `Filter.exists_seq_tendsto_liminf`? or `Filter.liminf`'s `frequently` characterization +
  `exists_seq_tendsto_sInf`), `w_j := distanceCutoff B r_j`, `lintegral_enorm_gradient_distanceCutoff_le`
  (`hac := hρ.withDensity_eq ▸ withDensity_absolutelyContinuous`), `exists_smooth_approximation_lipschitz` yields a smooth substitute
  `u_{j,k}`, diagonalization; `smoothConstant_mul_lintegral_min_superlevel_le`; `tendsto_distanceCutoff_indicator` +
  `tendsto_lintegral_min_superlevel`; `hB.Nonempty` is derived from `0 < ν B`.
- minkowskiConstant_eq_smoothConstant: `le_antisymm`.
- constant_eq_smoothConstant_intrinsic: `constant_eq_minkowskiConstant_intrinsic` + `minkowskiConstant_eq_smoothConstant hρ`
  on `V := (affineSupport μ).direction` (examples: `Submodule` with `InnerProductSpace`, `Subtype.borelSpace`, etc., `hμ` is only for documentation consistency,
  may `omit`; if linter reports unused, must add `include hμ in` before the statement—do not modify types).
- inverseScale_eq_inv_smoothConstant_intrinsic: `unfold inverseScale` + from the previous.

Report format: one obligation per line: name | completed/not completed | key API | bottleneck. Provide `-DwarningAsError=true` compilation summary and `#print axioms` result.
Do not claim that uncompiled content is completed. If a statement is found to be false (e.g. `distanceCutoff_eq_zero_of_notMem_thickening`'s `B = ∅`), list it separately as "statement issue".
```
