# 2026-09-11 — Prompt for proof session: replace the sorry placeholders in `KLS/WIP/RelativePerimeter.lean` and `Energy/WIP/Cheeger.lean` with proofs

The following two prompts can be directly copied to another model/session. The first segment is the obligation of today's `lem:relative-perimeter-smoothing` skeleton; the second segment is the obligation of today's `thm:smooth-gradient-relaxation-two-cheeger` skeleton that can be proven using existing inputs.

---

## Prompt A: `lem:relative-perimeter-smoothing`

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/)

Task: Fill in the sorry in formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean. This file is the statement skeleton for the Blueprint node lem:relative-perimeter-smoothing (formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex, "Relative perimeter without carrier-boundary charges" section); design and sentence-by-sentence alignment are specified in research/decisions/2026-09-11-relative-perimeter-smoothing-statement.md. First read these two files and the target .lean module documentation.

Rules:
1. Do not alter any statement (type) of theorem/def. If a statement is confirmed to be false or unprovable, do not change it: in the report, provide a counterexample/barrier and retain sorry.
   It is allowed to add private auxiliary lemmas within the same file, and imports are allowed.
2. Naming follows research/naming.md (short names without namespace collision; auxiliary lemmas are private).
3. Work only within this WIP file. Do not add it to formalization/FunctionalInequalities.lean, lakefile's Solutions root,
   research/a-series/ledger.yaml, research/check_blueprint.py, research/tasks.json, Blueprint \lean{}/\leanok.
   do not git commit, do not git push. Decisions/exploration records are only appended (new research/decisions/2026-09-1X-relative-perimeter-smoothing-proofs.md).
4. Compilation command (in formalization/):
     lake env lean FunctionalInequalities/KLS/WIP/RelativePerimeter.lean
   Goal: no errors; filled declarations no longer show "declaration uses 'sorry"'; no unusedSectionVars or other warnings
   (unused section variables are marked with `omit ... in`, needed ones with `include ... in`). After completion, use
     lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/RelativePerimeter.lean
   and for each completed top-level theorem, run #print axioms; only propext / Classical.choice / Quot.sound are allowed.
5. Syntax hints: `∞` (ContDiff order) requires `open scoped ContDiff`; `push_neg` is deprecated, use `push Not` or `not_le.mp`;
   `μH[d]` is a scoped notation under `open MeasureTheory`; Hausdorff measure scaling lemma requires `0 ≤ d`, `finrank = 0` is handled separately (boundary is empty).

Do it in the following order, starting with the easier ones; if stuck, leave a sorry and specify the bottleneck.

Layer one (pure Mathlib, should be completed entirely)
- SmoothDomain.empty / SmoothDomain.univ has exists_defining: `frontier_empty`, `frontier_univ`, under the condition that the premise is empty, `simp`.
- SmoothDomain.measurableSet: `U.isOpen.measurableSet`.
- relativePerimeter_eq_zero_of_frontier_eq_empty: `h ▸ Set.empty_inter`, `Measure.restrict_empty`, `lintegral_zero_measure`.
- SmoothDomain.frontier_inter_eq: ⊆: y ∈ frontier ∩ W, if φ_y < 0, then y ∈ U ∩ W open set, contradicting y ∉ interior;
  If φ y > 0 then on the neighborhood φ > 0 (continuous), contradicting y ∈ closure U. ⊇: φ y = 0, fderiv ≠ 0 for direction v such that fderiv φ y v < 0
  (Take v = −(fderiv φ y).symm direction or use `ContinuousLinearMap.exists_ne_zero`), along y + t v using `HasFDerivAt`
  First-order expansion (`hasFDerivAt_iff_isLittleO` or `HasFDerivAt.lim`) yields φ < 0 (∈ U) when t > 0, and φ > 0 (∉ U) when t < 0,
  Hence y ∈ closure U and y ∉ interior U.
- SmoothDomain.homothety's isOpen / exists_defining: the homothety `AffineMap.homothety a c` (c ≠ 0) is a homeomorphism:
  `AffineEquiv.homothetyUnitsMulHom a (Units.mk0 c hc)` For AffineEquiv, continuity `AffineMap.homothety_continuous`
  (or written as `x ↦ c • (x − a) + a` using `Homeomorph.smulOfNeZero`, `Homeomorph.addRight`). Image of open sets: `Homeomorph.isOpenMap`.
  Define a function: let W' = h'' W, φ' = φ ∘ h.symm (`ContDiff.comp` and the affine mapping's `contDiff`), fderiv uses the chain rule
  The derivatives of `fderiv_comp` and `(h.symm)` are invertible.
- SmoothDomain.indicator_homothety: `Set.indicator_apply`, x ∈ h '' U ↔ h⁻¹ x ∈ U (`AffineEquiv.image_eq_preimage`
  or `Set.mem_image_equiv`, the inverse of `AffineMap.homothety` is a homothety with scale factor c⁻¹ (`AffineMap.homothety_mul`, `homothety_one`).
- IsBorellDensity.le_rpow_mul_of_combination: from `h.logConcave x b s hs₀ hs₁` (note the parameter order of the field and t•x + (1−t)•y form)
  Get ρ x ^ s * ρ b ^ (1−s) ≤ ρ y. If ρ x = 0 trivially. Otherwise ρ x ^ s ≤ ρ y / b₀^{1−s}, raise both sides to the 1/sth power:
  `Real.rpow_le_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.div_rpow`, then ρ y^{1/s} = ρ y · ρ y^{(1−s)/s}
  ≤ ρ y · M^((1−s)/s) (`Real.rpow_le_rpow_left_iff`/`Real.rpow_le_rpow`, using hM y). All bases non-negative (`h.nonneg`).
- RelativePerimeter.tendsto_indicator_homothety: `tendsto_lintegral_of_dominated_convergence` is controlled by a constant 1
  (`ν` is finite); pointwise, for x ∈ U, `AffineMap.homothety a c x → x` (c → 1, `Continuous.tendsto`,
  `AffineMap.homothety_apply`, `one_smul`), open set ⇒ eventually in U, difference is 0; x ∉ closure U similarly eventually not in U;
  frontier is excluded using `hfr` (form: `ae` `compl_mem_ae_iff.mpr hfr`).

Layer two (using existing repositories input + Mathlib, should be able to complete)
- SmoothDomain.hausdorff_frontier_homothety: homeomorphism preserves boundary `Homeomorph.image_frontier` (Topology/Homeomorph/Defs.lean:315), then `MeasureTheory.Measure.hausdorffMeasure_homothety_image (hd : 0 ≤ d) a hc s`
  (Mathlib/MeasureTheory/Measure/Hausdorff.lean:1051, of the form `μH[d] (homothety x c '' s) = ‖c‖₊ ^ d • μH[d] s`).
  d = finrank − 1 < 0 if and only if finrank = 0: in this case `Subsingleton V` (`Module.finrank_zero_iff`), frontier is empty, and both sides 0.
- IsBorellDensity.exists_le: (i) Non-empty interior support: `h.convex_pos` gives {ρ > 0} convex; ν is a probability and ν = m.withDensity ρ,
  Thus m {ρ > 0} > 0; convex set Haar positive measure ⇒ interior non-empty (`Convex.interior_nonempty_iff_affineSpan_eq_top` and
  `MeasureTheory.Measure.addHaar_affineSubspace` (true affine subspace has zero measure)). (ii) Take a ∈ interior ν.support,
  closedBall a r ⊆ interior (`Metric.isOpen_iff`), `h.exists_bounds_of_isCompact (isCompact_closedBall a r)` gives b₀ > 0.
  (iii) For any x: z ∈ ball ((a+x)/2) (r/2) written as z = (1/2)•x + (1/2)•b, b ∈ ball a r,
  `h.logConcave x b (1/2)` Given ρ z ≥ √(ρ x · b₀); integral: 1 = ν univ ≥ ν(ball) = ∫_{ball} ρ dm ≥ √(ρ x b₀) m(ball(·, r/2))
  (`withDensity_apply`, `setLIntegral_mono`, `Metric.measure_ball_pos` (`IsAddHaarMeasure` implies `IsOpenPosMeasure`)), solve for ρ x ≤ 1/(b₀ m(ball 0 (r/2))²).
- SmoothDomain.mollifiedIndicator_contDiff_lipschitz_mem_Icc: regard `mollifiedIndicator` as a convolution
  `(φ.normed m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] 𝟙_U` (`MeasureTheory.convolution` unfolds to ∫ f (x − y) g y,
  Note that Mathlib's convention is `∫ t, L (f t) (g (x − t))`, requiring `convolution_flip`/`convolution_eq_swap` adjustments.
  Smooth: `HasCompactSupport.contDiff_convolution_left` and `φ.hasCompactSupport_normed`, `φ.contDiff_normed`,
  `𝟙_U` locally integrable (bounded measurable). Lipschitz: derivative = (∇η) ⋆ 𝟙_U, norm ≤ ∫‖∇η‖ dm (`HasCompactSupport.hasFDerivAt_convolution_left`)
  Again `lipschitzWith_of_nnnorm_fderiv_le`. [0,1]: `φ.nonneg_normed`, `φ.integral_normed`, `integral_mono`, the integral ≤ η(x−·).

Layer three (lacking infrastructure, doing one's best; if stuck, leave a sorry note and explain clearly)
- SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier and SmoothDomain.addHaar_frontier:
  Idea: by frontier_inter_eq, the boundary locally is {φ = 0} ∩ W, fderiv ≠ 0 ⇒ implicit function theorem (`HasStrictFDerivAt.implicitFunction`,
  Mathlib/Analysis/Calculus/Implicit.lean) write it as a C¹ image; the image is Lipschitz (`LipschitzOnWith`)
  `LipschitzOnWith.hausdorffMeasure_image_le` gives μH[n−1] (compact piece) ≤ K^{n−1} μH[n−1] (compact set in ℝ^{n−1}) < ∞
  (Requires `hausdorffMeasure_pi_real` or comparison between μH[n−1] and volume on EuclideanSpace; Haar null: image under product measure)
  Slice is a single point (`Measure.prod_apply` + `measure_singleton`). After compact covering and locally finite ⇒ use definition of `IsLocallyFiniteMeasure`.
- SmoothDomain.enorm_gradient_mollified_le (Gauss–Green theorem): For fixed x, ∇_x ∫ η(x−y) 𝚺_U(y) dy = ∫_U ∇η(x−y) dy
  = −∫_U div_y[η(x−y)] dy; cover U ∩ supp η(x−·) with finitely many defined neighborhoods and perform partition of unity, then on each image coordinate block use one-dimensional partial integration
  (along the normal coordinate, `intervalIntegral.integral_eq_sub_of_hasDerivAt`) together with Fubini, we obtain the boundary term ∫_{∂U} η(x−y) n(y) dH^{n−1};
  Take a norm. Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` only applies to boxes,
  Thus either perform a coordinate transformation to the box (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) in image coordinates,
  Either do a one-dimensional partial integration + Fubini. This is the heaviest duty of this node.
- RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le: Given the two previous statements, use enorm_gradient_mollified_le pointwise
  Let U' := U.homothety a (1/s), `lintegral_mono`, `lintegral_lintegral_swap` (Tonelli, requiring μH restricted to ∂U' to be σ-finite:
  By locally finite + second countable), for each y' ∈ ∂U' use `φ.integral_normed`-type ∫ η(x − y') dm(x) = 1 but with weight ρ x:
  When η(x−y') > 0, ‖x−y'‖ < φ.rOut, let y := a + s•(y'−a) ∈ ∂U (`indicator_homothety`/`hausdorff_frontier_homothety` of
  As described), b := a − (s/(1−s))•(x−y'), ‖b−a‖ < r (by hε), y = s•x + (1−s)•b (algebraically),
  `le_rpow_mul_of_combination` Given ρ x ≤ (M/b₀)^{(1−s)/s} ρ y; if y ∉ interior ν.support then ρ x = 0
  (x ∈ {ρ > 0} ⊆ ν.support by upper semicontinuous + `Measure.mem_support`-type argument, b ∈ interior, convex combination enters the interior:
  `Convex.combo_interior_closure_mem_interior`. Then change variables on ∂U' to ∂U: `lintegral_map` along the similar `MeasurableEquiv`
  + hausdorff_frontier_homothety, the factor (1/s)^{n−1} = s^{1−n} (`ENNReal.ofReal_rpow_of_pos`).
- RelativePerimeter.exists_smooth_recovery_sequence: Assembly. a, r, b₀ as in exists_le's (i)(ii); M from exists_le;
  Set s_j = 1 − 1/(j+2), ε_j such that s_j ε_j/(1−s_j) < r and ε_j → 0 (`ContDiffBump` uses `⟨rIn, rOut, …⟩`, for example rIn = ε/2, rOut = ε);
  u_j := (U.homothety a (1/s_j)⁻¹…).mollifiedIndicator φ_j m. Regularity: mollifiedIndicator_contDiff_lipschitz_mem_Icc.
  L¹: triangle inequality via v_{s_j}: ‖u_j − v_{s_j}‖_{L¹(ν)} → 0 using `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`
  (m-a.e. convergence) + ν ≪ m(`h.withDensity_eq ▸ withDensity_absolutelyContinuous`) + bounded convergence (dominated by 1,
  (`tendsto_lintegral_of_dominated_convergence`), note that here s is fixed while ε → 0, diagonal selection is required; ‖v_{s_j} − 𝟙_U‖ → 0 using
  tendsto_indicator_homothety (along c_j = 1/s_j → 1, `Tendsto.comp`) and indicator_homothety.
  limsup: `lintegral_enorm_gradient_mollified_homothety_le` term-by-term, right-hand coefficient
  `ENNReal.ofReal (s_j^{1−n} (M/b₀)^{(1−s_j)/s_j}) → ENNReal.ofReal 1 = 1` (`Real.rpow` continuous, `Real.rpow_zero`),
  `limsup_le_of_le`/`Filter.limsup_le_limsup` + `ENNReal.Tendsto.mul_const`.

Report format: one obligation per line: name | completed/not completed | key APIs involved | bottlenecks and required infrastructure if not completed. Finally provide the output summary for `lake env lean -DwarningAsError=true` and the result for `#print axioms`. Do not claim completion of uncompiled content.
```

---

## Prompt B: `thm:smooth-gradient-relaxation-two-cheeger` (only for provable layer)

```
Warehouse is the same. Task: fill in formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean with the 20 statements that can be proven using existing inputs;
also 6 statements (LocalSlope.relaxation_eq_asymptoticLipschitz, Cheeger.energy_eq_ofAsymptoticLipschitz,
SmoothGradient.relaxation_eq_localSlope, relaxation_eq_two_mul_cheeger, Intrinsic.energy_eq_two_mul_cheeger)
are open comparisons under singular measures (Ambrosio–Gigli–Savaré 2013 type), **do not modify**, keep sorry.
First read research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md: the "sorry obligation list" table
provides row numbers, statements, corresponding Blueprint sentences and suggested API; dependency order #1–#7, #14 → #8–#12, #16–#19 → #20, #21 → #25, #26.
Rules, compilation commands, report formats, and prompt A are the same (file path changed to Energy/WIP/Cheeger.lean; decide to record new
research/decisions/2026-09-1X-smooth-gradient-relaxation-two-cheeger-proofs.md).
key entry points: PreEnergy.sequentialRelaxation_comp_le, sequentialRelaxation_toAmbient_le,
lowerSemicontinuous_sequentialRelaxation, le_sequentialRelaxation_of_lowerSemicontinuous,
sequentialRelaxation_le_of_recovery_sequences (Energy/Relaxation/{Basic,LowerSemicontinuous}.lean);
Energy.LocalSlope.apply_eq_norm_gradient, energy_eq_lintegral_gradient, admissible_iff_memLp_gradient
 (Energy/LocalSlope/Gradient.lean); ContDiff.locallyLipschitz (Mathlib);
Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2 (B = ContinuousLinearMap.id);
KLS.LogConcave.intrinsic_absolutelyContinuous (KLS/LogConcave/AbsoluteContinuity.lean).
Refer to previously proven arguments: Energy.LipschitzGradient.localSlope_holds_of_relaxation (Poincare/LipschitzGradient/Comparison.lean)
and Energy.SmoothGradient.relaxation_eq_intrinsic_energy (Energy/SmoothGradient/Intrinsic/Comparison.lean).
```


---

## Note (late 2026-09-11): The statement corresponding to prompt A has been corrected

`KLS/WIP/RelativePerimeter.lean` uses normalized surface measure `relativePerimeter`
(`surfaceMeasure V`), the reference measure for `= ofReal (ω_{n−1}/2^{n−1}) • μH[n−1]`, `enorm_gradient_mollified_le`, `lintegral_enorm_gradient_mollified_homothety_le`, `exists_smooth_recovery_sequence` is fixed to `volume` (under assumption `IsBorellDensity ν volume ρ`), with new obligation `hausdorffNormalized_finrank_eq_volume`. See
[Statement record supplement](2026-09-11-relative-perimeter-smoothing-statement.md). The API hint for prompt A at the third level remains unchanged, but
the Gauss–Green inference now requires the standard normalized statement (`∇(η⋆𝟙_U)(x) = ∫_{∂U} η(x−y) n(y) dℋ^{n−1}_std(y)`, `n` outward normal),
and the local finiteness of `surfaceMeasure` in Tonelli's change of order is obtained via `isLocallyFiniteMeasure_hausdorff_frontier` through `smul`.
