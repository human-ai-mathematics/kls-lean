# 2026-09-12 — Prompt for proof session: replace the sorry placeholders in `KLS/WIP/AnalyticPrerequisites.lean` with proofs

Copy the code block below to the proof session. Background: same day's [statement record](2026-09-12-relative-perimeter-prerequisites-statement.md)
Wrote the missing analytical assumptions for the relative perimeter chain as 17 statements independent of KLS; this prompt provides a four-layered route and API based on feasibility.
The statement itself must not be modified; if found false or unprovable, retain `sorry` and note it in the report.

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib submission
db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/).
The local elan and all Lean toolchain components are natively arm64; git operations via lake work normally and no git wrapper scripts are required.

Task: Fill in sorry (in formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean entry 17).
This file is an independent statement of missing analytical premises for the relative perimeter chain (Blueprint lem:relative-perimeter-smoothing, lem:relative-perimeter-cheeger-infimum): A isodiametric inequality (via Prékopa–Leindler / Brunn–Minkowski), B Lipschitz graphs of regular level sets and μH[n−1] locally finite, C Gauss–Green for smooth domains, D weighted coarea, E Sard. Design, sources, and feasibility assessment of each are given in research/decisions/2026-09-12-relative-perimeter-prerequisites-statement.md; first read it, the target .lean module documentation, and research/naming.md.

Initial repository materials:
- formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean: SmoothDomain, frontier_inter_eq,
  Proof of addHaar_frontier (monotonicity along the normal direction, reusable for outwardNormal_eq), mollifiedIndicator, and
  mollifiedIndicator_contDiff_lipschitz_mem_Icc (usage of convolution differentiation API). Note that its private lemmas
  (mollifiedIndicator_eq, etc.) cannot be referenced across files and must be re-proved as private in this file when needed.
- formalization/FunctionalInequalities/Probability/Line/BrunnMinkowski.lean: One-dimensional Brunn–Minkowski and Prékopa–Leindler (prekopaLeindler without boundedness assumptions), and the "regularity within compact subsets + iSup" pattern in le_volume_combination.
- formalization/FunctionalInequalities/Probability/HaarLine.lean: lineEquiv, exists_lintegral_line (Fubini along a line).
- formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean: norm_gradient_le_of_lipschitz,
  gradient_eq_of_hasFDerivAt, measurable_gradient, ae_differentiableAt_of_locallyLipschitz.

Rules:
1. Do not alter any statement (type) of theorem/def, including the bodies of the two def definitions. If a statement is confirmed to be false or unprovable, retain sorry and document a counterexample/obstacle in the report. Allow addition of private auxiliary lemmas and import; allow adding general non-private lemmas (naming following research/naming.md), but list them in the report.
2. Work only within this file. Do not modify RelativePerimeter.lean / CheegerInfimum.lean. Do not add FunctionalInequalities.lean, lakefile Solutions root, research/a-series/ledger.yaml, research/check_blueprint.py, research/tasks.json, Blueprint \lean{}/\leanok. Do not git commit, do not git push. Record decisions are only appended: new
   research/decisions/2026-09-1X-relative-perimeter-prerequisites-proofs.md.
3. Compile (in formalization/):
     lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites
     lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
  Goal: no errors; filled declarations have no "declaration uses 'sorry"'; no other warnings. Note: unusedSectionVars linter does not report on declarations containing sorry, so a new such warning may appear after each completion—handle it with `omit [...] in` (placed before the docstring) for no longer needed section instances, and use `include ... in` for needed ones; do not modify the statements for this. Closeout with
     lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
  and for each completed top-level theorem, run #print axioms, allowing only propext / Classical.choice / Quot.sound.
4. Syntax: `∞` requires `open scoped ContDiff`; `μH[d]` requires `open MeasureTheory`; `⟪x, y⟫` is the `inner ℝ x y` under `open scoped RealInnerProductSpace`; `S + T` and `t • S` require `open scoped Pointwise`; `volume` comes from measureSpaceOfInnerProductSpace; `LinearMap.ker` only accepts LinearMap, for fderiv write `(fderiv ℝ φ x).toLinearMap` (as in the file); `push_neg` has been deprecated in favor of `push Not`.

Do it layer by layer, starting with easier problems; leave stuck points with a "sorry" and clearly specify the bottleneck.

Layer one (given the same file, after other entries are assembly, or pure Mathlib; all should be completed)
- KLS.SmoothDomain.norm_outwardNormal: Expand outwardNormal, `dif_pos hx`; `(U.exists_defining x hx).choose_spec.choose_spec`
  Given the properties of W and φ, particularly `fderiv ℝ φ x ≠ 0` (x ∈ W); `gradient` and `fderiv` are mutual `toDual` images
  (`gradient_eq_toDual_symm_fderiv`? or use LipschitzApproximation.norm_gradient_eq_norm_fderiv) ⇒ `gradient φ x ≠ 0`;
  `norm_smul`, `norm_inv`, `norm_norm`, `inv_mul_cancel₀`.
- Analysis.ae_forall_fderiv_ne_zero ← sard: `ae_iff`; `{t | ¬ ∀ x, u x = t → Du x ≠ 0} = u '' {x | Du x = 0}`
  (`Set.ext`, `Set.mem_image`, `not_forall`/[`not_imp`]/`not_not`), then `measure_mono_null` + sard.
- Analysis.volume_le_ofReal_mul_hausdorffMeasure ← isodiametric: `Measure.hausdorffMeasure_apply` (`μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → Set X)
  (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ (_ : (t n).Nonempty), diam (t n) ^ d, diam is EMetric.diam).
  It suffices to prove `vol S ≤ ofReal(ω/2^n) * (⨅ ...)` for r = 1: for each cover `vol S ≤ ∑' vol (t n)` (`measure_iUnion_le` + `measure_mono`);
  Each `t n`: if `EMetric.diam (t n) = ⊤` then the item is ⊤ (n ≥ 1; n = 0 is handled separately, in which case `0^0 = 1`, V is a point, `vol S ≤ 1`).
  Otherwise `t n` is bounded (`Metric.isBounded_iff_ediam_ne_top`), `isodiametric` is given to `vol (t n) ≤ ofReal(ω (diam/2)^n)`,
  Again `Metric.diam = (EMetric.diam).toReal` (Definition `Metric.diam`) and `ENNReal.ofReal_rpow_of_nonneg`/`ENNReal.ofReal_pow`
  Change to `ofReal(ω/2^n) * EMetric.diam^n`; `ENNReal.tsum_mul_left`, `le_iInf`, `le_iSup_of_le`.
- Analysis.exists_hausdorffMeasure_levelSet_lt_top ← exists_lipschitzOnWith_levelSet_subset_image: take N, K, s, g;
  `measure_mono` to `g '' s`; `LipschitzOnWith.hausdorffMeasure_image_le hg (d := finrank − 1) hd` (requires `0 ≤ d`; when n = 0
  The premise `Dφ x ≠ 0` is impossible; first `rcases Nat.eq_zero_or_pos` gives `≤ K^d * μH[d] s`; `μH[d]` on `ker`:
  `finrank ℝ ker = n − 1` (`LinearMap.finrank_range_add_finrank_ker`, range is ⊤ because the nonzero functional is surjective onto ℝ:
  `LinearMap.range_eq_top`/`finrank_top`/`Module.finrank_self`), thus `μH[finrank ℝ ker]` is `IsAddHaarMeasure`
  (instance `isAddHaarMeasure_hausdorffMeasure`, requires an instance of MeasurableSpace/BorelSpace on ker: `Subtype.instMeasurableSpace`,
  `Subtype.borelSpace`, and `FiniteDimensional`, `SecondCountableTopology`——finite-dimensional normed spaces automatically have)
  Haar ⇒ `IsFiniteMeasureOnCompacts`, bounded set contained in a compact ball (`Bornology.IsBounded.subset_closedBall` + `isCompact_closedBall`) ⇒ finite.
  Align `(finrank ℝ V : ℝ) − 1` with `(finrank ℝ ker : ℝ)` using `Nat.cast_sub`/`push_cast`.
- Analysis.volume_rpow_add_le_volume_add_rpow ← volume_rpow_mul_le_volume_combination: standard homogenization. `a := vol S ^ (1/n)`,
  `b := vol T ^ (1/n)` (compact implies finite, `IsCompact.measure_lt_top`). If a = 0 or b = 0: `x + T ⊆ S + T` gives `vol T ≤ vol (S+T)`
  (`measure_preimage_add`/`Set.singleton_add`), monotonicity suffices. Otherwise, the volumes of `S' := a⁻¹ • S` and `T' := b⁻¹ • T` are 1
  (`Measure.addHaar_smul volume r s : volume (r • s) = ofReal |r ^ finrank| * volume s`,`ENNReal.rpow_natCast`),
  Take `t := a/(a+b)` (real numbers), multiplicative BM gives `1 ≤ vol {t x' + (1−t) y'}`, and the combined set = `(a+b)⁻¹ • (S + T)`
  (`Set.ext`, `Set.mem_add`, `Set.mem_smul_set`, `smul_smul`, `smul_add`), then go back to `addHaar_smul`. Between ENNReal/ℝ use
  `ENNReal.toReal`, `ENNReal.rpow_add` (nonzero non-apex), `ENNReal.rpow_mul`, `ENNReal.rpow_le_rpow_iff`.
- Analysis.isodiametric ← volume_rpow_mul_le_volume_combination：`S ⊆ closure S`(`measure_mono subset_closure`),
  `Metric.diam_closure`；`closure S` compact (`hS.isCompact_closure`) hence measurable and nonempty (S = ∅ is trivial).`T := (-1 : ℝ) • closure S`
  (Volume equal: `Measure.addHaar_smul`, `|(-1)^n| = 1`, `t = 1/2`: combinatorial set ⊆ `closedBall 0 (diam S / 2)`)
  (`z = (x − y)/2`,`norm_sub_le`→`Metric.dist_le_diam_of_mem hS.isCompact_closure.isBounded hx hy`,`dist_eq_norm`)；
  `InnerProductSpace.volume_closedBall` (requires `Nontrivial V`; n = 0 branches: `Module.finrank_zero_iff` ⇒ Subsingleton,
  `vol S ≤ vol univ = 1`: `measureSpaceOfInnerProductSpace`'s `volume` is `(stdOrthonormalBasis ℝ V).toBasis.addHaar`,
  `Basis.addHaar_self` Given the parallelotope measure 1, the empty base parallelotope is `{0} = univ`), `ω_n = √π^n / Γ(n/2+1)` and
  `KLS.unitBallVolume` Definition is word-for-word identical (`unfold KLS.unitBallVolume`). Left side `vol^{1/2} · vol^{1/2} = vol`:
  `ENNReal.rpow_add` (vol non-zero non-maximal; trivial at zero), or `ENNReal.rpow_add_of_nonneg`.
- Analysis.hausdorffMeasure_finrank_eq_smul_volume ← volume_le_ofReal_mul_hausdorffMeasure：
  (i) `μH[n]` is Haar (instance `isAddHaarMeasure_hausdorffMeasure`; note the index of the instance is `(finrank ℝ E : ℝ)`, consistent with the statement),
  Haar uniqueness `MeasureTheory.Measure.isAddLeftInvariant_eq_smul` (`Haar/Unique.lean`, `to_additive` from `isMulLeftInvariant_eq_smul`)
  or `Measure.addHaarMeasure_unique` to `μH[n] = c • volume`, `c := addHaarScalarFactor μH[n] volume`, `c ≠ 0, ⊤`
  (`addHaarScalarFactor_pos_of_isAddHaarMeasure`,NNReal).
  (ii) Lower bound `2^n/ω_n ≤ c`: substitute (i) into the previous statement at `closedBall 0 1` (volume `ω_n`, `volume_closedBall`), divided by `ω_n`.
  (iii) Upper bound `c ≤ 2^n/ω_n`: for `B := closedBall 0 1`, `ε > 0`, `Besicovitch.exists_disjoint_closedBall_covering_ae volume
  (fun _ ↦ Ioo 0 ε) B ...`(`Mathlib/MeasureTheory/Covering/Besicovitch.lean`, requires SFinite volume; gives a countable family of pairwise disjoint closed balls
  `closedBall (x i) (r i)`, `x i ∈ B`, `r i < ε`, `volume (B \ ⋃) = 0`). Then
  `μH[n] B ≤ μH[n] (⋃) + μH[n] (B \ ⋃)`; the second term by (i) is `c • 0 = 0`; the first term `≤ ∑ μH[n] (closedBall) ≤ ∑ (2 r i)^n`
  (single set cover, `Measure.hausdorffMeasure_le_liminf_tsum` or direct `hausdorffMeasure_apply` of ⨅ taking a unary cover + `EMetric.diam_closedBall`)
  `= (2^n/ω_n) ∑ volume (closedBall (x i) (r i)) = (2^n/ω_n) volume (⋃) ≤ (2^n/ω_n) volume (closedBall 0 (1+ε))`
  (Disjoint `measure_iUnion`, `x i ∈ B, r i < ε` ⇒ ball ⊆ `closedBall 0 (1+ε)`). Let `ε → 0` (`volume_closedBall` continuous on radius),
  Comparing with (i) yields `c · ω_n ≤ 2^n`. ENNReal multiplication and division: `ENNReal.mul_le_iff_le_inv`, `ENNReal.div_eq_inv_mul`.
  Final form: `Measure.ext`/`smul` `ENNReal.ofReal (2^n/ω_n) = (c : ℝ≥0∞)` by the inequalities on both sides + `le_antisymm`.
- Analysis.volume_rpow_mul_le_volume_combination ← prekopaLeindler: Following the pattern of one-dimensional `le_volume_combination`: first for a compact `K ⊆ S`, `L ⊆ T`
  Proof, `t • K + (1−t) • L` compact (`IsCompact.smul`, `IsCompact.add`), hence measurable; take `f := K.indicator 1`, `g := L.indicator 1`,
  `h := (t • K + (1−t) • L).indicator 1` (all measurable: `measurable_one.indicator`), PL premise pointwise: `0^t = 0` (`Real.zero_rpow ht0.ne'`) ,
  `1^t = 1`; Conclusion `∫⁻ ofReal (indicator 1) = vol` (`lintegral_indicator_one`); then `MeasurableSet.measure_eq_iSup_isCompact`
  + `ENNReal.rpow` monotone + `ENNReal.iSup_mul`/`ENNReal.mul_iSup` (rpow and iSup commute: `ENNReal.rpow_iSup`? In a one-dimensional file there is
  private `rpow_iSup`, copyable), the collection set contains relation `t • K + (1−t) • L ⊆ {t x + (1−t) y | x ∈ S, y ∈ T}`.

Layer two (Mathlib + repository input, should be able to complete)
- Analysis.prekopaLeindler (n-dimensional): induction on dimension. It is suggested not to perform induction on an abstract V, but rather:
  (a) First prove `prekopaLeindler_pi` on `Fin n → ℝ` (product Lebesgue `volume`) by induction on n. The n = 0 case is trivial (a one-point space, where integration is evaluation,
  `Fin 0 → ℝ` above `volume univ = 1`); n+1 using `MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0` and
  `MeasureTheory.volume_preserving_piFinSuccAbove`(`Mathlib/MeasureTheory/Constructions/Pi.lean`)splits `Fin (n+1) → ℝ` into
  `ℝ × (Fin n → ℝ)`, `lintegral_prod` (Tonelli, requires AEMeasurable); for fixed `x' y'`, the slice function `s ↦ f (s, x')` satisfies the one-dimensional PL assumption
  (Using `hfgh` in `(s, x')`, `(s', y')`), a one-dimensional PL (`Probability.Line.prekopaLeindler`) inequality for slice integrals; then for
  `F x' := ∫⁻ s, ofReal (f (s, x'))` uses the n-dimensional induction hypothesis. **Barrier**: the one-dimensional PL statement is about ℝ-valued functions + `ENNReal.ofReal`, while the slice integral
  `F, G, H` takes values in ℝ≥0∞ (possibly equal to ⊤, and not in `ofReal` form). First prove a version taking values in ℝ≥0∞ `prekopaLeindler_ennreal`
  (measurable `f g h : ℝ → ℝ≥0∞`, with `f x ^ t * g y ^ (1−t) ≤ h (t x + (1−t) y)`): use truncation `min (f x) N` and `ENNReal.toReal`
  Reduce to the ℝ-valued version, then `lintegral_iSup` monotone convergence (`Monotone`, `Measurable.min`); handle the n-dimensional induction hypothesis similarly, ideally performing the entire induction in
  Under ℝ≥0∞ valued forms, finally specializing to `ofReal ∘ f`. Measurability: `Measurable.lintegral_prod_right'`.
  (b) Move from `Fin n → ℝ` to V: `(stdOrthonormalBasis ℝ V).repr : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)`,
  `measurePreserving_repr_symm` (see the proof of `VolumeOfBalls.lean`'s `volume_ball`) and
  `EuclideanSpace.volume_preserving_measurableEquiv` (to `Fin n → ℝ`); linear equivalence preserves `t • x + (1−t) • y`
  (`map_add`,`map_smul`),`lintegral_map_equiv`/`MeasurePreserving.lintegral_comp`.
- Analysis.exists_lipschitzOnWith_levelSet_subset_image: Implicit function theorem in Mathlib `HasStrictFDerivAt.implicitFunction`
  (`Analysis/Calculus/Implicit.lean`, requires `f'` surjectivity + `ker f'` closed complement; for `f' = fderiv ℝ φ x : V →L[ℝ] ℝ ≠ 0`, surjectivity is given by
  `LinearMap.range_eq_top` + one-dimensional target, closed complement by `ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range`):
  `ψ := HasStrictFDerivAt.implicitFunction φ f' hφ' hsurj hker : ℝ → ker f' → V`,`implicitFunction_apply_image`
  (`∀ᶠ y in 𝓝 x, ψ (φ y) (proj (y − x)) = y`) Given: each point y in a level set of N is `ψ (φ x) (proj (y − x))`, that is
  `g := ψ (φ x)`,s := proj '' (N ∩ level set) (bounded, since N can be taken to be a ball, proj is continuous linear). Lipschitz of `g`:
  `ImplicitContDiff.contDiffAt_implicitFunction` (`Analysis/Calculus/ImplicitContDiff.lean`) to `ContDiffAt ℝ 1 (uncurry ψ) (φ x, 0)`,
  Again `ContDiffAt.exists_lipschitzOnWith` (`ContDiff/RCLike.lean`) gives a Lipschitz condition on some neighborhood; shrink N so that `s` falls into that neighborhood.
  `HasStrictFDerivAt`: From `ContDiff ℝ 1 φ` we obtain `hφ.contDiffAt.hasStrictFDerivAt le_rfl`.
- KLS.SmoothDomain.outwardNormal_eq: Let `(W₁, φ₁)` be a pair from `choose`, and let `(W, φ)` be a given pair, such that both have the same in a neighborhood of x.
  Negativity set `{φ₁ < 0} = U ∩ W₁ ∩ W = {φ < 0}`. Proof `Dφ₁ x = λ • Dφ x`, `λ > 0`: for any v and `Dφ x v < 0`, along `x + t v`
  First-order expansion (`HasFDerivAt.lim` or `hasDerivAt_iff_tendsto_slope`, see proof in `frontier_inter_eq`) gives for small t > 0 `φ (x + t v) < 0`
  ⇒ `φ₁ (x + t v) < 0` ⇒ `Dφ₁ x v ≤ 0` (otherwise expand similarly for positive values). Thus the half-space `{Dφ x v < 0} ⊆ {Dφ₁ x v ≤ 0}`, linear algebra:
  Take `v₀` such that `Dφ x v₀ = 1`, for any w write `w = (w − (Dφ x w) v₀) + (Dφ x w) v₀`, the first term on `ker (Dφ x)` (on which `Dφ₁ x = 0`,
  By (the limit from both sides of `±`), we obtain `Dφ₁ x w = (Dφ₁ x v₀) (Dφ x w)`, `λ := Dφ₁ x v₀ ≥ 0`, `λ ≠ 0` due to `Dφ₁ x ≠ 0`.
  Again `gradient` is the `fderiv`-image of `toDual.symm` (linear), `norm_smul`, positive normalization. Written as a private lemma
  `fderiv_eq_smul_fderiv_of_forall_lt_imp_le`.
- KLS.SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal ← integral_divergence_eq_integral_inner_outwardNormal：
  For each `e : V`, `F := fun x ↦ η x • e` ( `ContDiff.smul_const`, `HasCompactSupport.smul_right` ),
  `divergence F x = fderiv ℝ η x e = ⟪gradient η x, e⟫`: `fderiv`'s `smul_const` rule `fderiv_smul_const`,
  the rank-one formula for `LinearMap.trace` (`LinearMap.trace_smulRight`? If unavailable, the trace of `(fderiv ℝ η x).smulRight e` equals `fderiv ℝ η x e`,
  By `LinearMap.trace_eq_matrix_trace` for any basis or `LinearMap.trace_eq_sum_inner`/orthonormal basis expansion), `gradient` and inner product:
  `HasGradientAt`/`gradient_eq`. Taking inner product with e on both sides: `integral_inner` (`∫ ⟪e, f x⟫ = ⟪e, ∫ f⟫`, integrable; the integrand has compact support and is continuous.
  ⇒ integrable, on the boundary side using `IntegrableOn` + `outwardNormal` with continuity/boundedness on the frontier + locally finite), `ext_inner_right ℝ`.
- KLS.SmoothDomain.gradient_mollifiedIndicator_eq ← setIntegral_gradient_eq_integral_smul_outwardNormal：
  `mollifiedIndicator x = ∫_U η (x − y) dy` (`integral_indicator`/`setIntegral` rewrite); derivative with respect to x: convolution form
  `U.carrier.indicator 1 ⋆[lsmul ℝ ℝ, volume] φ.normed volume` (in this document, a reproof of RP's private `mollifiedIndicator_eq`),
  `HasCompactSupport.hasFDerivAt_convolution_right` + `convolution_precompR_apply` given
  `fderiv (mollified) x v = ∫ 𝟙_U(y) · (fderiv η (x − y)) v dy`；the other side: `η_x := fun y ↦ φ.normed volume (x − y)`,
  `ContDiff ℝ 1` (`contDiff_normed.comp (contDiff_const.sub contDiff_id)`), compact support (`hasCompactSupport_normed`)
  `HasCompactSupport.comp_homeomorph` or `.comp_isClosedEmbedding`),`gradient η_x y = −gradient (φ.normed) (x − y)`
  (`HasFDerivAt.comp` and `hasFDerivAt_const_sub`/`(hasFDerivAt_id).const_sub`/`fderiv_comp`, substitute into C2, `integral_neg`.)
  Both sides take values in `V`; a pointwise comparison using `ext_inner_right ℝ` is more convenient.

Layer three (lacking infrastructure, doing one's best; expected to leave sorry)
- Analysis.sard: Milnor's inductive proof (by induction on n; `C_i` = the set where all first i derivatives are identically zero). Suggestion to first do what is possible:
  (a) n = 0：`Subsingleton V`, like a point, `measure_singleton`.
  (b) n = 1：`V ≃L[ℝ] ℝ`(`ContinuousLinearEquiv.ofFinrankEq`/`LinearEquiv.toContinuousLinearEquiv`),Mathlib same-dimensional Sard
  `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (`Function/Jacobian.lean`) for `u ∘ e.symm : ℝ → ℝ`, determinant = derivative.
  (c) In general n: requires Fubini (along coordinate slices, `volume_preserving_piFinSuccAbove`), Taylor remainder term (`taylor_mean_remainder`/)
  `ContDiff`'s `isLittleO` together with a uniform estimate on compact sets; Mathlib lacks an existing framework. If not proceeding, leave sorry and note that (a)(b) have been completed.
  Note the statement with sharp exponent `ContDiff ℝ (finrank ℝ V) u`; `C^∞` is a special case obtained from `hu.of_le le_top`, but do not modify the statement.
- Analysis.aemeasurable_lintegral_levelSet and lintegral_enorm_gradient_mul_eq_lintegral_levelSet (coarea):
  Evans–Gariepy §3.4 approach: Rademacher(`LipschitzWith.ae_differentiableAt`); on an open subset of `{∇u ≠ 0}` using the implicit function of B2 to
  u is locally straightened to a coordinate projection, the same dimensional area formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (`Function/Jacobian.lean`) + Fubini
  Given local coarea (requiring `ℋ^{n−1}` for Lipschitz graph = `√(1+|∇g|²)` weighted Lebesgue, see below C1 with the same obstacle); `{∇u = 0}` on the left is 0,
  The right-hand side is obtained by Sard (`C¹` Lipschitz is insufficient—EG uses `C¹` approximation + a `ℋ^{n−1}(A ∩ {u = t})` estimate of Lipschitz functions with respect to `A ⊆ {∇u = 0}`);
  Lipschitz general case then approximated by `C¹` (Whitney extension, no support in Mathlib). **Expected to leave sorry**; if implemented, first implement `u` for `C¹` and the local version on `{∇u ≠ 0}`
  As a private lemma. The measurability statement is independent of the coarea formula, one may first try: measurability of `t ↦ surfaceMeasure (A ∩ {u = t})`
  The product measurability of `{(t, y) | u y = t}` + Fubini-type argument (`Measurable.lintegral_prod_right`), but requires the s-finiteness of `surfaceMeasure`
  ( `μH` is generally not s-finite; it becomes finite when restricted to `A` bounded compact slices—by locally finite + countable union).
- KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal (Gauss–Green, most important in this document):
  (a) Local form: F is supported inside a defining neighborhood W, and `{φ = 0} ∩ W` is the graph of a `C¹` function `g` on the hyperplane `P = (ℝ ∙ ν)ᗮ` (by B2 and strict
  Monotonicity, see RP's `addHaar_frontier`. Change of variables `Φ (z, s) := z + (g z + s) • ν` ( `P × ℝ → V`, `C¹` diffeomorphism, Jacobian determinant 1 ):
  `integral_image_eq_integral_abs_det_fderiv_smul` transform `∫_U div F` into `∫_{s<0} (div F) ∘ Φ`; along s by FTC
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` + Fubini (the Bochner version of `Probability.exists_lintegral_line`, or
  `MeasurePreserving.integral_prod` by `lineEquiv`; what remains to be proven is the boundary term `∫_P G(z, g z) √(1+|∇g z|²) dz = ∫_{graph} G dℋ^{n−1}`
  ——**Area formula for Lipschitz graphs**, Mathlib only has the area formula for same-dimensional areas. This is an independent, Mathlib-level sub-obligation; stated as a private or public lemma
  `hausdorffMeasure_graph_eq`, just give up and treat it as the only remaining one sorry.
  (global: `SmoothPartitionOfUnity.exists_isSubordinate` (`Geometry/Manifold/PartitionOfUnity.lean` , taking the `𝓘(ℝ, V)` model))
  Or `exists_smooth_zero_one_of_isClosed` manual stitching: `tsupport F ∩ frontier U` compact, finitely many defined neighborhoods covering, plus `U` interior and
  `closure U` External (there F's contribution is respectively `∫ div F = 0`: the divergence integral of a compactly supported field over the entire space is zero—this itself needs to be proven, using Fubini + one-dimensional FTC,
  Mathlib's `integral_divergence_of_hasFDerivAt_off_countable` only applies to boxes, taking a sufficiently large box containing `tsupport F` is sufficient to use it directly).
  `divergence` Leibniz rule for `ψ • F`: `divergence (ψ • F) = ⟪∇ψ, F⟫ + ψ divergence F` (`fderiv_smul`, `LinearMap.trace` linear +
  (rank-one trace).

Layer 4 (if C1 of layer 3 is completed)
- None. C2, C3, B1, E2, A2a, A2 have already been listed as assemblies in layer 1/2.

Report format: one obligation per line: name | completed/not completed | key API | bottleneck. List additional non-private lemmas separately. Provide `-DwarningAsError=true`
Compilation summary and `#print axioms` results. Do not claim that content not compiled successfully is considered completed. If a statement is found to be false, list "statement issue" and provide a counterexample, without changing the type.
```
