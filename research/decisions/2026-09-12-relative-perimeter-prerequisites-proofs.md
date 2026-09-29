# 2026-09-12 — Analytical prerequisites for relative perimeter chains: fill sorry (12/17 completed)

On the same day, [statement record](2026-09-12-relative-perimeter-prerequisites-statement.md) and
[sorry prompt](2026-09-12-relative-perimeter-prerequisites-sorry-prompt.md). This round only modifies
`formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` one file: 17 clause completed 12 clauses,
leaving 5 clauses `sorry`. No changes to any `theorem`/`def` type, no changes to the definitions of two `def`, no changes to
`RelativePerimeter.lean` / `CheegerInfimum.lean` (the `sorry` values remain 5 and 9), no registration, no commit, no push.

## Overview

| Obligation (omitted `FunctionalInequalities.`) | Status | Key API | Bottleneck |
|---|---|---|---|
| `Analysis.prekopaLeindler` | completed | see below "Group A" | — |
| `Analysis.volume_rpow_mul_le_volume_combination` | completed | indicator function substitution into PL + `MeasurableSet.measure_eq_iSup_isCompact` + `ENNReal.orderIsoRpow` | — |
| `Analysis.volume_rpow_add_le_volume_add_rpow` | completed | homogenization + `Measure.addHaar_smul_of_nonneg` + `ENNReal.ofReal_rpow_of_nonneg` | — |
| `Analysis.isodiametric` | completed | `t = 1/2`'s multiplicative type BM + `InnerProductSpace.volume_closedBall` + `Metric.diam_closure` | — |
| `Analysis.volume_le_ofReal_mul_hausdorffMeasure` | completed | `Measure.le_hausdorffMeasure` (ε = 1) + `isodiametric` | — |
| `Analysis.hausdorffMeasure_finrank_eq_smul_volume` | completed | Haar uniqueness + Besicovitch; see below «A2» | — |
| `Analysis.exists_lipschitzOnWith_levelSet_subset_image` | completed | `HasStrictFDerivAt.implicitFunctionOfComplemented`, `to_implicitFunctionOfComplemented`, `HasStrictFDerivAt.exists_lipschitzOnWith` | — |
| `Analysis.exists_hausdorffMeasure_levelSet_lt_top` | completed | `LipschitzOnWith.hausdorffMeasure_image_le`, `Module.Dual.finrank_ker_add_one_of_ne_zero`, `isAddHaarMeasure_hausdorffMeasure` | — |
| `Analysis.aemeasurable_lintegral_levelSet` | **Incomplete** | — | See below "D group" |
| `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | **Incomplete** | — | See below "D group" |
| `Analysis.sard` | **Incomplete** | — | See below "E group" |
| `Analysis.ae_forall_fderiv_ne_zero` | completion (depends on `sard`) | `ae_iff` + `measure_mono_null` | — |
| `KLS.SmoothDomain.outwardNormal_eq` | completed | slope argument along rays + half-space containment by linear functionals; see below "C group" | — |
| `KLS.SmoothDomain.norm_outwardNormal` | completed | `dif_pos`, `toDual_gradient`, `inv_mul_cancel₀` | — |
| `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | **Incomplete** | — | See below "C1" |
| `KLS.SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal` | **Incomplete** | — | See below "C2" |
| `KLS.SmoothDomain.gradient_mollifiedIndicator_eq` | completion (dependent on C2) | convolution derivative + `ext_inner_right` + `integral_inner` | — |

`#print axioms`: In the completed list 12, **item 10 only depends on `propext / Classical.choice / Quot.sound`**;
`ae_forall_fderiv_ne_zero` (depending on `sard`) and `gradient_mollifiedIndicator_eq` (depending on C2) additionally appear `sorryAx`,
this is as expected by the hierarchical design of the prompt (the assembly layer completes before its inputs).

## Completed Proof: Paths and New private Lemmas

**All new declarations are `private`**, with no new non-private general lemmas added; 17 public statements and 2 `def` are word-for-word unchanged.

### Group A (isodiametric inequality, 6/6 completed, all without `sorryAx`)

n-dimensional Prékopa–Leindler via "abstract properties + dimensional induction":

* `private def IsPL (X) (μ) (t)`: `ℝ≥0∞` value PL property (`f g h : X → ℝ≥0∞` measurable,
  `f x ^ t * g y ^ (1−t) ≤ h (t • x + (1−t) • y)` ⟹ (the corresponding inequality for integrals). Use `ℝ≥0∞` values instead of those in the prompt
  ofReal ∘ (ℝ-valued), is precisely designed to circumvent the obstacle pointed out by the prompt: the slice integral `∫⁻ s, f (s, x')` might be `⊤`, and is not necessarily `ofReal` form.
* `private isPL_real`: by the warehouse's `Probability.Line.prekopaLeindler` cut off by `min · N` (`N : ℕ`) + `toReal`
  Reduction, then use `lintegral_iSup` monotone convergence to remove the truncation. Auxiliary `private iSup_min_natCast`, `private rpow_iSup`
  (The latter is a copy of the privately named lemma in `Probability/Line/BrunnMinkowski.lean`, and cannot be referenced across modules.)
`private IsPL.prod`: Tonelli (`lintegral_prod`, `Measurable.lintegral_prod_right'`) + Y's PL for slicing,
  Use the PL of X for slicing integrals.
* `private IsPL.comp` / `IsPL.symm`: Transport along a map preserving measure and preserving convex combinations (`MeasurePreserving.lintegral_comp`);
  `symm` By the injectivity of `MeasurableEquiv`, the forward linearity is transformed into backward linearity.
* `private isPL_pi`: induction on `n`. `n = 0` by `Measure.volume_pi_eq_dirac` + `lintegral_dirac'`;
  `n+1` using `MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0` and `volume_preserving_piFinSuccAbove`,
  Its linearity is `rfl`.
* `private isPL_euclidean`, `private isPL_volume`: `PiLp.volume_preserving_toLp` (linearity `rfl`) and
  `OrthonormalBasis.measurePreserving_repr_symm` (linearity `simp`).

`volume_rpow_mul_le_volume_combination` and the one-dimensional `le_volume_combination` follow the same pattern (regularity within compact subsets + `iSup`),
`volume_rpow_add_le_volume_add_rpow`, `isodiametric`, `volume_le_ofReal_mul_hausdorffMeasure` along the prompt's route.
The `isodiametric` `n = 0` branch is given by `Basis.addHaar_self` and `Subsingleton.eq_univ_of_nonempty` to yield `vol univ = 1`.

**A2 (`hausdorffMeasure_finrank_eq_smul_volume`) Actual Path** differs slightly from the prompt, recorded here:

1. Haar uniqueness uses `Measure.isAddLeftInvariant_eq_smul` (not `addHaarMeasure_unique`),
   Get `μH[n] = (addHaarScalarFactor μH[n] volume : ℝ≥0) • volume`.
2. The lower bound is taken by `volume_le_ofReal_mul_hausdorffMeasure` on `Metric.ball 0 1` (`InnerProductSpace.volume_ball`).
3. Upper bound `private hausdorffMeasure_ball_le`: **apply Besicovitch to the scale premeasure on `mkMetric`**, rather than to
   on `μH[n]`. A crucial step omitted by the prompt: `μH[n] (closedBall x r) ≤ (2r)^n` is as strong as the conclusion itself and cannot be proved first;
   But for each scale `k⁻¹`, `OuterMeasure.mkMetric'.pre_le` directly provides a "single set cover" bound. Thus
   `μH[n] s = ⨆ k, pre (fun t ↦ ediam t ^ n) k⁻¹ s` (`OuterMeasure.mkMetric'.eq_iSup_nat` +
   (`OuterMeasure.coe_mkMetric`), for each `k` use `Besicovitch.exists_disjoint_closedBall_covering_ae`
   Cover `ball 0 1` to the zero measure set, the difference set part is represented by `c • volume` in step 1, `0`, and the spherical part by `pre_le`,
   Sum of `Metric.diam_closedBall`, `InnerProductSpace.volume_closedBall`, and `measure_biUnion` (pairwise disjoint).
4. **Use open balls instead of closed balls**, and let Besicovitch's upper bound on the radius be `min δ (1 − ‖x‖)`, so that all small balls lie within `ball 0 1`;
   Thus the upper bound is directly `ofReal(2^n/ω_n) · vol(ball 0 1)`, eliminating the limit argument involving `ε → 0`.
5. `n = 0` Branch listed: `Measure.hausdorffMeasure_zero_singleton` and `vol univ = 1`, both sides are `1`.

### B group (2/2 completed, no `sorryAx`)

`exists_lipschitzOnWith_levelSet_subset_image` using `HasStrictFDerivAt.implicitFunctionOfComplemented`
(the **version with `hker`**, not the finite-dimensional version `implicitFunction` suggested by the prompt), because only this version allows
`(Φ y).snd = P (y − x)` to hold for the explicit projection `P = Classical.choose hker`
(`implicitToOpenPartialHomeomorphOfComplemented_apply`):
the boundedness of `s` thus reduces to "`P` is a continuous linear map, `N ⊆ ball x 1`", and the Lipschitz property of `g` is given by the `to_implicitFunctionOfComplemented`-provided `HasStrictFDerivAt g (ker).subtypeL 0` plus `HasStrictFDerivAt.exists_lipschitzOnWith`—**without** the `ImplicitContDiff` file.
`N` is taken as the intersection of `eq_implicitFunctionOfComplemented`'s neighborhood, `P(· − x)`'s preimage under Lipschitz neighborhoods, and `ball x 1`.

`exists_hausdorffMeasure_levelSet_lt_top` assemble according to the prompt; `finrank ker = n − 1` use
`Module.Dual.finrank_ker_add_one_of_ne_zero` (more directly than the prompt suggests `finrank_range_add_finrank_ker`).

### C group (3/5 completed)

* `norm_outwardNormal`: `dif_pos` + `toDual_gradient`.
* `outwardNormal_eq`: First prove that any two definitions yield the same unit normal. Three private auxiliaries:
  `eventually_lt_zero_of_hasDerivAt` / `eventually_zero_lt_of_hasDerivAt` (`hasDerivAt_iff_tendsto_slope`,
  of the same type as the argument in `RelativePerimeter.frontier_inter_eq`, but organized into the `𝓝[>] 0` `Eventually` form),
  `hasDerivAt_line`, and linear algebra's `eq_smul_of_forall_lt_imp_le`:
  `{A v < 0} ⊆ {B v ≤ 0}` and `A` surjective ⟹ `B = λ • A`, `λ > 0` (bilateral ε argument on the kernel).
  Then, by the injectivity of `toDual`, transfer the proportionality relation from `fderiv` to `gradient`.
* `gradient_mollifiedIndicator_eq`: By the hint, from C2 to `η_x = φ.normed volume (x − ·)`.
  Convolution derivative uses `HasCompactSupport.hasFDerivAt_convolution_right` and `convolution_precompR_apply`,
  then uses `ext_inner_right ℝ` and `integral_inner` to compare component-wise; `gradient η_x y = −gradient η (x − y)` follows from
  the injectivity of `HasFDerivAt.const_sub` and `toDual`. Two private copies
  `mollifiedIndicator_eq_convolution`, `locallyIntegrable_indicator_one` correspond to private lemmas in RP that cannot be cross-module referenced.

## Incomplete 5 Item: Critical Point

### C1 `integral_divergence_eq_integral_inner_outwardNormal` (Gauss–Green)

No movement. The checkpoint and the third-level judgment of the prompt are consistent and more specific: the only true missing piece is the **area formula on Lipschitz graphs**.
`∫_P G(z, g z) √(1+|∇g z|²) dz = ∫_{graph} G dℋ^{n−1}`, Mathlib only has area formulas for the same dimension
 (`MeasureTheory/Function/Jacobian.lean`). Partition of unity and one-dimensional partial integration along the normal direction both have ready-made materials,
but connecting them to `surfaceMeasure` (i.e., the normalization of `μH[n−1]`) requires going through this subtask. This subtask has not yet begun.

### C2 `setIntegral_gradient_eq_integral_smul_outwardNormal`

**Prompt labels this entry as "Easy (given C1)", which is overly optimistic**, reason recorded: lifting the `∫_U ⟪∇η, e⟫ = ∫_{∂U} ⟪e, η ν⟫` of C1 into a vector equation `∫_U ∇η = ∫_{∂U} η ν` requires `integral_inner`, thus requiring the integrand `y ↦ η y • ν y` to be **integrable** under `(surfaceMeasure V).restrict (frontier U)`, which involves two conditions:

1. `surfaceMeasure V (frontier U ∩ tsupport η) < ⊤`——that is `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`
   (RP is still `sorry`, but this round's `exists_hausdorffMeasure_levelSet_lt_top` is already its complete input);
2. **`outwardNormal` measurability on the frontier**. This statement has not appeared in the statement record: `outwardNormal` uses
   defined using `Classical.choose`, so measurability is not immediate. The valid statement is that `ν` is continuous on the frontier, by `outwardNormal_eq`
   With the continuity of `∇φ/‖∇φ‖`, but only valid within each defined neighborhood `W`; overall measurability requires an open cover of the frontier
   `{W_i}` Take a countable subcover (`V` finite-dimensional hence Lindelöf), then perform a countable piecewise division. This is an independent, approximately hundred-line obligation,
   Suggest to list separately as `SmoothDomain.continuousOn_outwardNormal` / `measurable_outwardNormal`.

If it does not hold (i.e. `η • ν` is not integrable), the right-hand side is taken as `0` by Bochner's convention, while the left-hand side is generally nonzero, so this step cannot be bypassed.

### D group `aemeasurable_lintegral_levelSet`, `lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (coarea)

No action taken, consistent with the third-level expectation of the prompt: missing the area formula on Lipschitz graphs (same as C1), Whitney extension (approximation via `C¹`), and the s-regularization required for measurability in `t ↦ μH[n−1] (A ∩ {u = t})`. No local version was implemented.

### E group `sard`

No progress. Milnor's induction on dimension requires uniform estimates of Taylor remainders on compact sets and Fubini along coordinate slices, and the Mathlib materials are available.
However, there is no ready-made framework; the suggested branches (a) `n = 0` and (b) `n = 1` even if written down cannot eliminate this `sorry`.
(The statement holds for all `n`.) Thus, no half-finished work was written this round. **Note**: `ae_forall_fderiv_ne_zero` has been completed and only depends on `sard`; therefore, once `sard` is proven, the `SmoothDomain.ae_exists_superlevel` of `CheegerInfimum.lean` can be immediately assembled.

## Statement of the problem

No false statements were found. 17 Each statement was used as stated; the two `def` definitions suffice.
(`outwardNormal`'s `Classical.choose` form was handled smoothly in `outwardNormal_eq`, see above).
The only "statement-level gap" is the measurability of `outwardNormal` mentioned above—this is not a false statement, but rather a missing lemma in the chain that has not been formally required.

## New non-private lemmas

Nothing.

## Compilation

Under `formalization/` (native arm64 toolchain):

```
lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites   # Build completed successfully (3088 jobs)
lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
```

`lake env lean` output exactly 5 `declaration uses 'sorry'`s (879, 889, 906, 1102, 1111 lines), no other warnings;
`-DwarningAsError=true` below 5 lines upgraded to error, **no other diagnostics**. Line 1218 of the file.

New imports: `Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`, `Mathlib.Analysis.Calculus.Implicit`, `Mathlib.MeasureTheory.Constructions.Pi`, `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`, `FunctionalInequalities.Probability.Line.BrunnMinkowski`; `open scoped` adds `Convolution`.
According to prompt item 3, handle the newly appeared `unusedSectionVars` warnings after filling each item with `omit [...] in`
(`rpow_iSup`, `hasDerivAt_line`, `eq_smul_of_forall_lt_imp_le`, two private copies of C3]).

## Not done

- Unaltered `RelativePerimeter.lean` (Article 5, Clause `sorry`), `CheegerInfimum.lean` (Article 9, Clause `sorry`).
- Not registered: `FunctionalInequalities.lean`, lakefile `Solutions` branch, `research/a-series/ledger.yaml`, `research/check_blueprint.py`, `research/tasks.json`, Blueprint's `\lean{}`/`\leanok` remain unchanged.
- Not `git commit`, not `git push`.
