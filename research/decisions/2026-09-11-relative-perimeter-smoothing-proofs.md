# 2026-09-11 — `lem:relative-perimeter-smoothing`: Proof filling for WIP module (13/17 completed)

Following the same day's [statement-skeleton record](2026-09-11-relative-perimeter-smoothing-statement.md). This round changes only
`formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean` a file, not registered, not submitted, not pushed,
Do not change any theorem/def statement.

## Decision

- Fill proofs in this WIP module: of the statement skeleton's 17 obligations, 13 are proved; 4 retain `sorry`, with blockers documented in the module.
- New import: `Mathlib.Analysis.Calculus.ContDiff.Convolution` (differentiability of convolution),
  `Mathlib.MeasureTheory.Measure.Haar.Unique` (a Haar measure `IsNegInvariant` instance, `convolution_eq_swap` required),
  `Mathlib.Analysis.Calculus.Deriv.MeanValue` (`strictMonoOn_of_deriv_pos`); `open scoped` plus `Convolution`.
- Added private auxiliary declarations (all within this file, naming follows `research/naming.md`: short names do not repeat namespace, used once for auxiliary purposes `private`):
  `SmoothDomain.frontier_eq_empty_of_subsingleton`, `homothetyHomeomorph`, `coe_homothetyHomeomorph`(+`_symm`),
  `image_homothety_eq_preimage`, `contDiff_homothety`, `hasFDerivAt_homothety`, `locallyIntegrable_indicator`,
  `indicator_mem_Icc`, `mollifiedIndicator_eq`; `IsBorellDensity.nonempty_interior_pos`, `exists_ball_le`.
- By `research/naming.md` §Scope Section 4, add `omit ... in` to section variables that are not used, without closing linter.

## Completed Responsibilities and Key APIs

| Obligation | Key API |
|---|---|
| `SmoothDomain.frontier_inter_eq` | Before this round, already proven (skeleton comes with it) |
| `SmoothDomain.empty` / `univ` / `measurableSet` / `relativePerimeter_eq_zero_of_frontier_eq_empty` | Before this round, already proven (skeleton comes with) |
| `SmoothDomain.homothety` (`isOpen`, `exists_defining`) | `AffineMap.homothety_isOpenMap`, `Homeomorph.image_frontier`, `image_homothety_eq_preimage` (`Set.image_eq_preimage_of_inverse`,  note that in Mathlib it is the funext form of `Set.image f = Set.preimage g`, requires `congrFun`), `ContDiff.comp`, `HasFDerivAt.comp` + `HasFDerivAt.fderiv` |
| `SmoothDomain.indicator_homothety` | `image_homothety_eq_preimage`, `Set.indicator_of_mem` / `Set.indicator_of_notMem` |
| `SmoothDomain.hausdorff_frontier_homothety` | `Homeomorph.image_frontier`, `MeasureTheory.hausdorffMeasure_homothety_image` (to `0 ≤ d`), `Module.finrank_zero_iff` + `frontier_eq_empty_of_subsingleton` handling `n = 0`, `ENNReal.coe_rpow_of_ne_zero`, `ENNReal.smul_def` |
| `SmoothDomain.addHaar_frontier` | see the following section |
| `SmoothDomain.mollifiedIndicator_contDiff_lipschitz_mem_Icc` | `mollifiedIndicator = 𝟙_U ⋆[lsmul ℝ ℝ, m] φ.normed m`; `HasCompactSupport.contDiff_convolution_right`, `HasCompactSupport.hasFDerivAt_convolution_right`, `convolution_precompR_apply`, `convolution_eq_swap`, `lipschitzWith_of_nnnorm_fderiv_le`, `ContinuousLinearMap.opNorm_le_bound`, `norm_integral_le_of_norm_le`, `ContDiffBump.{nonneg_normed,integral_normed,integrable_normed,contDiff_normed,hasCompactSupport_normed}`, `Measure.integrableOn_of_bounded` (indicator locally integrable) |
| `IsBorellDensity.exists_le` | `convex_pos` + `Convex.interior_nonempty_iff_affineSpan_eq_top` + `Measure.addHaar_affineSubspace` (non-empty interior), `continuousOn_interior_pos` (upper and lower bounds of ball), on a ball of radius `r/2`, `ρ ≥ √(ρx·b₀)` (`logConcave` takes `t = 1/2`), `withDensity_apply`, `setLIntegral_mono`, `setLIntegral_const`, `Measure.addHaar_ball_center`, `Metric.measure_ball_pos`, `measure_ball_lt_top`, `prob_le_one` |
| `IsBorellDensity.le_rpow_mul_of_combination` | `Real.rpow_le_rpow`, `Real.rpow_mul`, `Real.rpow_add`, `Real.div_rpow`, `le_div_iff₀`; no need to discuss separately outside of `ρ x = 0` for different cases |
| `RelativePerimeter.tendsto_indicator_homothety` | `tendsto_lintegral_filter_of_dominated_convergence` (control function constant 1, `𝓝 1` countably generated), `Real.enorm_eq_ofReal_abs`, `Tendsto.congr'` (the two branches `x ∈ U` and `x ∉ closure U` eventually become 0), `ae_iff` transforms `hfr` into a.e. condition |

### Proof roadmap for `addHaar_frontier` (without implicit function theorem)

Mathlib does not have "`C^1` Haar zero-measure hypersurface". The current argument uses the **translation-disjoint** approach, requiring only the mean value theorem in one dimension:

1. `measure_null_of_locally_null` (second countable) reduces the problem to each boundary point having local zero measure.
2. Take the definition neighborhood `W, φ`, and by `fderiv ℝ φ y ≠ 0` take direction `n` so that `0 < fderiv ℝ φ y n`; `fderiv` is continuous (`ContDiff.continuous_fderiv`).
   This yields the ball `B = ball y r ⊆ {z | 0 < fderiv ℝ φ z n} ∩ W`.
3. `S := frontier U ∩ B`, by `frontier_inter_eq` we get `S ⊆ {φ = 0}`.
4. **Key**: `z ∈ S` and `z + u • n ∈ S` (`u > 0`) is impossible—the ball is convex, and `t ↦ φ (z + t • n)` has positive derivative on `[0, u]` (`strictMonoOn_of_deriv_pos`), hence `φ z < φ (z + u • n)`, contradicting that both ends are 0.
5. Thus `T k := (· + (-(t k • n))) ⁻¹' S` (`t k = 1/(k+1)`) are pairwise disjoint, all measurable, `m (T k) = m S` (`measure_preimage_add`]), and all contained in `ball y (r + ‖n‖)`. `measure_iUnion` + `ENNReal.tsum_const_eq_top_of_ne_zero` + `measure_ball_lt_top` forces `m S = 0`.

## Four remaining `sorry` obligations and obstacles

- `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`. Missing "the `C^∞` hypersurface's `μH[n-1]` on a compact slice is finite".
  Need: Express `{φ = 0} ∩ B` as the graph of a function on the hyperplane `n^⊥` (this document already has strict monotonicity along `n`, which provides uniqueness, but still requires Lipschitz property of the implicit function), then apply `LipschitzOnWith.hausdorffMeasure_image_le`, and compare `μH[n-1]` on `n^⊥` with Lebesgue measure (`hausdorffMeasure_pi_real` only applies to `EuclideanSpace ℝ (Fin k)`; requires transport via `stdOrthonormalBasis`'s `LinearIsometryEquiv` and `IsometryEquiv.hausdorffMeasure_image`).
  Note the difference from `addHaar_frontier`: there, mere zero measure suffices, and one can bypass the graph representation via elementary non-overlapping translations; finiteness cannot be avoided.
- `SmoothDomain.enorm_gradient_mollified_le` (this node's most important responsibility). Missing Gauss–Green.
  Mathlib's `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` only covers boxes; first, perform a coordinate transformation in graphical coordinates (`integral_image_eq_integral_abs_det_fderiv_smul`) or directly carry out a one-dimensional partial integration along the normal direction (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) with Fubini, and use a partition of unity. Materials already available within this document: `mollifiedIndicator_eq` (convolution form), `convolution_precompR_apply` (∇ component formulas), `frontier_inter_eq` (local `{φ = 0}` description).
- `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`. Pointwise bounds directly inherited from the previous statement; Tonelli's interchange requires the local finiteness from the previous one, so it is retained together. The remaining components are in place: `le_rpow_mul_of_combination`, `hausdorff_frontier_homothety`, `indicator_homothety`.
- `RelativePerimeter.exists_smooth_recovery_sequence`. Purely assembled, but the main term comes from the previous one. The regularity part (`mollifiedIndicator_contDiff_lipschitz_mem_Icc`) and the two parts of the `L¹` section (`tendsto_indicator_homothety`, `addHaar_frontier` providing `∂U` as `ν`-negligible) are both available.

## Compilation and Axioms

`lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/RelativePerimeter.lean`
Only the above 4 `declaration uses 'sorry'`s remain, with no other warnings (all `unusedSectionVars`s are handled using `omit ... in`).

All completed top-level declarations `#print axioms` are `[propext, Classical.choice, Quot.sound]`:
`SmoothDomain.homothety`, `indicator_homothety`, `hausdorff_frontier_homothety`, `addHaar_frontier`,
`mollifiedIndicator_contDiff_lipschitz_mem_Icc`, `IsBorellDensity.exists_le`,
`le_rpow_mul_of_combination`, `RelativePerimeter.tendsto_indicator_homothety`, and the skeleton's built-in
`frontier_inter_eq`, `empty`, `univ`, `measurableSet`, `relativePerimeter_eq_zero_of_frontier_eq_empty`.

## Not done

- Unregistered: aggregated import `FunctionalInequalities.lean`, lakefile, `research/a-series/ledger.yaml`, `research/check_blueprint.py`, `research/tasks.json`, Blueprint's `\lean{}` / `\leanok` remain unchanged.
- Not committed, not pushed. No shared files were created or modified besides this record.
- The statement "Every proof body is `sorry`" in the module documentation has been rewritten as-is; all other document sections (claimed / not claimed / restricted scope / dimension zero) remain unchanged.
