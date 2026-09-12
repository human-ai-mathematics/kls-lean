# 2026-09-11 — `lem:relative-perimeter-smoothing`：WIP 模块的证明填充（13/17 完成）

承接同日的[陈述骨架记录](2026-09-11-relative-perimeter-smoothing-statement.md)。本轮只改
`formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean` 一个文件，不注册、不提交、不推送，
不改任何 theorem/def 的陈述。

## 决定

- 补齐该 WIP 模块的 `sorry`：陈述骨架的 17 条义务中 13 条已证，4 条保留 `sorry` 并在模块文档里写明卡点。
- 新增 import：`Mathlib.Analysis.Calculus.ContDiff.Convolution`（卷积的可微性）、
  `Mathlib.MeasureTheory.Measure.Haar.Unique`（Haar 测度的 `IsNegInvariant` 实例，`convolution_eq_swap` 需要）、
  `Mathlib.Analysis.Calculus.Deriv.MeanValue`（`strictMonoOn_of_deriv_pos`）；`open scoped` 加 `Convolution`。
- 新增 private 辅助声明（均在本文件内，命名遵守 `research/naming.md`：短名不复述命名空间，一次性辅助用 `private`）：
  `SmoothDomain.frontier_eq_empty_of_subsingleton`、`homothetyHomeomorph`、`coe_homothetyHomeomorph`(+`_symm`)、
  `image_homothety_eq_preimage`、`contDiff_homothety`、`hasFDerivAt_homothety`、`locallyIntegrable_indicator`、
  `indicator_mem_Icc`、`mollifiedIndicator_eq`；`IsBorellDensity.nonempty_interior_pos`、`exists_ball_le`。
- 按 `research/naming.md` §作用域第 4 条，为不用的 section 变量加 `omit ... in`，不关闭 linter。

## 已完成的义务与关键 API

| 义务 | 关键 API |
|---|---|
| `SmoothDomain.frontier_inter_eq` | 本轮之前已证（骨架自带） |
| `SmoothDomain.empty` / `univ` / `measurableSet` / `relativePerimeter_eq_zero_of_frontier_eq_empty` | 本轮之前已证（骨架自带） |
| `SmoothDomain.homothety`（`isOpen`、`exists_defining`） | `AffineMap.homothety_isOpenMap`、`Homeomorph.image_frontier`、`image_homothety_eq_preimage`（`Set.image_eq_preimage_of_inverse`，注意 Mathlib 里它是 `Set.image f = Set.preimage g` 的 funext 形式，要 `congrFun`）、`ContDiff.comp`、`HasFDerivAt.comp` + `HasFDerivAt.fderiv` |
| `SmoothDomain.indicator_homothety` | `image_homothety_eq_preimage`、`Set.indicator_of_mem` / `Set.indicator_of_notMem` |
| `SmoothDomain.hausdorff_frontier_homothety` | `Homeomorph.image_frontier`、`MeasureTheory.hausdorffMeasure_homothety_image`（要 `0 ≤ d`）、`Module.finrank_zero_iff` + `frontier_eq_empty_of_subsingleton` 处理 `n = 0`、`ENNReal.coe_rpow_of_ne_zero`、`ENNReal.smul_def` |
| `SmoothDomain.addHaar_frontier` | 见下节 |
| `SmoothDomain.mollifiedIndicator_contDiff_lipschitz_mem_Icc` | `mollifiedIndicator = 𝟙_U ⋆[lsmul ℝ ℝ, m] φ.normed m`；`HasCompactSupport.contDiff_convolution_right`、`HasCompactSupport.hasFDerivAt_convolution_right`、`convolution_precompR_apply`、`convolution_eq_swap`、`lipschitzWith_of_nnnorm_fderiv_le`、`ContinuousLinearMap.opNorm_le_bound`、`norm_integral_le_of_norm_le`、`ContDiffBump.{nonneg_normed,integral_normed,integrable_normed,contDiff_normed,hasCompactSupport_normed}`、`Measure.integrableOn_of_bounded`（indicator 局部可积） |
| `IsBorellDensity.exists_le` | `convex_pos` + `Convex.interior_nonempty_iff_affineSpan_eq_top` + `Measure.addHaar_affineSubspace`（内部非空）、`continuousOn_interior_pos`（球上下界）、半径 `r/2` 的球上 `ρ ≥ √(ρx·b₀)`（`logConcave` 取 `t = 1/2`）、`withDensity_apply`、`setLIntegral_mono`、`setLIntegral_const`、`Measure.addHaar_ball_center`、`Metric.measure_ball_pos`、`measure_ball_lt_top`、`prob_le_one` |
| `IsBorellDensity.le_rpow_mul_of_combination` | `Real.rpow_le_rpow`、`Real.rpow_mul`、`Real.rpow_add`、`Real.div_rpow`、`le_div_iff₀`；不需要对 `ρ x = 0` 单独讨论以外的分情形 |
| `RelativePerimeter.tendsto_indicator_homothety` | `tendsto_lintegral_filter_of_dominated_convergence`（控制函数常数 1，`𝓝 1` 可数生成）、`Real.enorm_eq_ofReal_abs`、`Tendsto.congr'`（`x ∈ U` 与 `x ∉ closure U` 两支上最终为 0）、`ae_iff` 把 `hfr` 变成 a.e. 条件 |

### `addHaar_frontier` 的证明路线（不用隐函数定理）

Mathlib 没有"`C^1` 超曲面 Haar 零测"。本轮用的是**平移不交**论证，只需要一维中值定理：

1. `measure_null_of_locally_null`（第二可数）把问题化为每个边界点的局部零测。
2. 取定义邻域 `W, φ`，由 `fderiv ℝ φ y ≠ 0` 取方向 `n` 使 `0 < fderiv ℝ φ y n`；`fderiv` 连续（`ContDiff.continuous_fderiv`）
   给出球 `B = ball y r ⊆ {z | 0 < fderiv ℝ φ z n} ∩ W`。
3. `S := frontier U ∩ B`，由 `frontier_inter_eq` 得 `S ⊆ {φ = 0}`。
4. **关键**：`z ∈ S` 且 `z + u • n ∈ S`（`u > 0`）不可能——球是凸的，`t ↦ φ (z + t • n)` 在 `[0, u]` 上
   导数为正（`strictMonoOn_of_deriv_pos`），故 `φ z < φ (z + u • n)`，与两端都为 0 矛盾。
5. 于是 `T k := (· + (-(t k • n))) ⁻¹' S`（`t k = 1/(k+1)`）两两不交、都可测、`m (T k) = m S`
   （`measure_preimage_add`），且全部落在 `ball y (r + ‖n‖)` 里。`measure_iUnion` +
   `ENNReal.tsum_const_eq_top_of_ne_zero` + `measure_ball_lt_top` 迫使 `m S = 0`。

## 保留 `sorry` 的 4 条与卡点

- `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`。缺"`C^∞` 超曲面的 `μH[n-1]` 在紧片上有限"。
  需要：把 `{φ = 0} ∩ B` 写成超平面 `n^⊥` 上某函数的图（本文件已有沿 `n` 的严格单调性，可给出唯一性，
  但还需该隐函数的 Lipschitz 性），再用 `LipschitzOnWith.hausdorffMeasure_image_le`，并把 `n^⊥` 上的
  `μH[n-1]` 与 Lebesgue 比较（`hausdorffMeasure_pi_real` 只对 `EuclideanSpace ℝ (Fin k)`，需经
  `stdOrthonormalBasis` 的 `LinearIsometryEquiv` 与 `IsometryEquiv.hausdorffMeasure_image` 搬运）。
  注意与 `addHaar_frontier` 不同：那条只要零测，可以用平移不交的初等论证绕开图表示；有限性绕不开。
- `SmoothDomain.enorm_gradient_mollified_le`（本节点最重的义务）。缺 Gauss–Green。
  Mathlib 的 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` 只覆盖盒子，
  需要先在图坐标下做坐标变换（`integral_image_eq_integral_abs_det_fderiv_smul`）或直接做沿法向的一维分部积分
  （`intervalIntegral.integral_eq_sub_of_hasDerivAt`）加 Fubini，并配单位分解。本文件内已经具备的材料：
  `mollifiedIndicator_eq`（卷积形式）、`convolution_precompR_apply`（∇ 的分量公式）、
  `frontier_inter_eq`（局部 `{φ = 0}` 描述）。
- `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`。逐点界直接取自上一条，
  Tonelli 换序又要上上条的局部有限性，故一并保留。其余零件已就位：`le_rpow_mul_of_combination`、
  `hausdorff_frontier_homothety`、`indicator_homothety`。
- `RelativePerimeter.exists_smooth_recovery_sequence`。纯组装，但组装的主项是上一条。正则性部分
  （`mollifiedIndicator_contDiff_lipschitz_mem_Icc`）与 `L¹` 部分的两块
  （`tendsto_indicator_homothety`、`addHaar_frontier` 给出的 `∂U` 为 `ν`-零测）都已可用。

## 编译与公理

`lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/RelativePerimeter.lean`
只剩上述 4 条 `declaration uses 'sorry'`，无其它警告（`unusedSectionVars` 一律用 `omit ... in` 处理）。

已填完的顶层声明 `#print axioms` 均为 `[propext, Classical.choice, Quot.sound]`：
`SmoothDomain.homothety`、`indicator_homothety`、`hausdorff_frontier_homothety`、`addHaar_frontier`、
`mollifiedIndicator_contDiff_lipschitz_mem_Icc`、`IsBorellDensity.exists_le`、
`le_rpow_mul_of_combination`、`RelativePerimeter.tendsto_indicator_homothety`，以及骨架自带的
`frontier_inter_eq`、`empty`、`univ`、`measurableSet`、`relativePerimeter_eq_zero_of_frontier_eq_empty`。

## 未做

- 未注册：聚合导入 `FunctionalInequalities.lean`、lakefile、`research/a-series/ledger.yaml`、
  `research/check_blueprint.py`、`research/tasks.json`、Blueprint 的 `\lean{}` / `\leanok` 均未动。
- 未提交、未推送。除本记录外未新建或修改任何共享文件。
- 模块文档中"Every proof body is `sorry`"一句已按现状改写，其余文档段落（claimed / not claimed /
  restricted scope / dimension zero）未动。
