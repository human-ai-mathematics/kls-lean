# 2026-09-11 — `lem:relative-perimeter-cheeger-infimum`：证明进展（追加型记录）

## 决定

- 在两个既有 WIP 文件（`formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean`、
  `formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean`）内填 sorry，不改任何
  `theorem`/`def` 的类型签名，不注册、不提交、不推送、不改共享文件。
- `CheegerInfimum.lean` 原 25 条 `sorry`：**13 条已证完**（含 3 条纯粘合/组装引理，其证明本身
  `sorry`-free，但传递依赖仍带 `sorry` 的下游引理，见下）；**12 条仍为 `sorry`**，均已在代码内加注释
  说明卡点。`RelativePerimeter.lean` 新增的 1 条 `hausdorffNormalized_finrank_eq_volume` 仍为 `sorry`
  （已加注释说明卡点），文件其余部分未改动。
- 未发现需要为了消除 `sorry` 而伪造/绕过陈述本意的证明；两处怀疑陈述有误/有缺口的（见"陈述问题"一节）
  按规则 1 保留 `sorry` 并在此记录反例，未擅自改类型。

## 逐条状态

### `CheegerInfimum.lean`（25 条）

| 名称 | 状态 | 关键 API | 卡点 |
|---|---|---|---|
| `SmoothDomain.ae_exists_superlevel` | 未完成 | — | Sard 定理：Mathlib 只有同维数的 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`（`Jacobian.lean`），没有一般维数的 Sard（临界值集合零测）。留 `sorry`，写明缺基础设施。 |
| `SmoothDomain.frontier_superlevel_subset` | **完成** | `frontier_subset_closure`、`closure_lt_subset_le`、`isOpen_lt` | — |
| `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（加权 coarea 公式） | 未完成 | — | Mathlib 只有同维数的面积公式，没有 coarea 公式（`{∇u≠0}` 上局部拉直+隐函数定理的路线未实现）。留 `sorry`。 |
| `minkowskiConstant_eq_top_of_subsingleton` | **完成** | `iInf_eq_top`、`iInf_pos`、`iInf_neg`、`measure_univ` | — |
| `smoothConstant_eq_top_of_subsingleton` | **完成** | 同上 | — |
| `measure_closure_eq_of_minkowskiContent_ne_top` | **完成** | `Metric.closure_subset_thickening`、`tsub_le_tsub_right`、`ENNReal.tendsto_ofReal_nhds_top`、`tendsto_inv_nhdsGT_zero`、`ENNReal.Tendsto.const_mul`、`liminf_le_liminf`、`Filter.Tendsto.liminf_eq` | — |
| `lintegral_measure_symmDiff_superlevel` | **完成** | `lintegral_lintegral_swap`（Tonelli）、`lintegral_indicator_one`、`Set.Ioo_inter_Iio`、`measure_sdiff`、`ENNReal.ofReal_sub`、`Real.enorm_eq_ofReal_abs` | 最长的纯 Mathlib 证明；核心是把 t-积分与 x-积分通过乘积测度 Fubini 交换，再逐点计算区间长度。 |
| `min_measure_le_add_measure_symmDiff` | **完成** | `measure_union_le`、`measure_compl`、`compl_symmDiff_compl` | 私有辅助 `hbasic`（`ν C ≤ ν D + ν(C∆D)`）对 `(A,B)` 和 `(Aᶜ,Bᶜ)` 各用一次，再按 `min` 的两支分类。 |
| `tendsto_lintegral_min_superlevel` | **完成** | `Antitone.measurable`（把 `t ↦ ν{t<u_j}` 的可测性归约为其单调性）、`Measurable.min`、`setLIntegral_mono'`、`lintegral_add_left`、`ENNReal.Tendsto.sub`、`Tendsto.const_add`、`tendsto_of_tendsto_of_tendsto_of_le_of_le'`（夹逼） | 需要证明 `min(ν{t<u_j x})(...)` 关于 `t` 可测，用其反单调性；否则 `lintegral_add_left` 拆不出这一项。 |
| `distanceCutoff_mem_Icc` | **完成** | `le_max_left`、`max_le`、`Metric.infDist_nonneg` | — |
| `lipschitzWith_distanceCutoff` | **完成** | `Metric.lipschitz_infDist_pt`、`abs_max_sub_max_le_abs`、`LipschitzWith.of_dist_le'` | 直接用 `dist ≤ K*dist` 的定义式证明，绕开了寻找 `LipschitzWith.const_sub`/`const_max` 组合子的麻烦。 |
| `distanceCutoff_eq_one_of_mem_closure` | **完成** | `Metric.mem_closure_iff_infDist_zero` | — |
| `distanceCutoff_eq_zero_of_notMem_thickening` | **未完成（陈述问题）** | — | **`B = ∅` 时陈述为假**，见下"陈述问题"。 |
| `tendsto_distanceCutoff_indicator` | **未完成（陈述/前提问题）** | — | 缺 `MeasurableSet B`（或 `NullMeasurableSet B ν`）前提，见下"陈述问题"。 |
| `lintegral_enorm_gradient_distanceCutoff_le` | 未完成 | — | 需要 Rademacher（`LipschitzWith.ae_differentiableAt`）+"水平集上梯度 a.e. 为零"的论证（未在 Mathlib 中找到直接引理，需要 Lebesgue 密度点或专门构造）；受时间限制未展开。 |
| `exists_smooth_approximation_lipschitz` | 未完成 | — | 需要 `Energy/Euclidean/LipschitzApproximation.lean` 的磨光算子与梯度磨光交换的引理配合一致连续性论证；受时间限制未展开。 |
| `smoothConstant_mul_lintegral_min_superlevel_le` | 未完成 | — | 依赖 Sard（`ae_exists_superlevel`）与 coarea 公式（`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`），两者均未完成。 |
| `lintegral_minkowskiContent_superlevel_le`（ADG 2017 Lemma 3.2） | 未完成 | — | 需要"闭超水平集加厚 ⊆ 局部 Lipschitz 常数控制的窄带"的初等但繁琐的论证，加上单调收敛/Fatou 交换极限与积分；受时间限制未展开。 |
| `minkowskiConstant_mul_lintegral_min_superlevel_le` | 未完成 | — | 依赖上一条。 |
| `minkowskiConstant_le_smoothConstant` | 未完成 | — | 依赖 `RelativePerimeter.exists_smooth_recovery_sequence`（本身在 `RelativePerimeter.lean` 中未完成）与 `minkowskiConstant_mul_lintegral_min_superlevel_le`；组装本身（`limsup`/`le_iInf` 操作）也未展开。 |
| `smoothConstant_le_minkowskiConstant` | 未完成 | — | 依赖 `lintegral_enorm_gradient_distanceCutoff_le`、`exists_smooth_approximation_lipschitz`、`smoothConstant_mul_lintegral_min_superlevel_le`，且需要处理 `Filter.exists_seq_tendsto_liminf` 式的对角化；受时间限制未展开。 |
| `minkowskiConstant_eq_smoothConstant` | **完成（粘合）** | `le_antisymm` | 证明本身是纯粘合（`le_antisymm (minkowskiConstant_le_smoothConstant hρ) (smoothConstant_le_minkowskiConstant hρ)`），无 `sorry` 字面出现，但两个被调用的引理仍是 `sorry`，因此 `#print axioms` 显示 `sorryAx`（见下）。 |
| `constant_eq_minkowskiConstant_intrinsic` | 未完成 | `Probability.coordinateEquiv`、`Probability.intrinsicMap`、`AffineIsometryEquiv.toIsometryEquiv`、`EMetric.infEDist_image`、`Metric.mem_thickening_iff_infEDist_lt` | 数学内容已理清（见代码内长注释：用 `coordinateEquiv μ` 的等距性证明 `e '' thickening r B' = thickening r (e '' B')`，用 `ProbabilityMeasure.toMeasure_map` + `Measure.map_map` 证明 `intrinsicMeasure μ = (carrierMeasure μ).map (coordinateEquiv μ).symm`，再把 `constant`/`minkowskiConstant` 的四层嵌套 `⨅` 沿双射 `B' ↦ coordinateEquiv μ '' B'` 重新索引），但完整形式化"沿双射重新索引一个四层嵌套 `⨅`"没有找到单个 Mathlib 组合子，需要逐层手写，受时间限制未完成。 |
| `constant_eq_smoothConstant_intrinsic` | **完成（粘合）** | `rw [constant_eq_minkowskiConstant_intrinsic, minkowskiConstant_eq_smoothConstant hρ]` | 同上，纯粘合，传递依赖 `sorryAx`。 |
| `inverseScale_eq_inv_smoothConstant_intrinsic` | **完成（粘合）** | `unfold inverseScale; rw [constant_eq_smoothConstant_intrinsic hμ hρ]` | 同上，纯粘合，传递依赖 `sorryAx`。 |

共 13 条真正 `sorry`-free（其证明项本身不含 `sorry`），其中 10 条是"叶子"（自身及其调用链都不含任何
`sorry`，`#print axioms` 只有 `propext`/`Classical.choice`/`Quot.sound`），3 条是组装引理（自身证明
`sorry`-free，但引用的其他引理仍是 `sorry`，故 `#print axioms` 会显示 `sorryAx`）。

### `RelativePerimeter.lean`（新增 1 条）

| 名称 | 状态 | 卡点 |
|---|---|---|
| `KLS.hausdorffNormalized_finrank_eq_volume` | 未完成 | 需要"等周直径不等式"（每个直径为 `d` 的集合 Lebesgue 测度 `≤ ω_n (d/2)^n`，等号只在球实现）以确定 Haar 唯一性给出的比例常数；检索确认当前 pinned Mathlib 快照中不存在 `isodiametric`/`isoperimetric` 标识符。已在代码内加注释写明卡点（含到 `Measure.addHaarMeasure_unique`/`InnerProductSpace.volume_ball` 的路线草图）。 |

## `-DwarningAsError=true` 编译结果

```
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/CheegerInfimum.lean
```

输出恰好 12 条 `error: declaration uses 'sorry'`，行号为
`87,112,448,462,472,485,500,512,520,533,540,566`，与上表中"未完成"的 12 条一一对应；**没有任何其他
警告/错误**（`unusedSectionVars`、`unusedVariables`、deprecated 引理等在填 sorry 过程中产生的警告均已
清理：加了 10 处 `omit [...] in`，把 `Set.mem_setOf_eq`/`Set.mem_diff` 换成 `Set.mem_ofPred_eq`/
`Set.mem_sdiff`，把两个未使用的假设 `hr`、`hμ` 改名为 `_hr`、`_hμ`）。

`lake build FunctionalInequalities.KLS.WIP.RelativePerimeter` 与
`lake build FunctionalInequalities.KLS.WIP.CheegerInfimum`（普通模式，不带 `-DwarningAsError`）均
`Build completed successfully`，分别只剩 5 条与 12 条 `declaration uses 'sorry'` 警告，无其他警告。

## `#print axioms` 结果

对 13 条 sorry-free 声明逐一执行 `#print axioms`：

- 以下 10 条只依赖 `[propext, Classical.choice, Quot.sound]`：
  `SmoothDomain.frontier_superlevel_subset`、
  `Isoperimetry.minkowskiConstant_eq_top_of_subsingleton`、
  `Isoperimetry.smoothConstant_eq_top_of_subsingleton`、
  `Isoperimetry.measure_closure_eq_of_minkowskiContent_ne_top`、
  `Isoperimetry.lintegral_measure_symmDiff_superlevel`、
  `Isoperimetry.min_measure_le_add_measure_symmDiff`、
  `Isoperimetry.tendsto_lintegral_min_superlevel`、
  `Isoperimetry.distanceCutoff_mem_Icc`、
  `Isoperimetry.lipschitzWith_distanceCutoff`、
  `Isoperimetry.distanceCutoff_eq_one_of_mem_closure`。
- 以下 3 条（组装/粘合引理，证明项本身 `sorry`-free）额外依赖 `sorryAx`（因为它们调用了仍是 `sorry` 的
  `minkowskiConstant_le_smoothConstant`、`smoothConstant_le_minkowskiConstant`、
  `constant_eq_minkowskiConstant_intrinsic`）：
  `Isoperimetry.minkowskiConstant_eq_smoothConstant`、
  `Isoperimetry.constant_eq_smoothConstant_intrinsic`、
  `Isoperimetry.inverseScale_eq_inv_smoothConstant_intrinsic`。
  **不应将这 3 条报告为"完全证完"**：它们的证明策略是对的、组装是正确的，但整条定理链条要到
  `minkowskiConstant_le_smoothConstant`、`smoothConstant_le_minkowskiConstant`、
  `constant_eq_minkowskiConstant_intrinsic` 三者都补完才算真正无 `sorry`。

## 陈述问题

1. **`distanceCutoff_eq_zero_of_notMem_thickening` 在 `B = ∅` 时为假。** 陈述：
   `∀ B r (hr : 0 < r) x, x ∉ Metric.thickening r B → distanceCutoff B r x = 0`。取 `B = ∅`：
   `Metric.thickening r ∅ = ∅`（`Metric.thickening_empty`），所以对任意 `x`，前提
   `x ∉ Metric.thickening r ∅` 恒真；但 `Metric.infDist x ∅ = 0`（Mathlib 对空集 `infDist` 的约定，
   `Metric.infDist_empty`），故 `distanceCutoff ∅ r x = max 0 (1 - 0/r) = max 0 1 = 1 ≠ 0`。命题对
   `B` 非空成立（此时 `x ∉ thickening r B ↔ r ≤ infDist x B`
   `Metric.mem_thickening_iff_infDist_lt` 取逆否，直接给出 `1 - infDist x B / r ≤ 0`），但陈述里没有
   `B.Nonempty` 前提，且规则 1 不允许为了让它能证而加前提。已保留 `sorry` 并在代码内写明反例。
2. **`tendsto_distanceCutoff_indicator` 缺 `MeasurableSet B`（或 `NullMeasurableSet B ν`）前提，
   一般情形下可能不可证。** 该引理需要对每个 `r`，被积函数
   `x ↦ ‖distanceCutoff B r x - B.indicator 1 x‖ₑ` 可测（以便使用控制收敛定理
   `tendsto_lintegral_filter_of_dominated_convergence`），而 `distanceCutoff B r` 连续（故 Borel 可
   测）、`B.indicator 1` 在 `B` 非 Borel 时一般不可测，两者之差也一般不可测。更本质的问题：证明思路
   依赖"`hcl : ν(closure B) = ν B` ⟹ `ν(closure B \ B) = 0`"，但对不可测 `B` 这一步不成立——取
   Vitali/Bernstein 型集合 `B ⊆ closure B`（例如 `closure B` 是一个闭球，`B` 与 `closure B \ B` 都是外
   测度等于 `ν(closure B)` 的不可测子集，这在经典 Bernstein 集构造中是标准操作）即可使
   `ν(closure B) = ν(B)`（外测度）成立而 `ν(closure B \ B)` 同时也取到满外测度（`≠ 0`）。命题对
   Borel（或 `ν`-零测完备化可测）的 `B` 成立，但陈述未加此前提。已保留 `sorry` 并在最终报告中说明。

## 环境

沿用当天早些时候诊断的 Command Line Tools / x86_64 lake 与 arm64 xcrun 不兼容问题；所有 `lake`/`lean`
调用均在 PATH 前插入一个仅 `exec` `/Library/Developer/CommandLineTools/usr/bin/git` 并显式设置
`GIT_EXEC_PATH`/`GIT_TEMPLATE_DIR` 的包装脚本目录下运行，未修改仓库内容。

## 未做 / 后续

- 未注册进 `research/tasks.json`、`research/a-series/ledger.yaml`；未改 Blueprint 的 `\lean{}`/
  `\leanok`；未 `git commit`、未 `git push`；未改 `FunctionalInequalities.lean`、`lakefile.toml`、
  `solutions/README.md` 等共享文件。
- 若日后有人继续：`constant_eq_minkowskiConstant_intrinsic` 的"沿双射重新索引嵌套 `⨅`"是下一个最值得
  投入的单点（一旦完成，`constant_eq_smoothConstant_intrinsic`、
  `inverseScale_eq_inv_smoothConstant_intrinsic` 就只再依赖
  `minkowskiConstant_eq_smoothConstant` 链）。`lintegral_minkowskiContent_superlevel_le`（ADG
  Lemma 3.2）和 Sard/coarea 两条是接下来工作量最大的三个节点，各自可能需要独立的大段开发。
