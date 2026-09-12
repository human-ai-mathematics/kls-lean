# 2026-09-12 — `KLS/WIP/CheegerInfimum.lean`：再填一条 sorry 并修复两条错误陈述

承接 [2026-09-11 的证明记录](2026-09-11-relative-perimeter-cheeger-infimum-proofs.md)（25 条中 13 条已证，
12 条留 `sorry` 并逐条写明卡点）。本轮只动这一个 WIP 文件，未注册、未提交、未推送。

## 结果

`sorry` 从 12 条降到 **11 条**；文件在 `-DwarningAsError=true` 下无警告。

### 1. `constant_eq_minkowskiConstant_intrinsic` —— 已证

上一轮留 `sorry` 的理由是「沿双射重标号两个 `⨅` 的步骤没做完，需要一串对齐四层 binder 的 `iInf` congruence
引理，而不是单个 Mathlib 组合子」。本轮换了路线绕开这个困难：**全程用原像而不是像**。

- 新增私有引理 `thickening_preimage_of_isometry`：满射等距下 `thickening r (f ⁻¹' B) = f ⁻¹' thickening r B`
  （`Metric.infEDist_image` + `Set.image_preimage_eq`）。用原像而非像，避免了「像是否可测」的额外负担。
- 新增私有引理 `measurePreserving_coordinateEquiv`：
  `MeasurePreserving (coordinateEquiv μ) (intrinsicMeasure μ) (carrierMeasure μ)`，
  由 `intrinsicMap = (coordinateEquiv μ).symm ∘ retraction` 与 `Measure.map_map` 得到。
- 于是对每个可测 `B ⊆ affineSupport μ`，`minkowskiContent (intrinsicMeasure μ) (g ⁻¹' B) = boundaryContent μ B`
  与质量相等都是逐点改写；两个 `⨅` 的互相支配用 `le_iInf` + `iInf_le_of_le` 各写一次，
  取 `B' := g ⁻¹' B` 和 `B := g.symm ⁻¹' B'`，不需要任何重标号组合子。
- `finrank = 0` 分支由 `Module.finrank_zero_iff` 得 `Subsingleton`，再接既有的
  `minkowskiConstant_eq_top_of_subsingleton`。

签名未改。`CompleteSpace E` 在填了证明之后成为未用变量，按与
`ae_conditionalFiber_logConcave` 相同的处理，用逐声明的 `set_option linter.unusedSectionVars false in`
消除警告，而不是加 `omit`（加 `omit` 会改签名）。

### 2. 两条错误陈述：补可用版本，原陈述原样保留

上一轮记录里标注为「陈述问题」的两条，本轮**没有改它们的类型**（那是留给 owner 审阅的记录），
而是各补一条已证的修复版本，供下游使用：

| 原陈述（仍为 `sorry`） | 缺陷 | 新增的已证版本 |
|---|---|---|
| `distanceCutoff_eq_zero_of_notMem_thickening` | `B = ∅` 时**为假** | `distanceCutoff_eq_zero_of_notMem_thickening_of_nonempty`（加 `B.Nonempty`） |
| `tendsto_distanceCutoff_indicator` | 缺 `MeasurableSet B` | `tendsto_distanceCutoff_indicator_of_measurableSet`（加 `MeasurableSet B`） |

本轮独立复核了第一条的反例并确认上一轮的判断正确：`distanceCutoff B r x = max 0 (1 - infDist x B / r)`，
而 Mathlib 约定 `Metric.infDist x ∅ = 0`，故 `distanceCutoff ∅ r x = 1`；同时 `thickening r ∅ = ∅`
使前提空洞成立，结论 `1 = 0` 为假。另外确认该引理**在全仓库没有任何使用点**，所以将来 owner 决定
直接修正其类型不会破坏任何下游。

第二条的证明路线：逐点有 `‖w_r x − 1_B x‖ₑ ≤ (thickening r B \ B).indicator 1 x`（三分支：`x ∈ B`、
`x ∈ thickening r B \ B`、`x ∉ thickening r B`，第三支正是上面新增的修复版本），
积分得 `≤ ν(thickening r B) − ν B`；再由 `Metric.closure_eq_iInter_thickening` 与
`tendsto_measure_iInter_atTop` 沿半径 `1/(n+1)` 做上方连续性，配合 `hcl` 把它压到 0，
最后 `ENNReal.tendsto_nhds_zero` + 夹逼。

## 剩下的 11 条与卡点

均维持上一轮的判断，本轮复核后未发现可以绕开的：

- 缺 Mathlib 理论：`ae_exists_superlevel`（一般维数 Sard）、
  `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（coarea 公式）、
  `KLS.hausdorffNormalized_finrank_eq_volume`（等周直径不等式）。
- 需要成规模的分析工作：`lintegral_enorm_gradient_distanceCutoff_le`（Rademacher + 水平集上梯度 a.e. 为零）、
  `exists_smooth_approximation_lipschitz`（磨光后梯度积分的**收敛**，不只是界）、
  `lintegral_minkowskiContent_superlevel_le`（ADG 2017 Lemma 3.2；注意粗糙的全局 Lipschitz 估计只能给出
  `≤ K`，要得到 `≤ ∫‖∇u‖dν` 必须做局部 Lipschitz 常数的窄带论证）。
- 纯下游依赖：`smoothConstant_mul_lintegral_min_superlevel_le`、
  `minkowskiConstant_mul_lintegral_min_superlevel_le`、`minkowskiConstant_le_smoothConstant`、
  `smoothConstant_le_minkowskiConstant`。
- 保留作为缺陷记录：上表两条原陈述。

其余两个 WIP 文件本轮未动：`KLS/WIP/RelativePerimeter.lean`（5 条，卡在 C¹ 超曲面面积测度的局部有限性与
Gauss–Green）、`Energy/WIP/Cheeger.lean`（5 条，归约为 2 条奇异测度下的 AGS 型开放比较）。

## 检查

`lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/CheegerInfimum.lean`：
除 11 条 `declaration uses 'sorry'` 外无输出。该模块不在聚合导入中，不影响 `lake build` 与任何证书。

## 补充（同日，owner 指示）：两条缺陷陈述直接改正，不再保留假命题

owner 明确要求仓库中不保留假命题，故撤销上文「原陈述原样保留」的处理，改为**直接修正类型**：

- `distanceCutoff_eq_zero_of_notMem_thickening`：加 `(hB : B.Nonempty)`，证明即原先的修复版本，`sorry` 消除。
- `tendsto_distanceCutoff_indicator`：加 `(hBm : MeasurableSet B)`，证明即原先的修复版本，`sorry` 消除。

两条带后缀的临时版本（`..._of_nonempty`、`..._of_measurableSet`）随之删除，文件内唯一的引用点改指原名。
改动前已确认这两条在**全仓库没有任何外部使用点**，且 `KLS/WIP/CheegerInfimum.lean` 不被任何模块导入、
不在聚合导入、lakefile `Solutions` 根、ledger、`CERTIFICATES` 与 Blueprint `\lean{}` 中，
因此改类型不影响任何证书。

反例在改动前已用独立 Lean 文件机器证伪（`B = ∅`，`r = 1`，`x = 0`：前提因
`Metric.thickening 1 ∅ = ∅` 空洞成立，而 `Metric.infDist 0 ∅ = 0` 给出 `distanceCutoff ∅ 1 0 = 1`），
不是仅凭推理判定。

`sorry` 由 11 条降到 **9 条**；文件在 `-DwarningAsError=true` 下仍无警告。
另复核全仓库：`.lean` 文件中已无任何标注陈述缺陷的注释（`STATEMENT ISSUE` 等），
决定记录中记载过的陈述问题仅此两处，均已修正。
