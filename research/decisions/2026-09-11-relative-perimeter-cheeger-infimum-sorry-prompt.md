# 2026-09-11 — 交给证明会话的提示词：填 `KLS/WIP/CheegerInfimum.lean` 的 sorry

复制下方代码块给证明会话。前置说明：`KLS/WIP/RelativePerimeter.lean` 已于今晚修正两处陈述
（见 [平滑引理记录补记](2026-09-11-relative-perimeter-smoothing-statement.md)），其 13 条已证明未受影响；
本提示词的第 0 层先处理该文件的新义务。

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交 db584cd6d46c92f209a44c0f1c829460d327499d；
Lake 根目录 formalization/）。

环境注意：这台机器今天更新了 Command Line Tools（仅 arm64），而 ~/.elan 的 lake 是 x86_64，lake 调 git 会失败并删除
.lake/packages/checkdecls。运行任何 lake 命令前，把一个名为 git 的包装脚本目录放到 PATH 前端，脚本内容：
    #!/bin/sh
    export GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core
    export GIT_TEMPLATE_DIR=/Library/Developer/CommandLineTools/usr/share/git-core/templates
    exec /Library/Developer/CommandLineTools/usr/bin/git "$@"
若 .lake/packages/checkdecls 缺失，带包装的 lake 会自动按 manifest 重新克隆。

任务：填写 formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean 中的 sorry（25 条），并补
formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean 新增的 1 条（hausdorffNormalized_finrank_eq_volume，见第 0 层）。
CheegerInfimum 是 Blueprint lem:relative-perimeter-cheeger-infimum（formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex）
及 thm:klartag-density-frontend-identification（45 章）中 h_μ = h^{sm,rel}_ν 子句的陈述骨架；设计与逐句对齐见
research/decisions/2026-09-11-relative-perimeter-cheeger-infimum-statement.md。先读这些文件与目标 .lean 的模块文档。

规则：
1. 不改任何 theorem/def 的陈述（类型）。若确认某陈述为假或不可证，保留 sorry 并在报告中说明反例/障碍。
   允许加 private 辅助引理与 import。
2. 命名遵守 research/naming.md。
3. 只在两个 WIP 文件内工作。不加入 FunctionalInequalities.lean、lakefile Solutions 根、research/a-series/ledger.yaml、
   research/check_blueprint.py、research/tasks.json、Blueprint \lean{}/\leanok。不 git commit、不 git push。
   决定记录只追加：新建 research/decisions/2026-09-1X-relative-perimeter-cheeger-infimum-proofs.md。
4. 编译（在 formalization/ 下，PATH 已含包装 git）：
     lake build FunctionalInequalities.KLS.WIP.RelativePerimeter      # CheegerInfimum 导入它，改动后需重建 olean
     lake env lean FunctionalInequalities/KLS/WIP/CheegerInfimum.lean
   目标：无错误，填完的声明不再有 "declaration uses 'sorry'"，无 unusedSectionVars 等其他警告（用 omit/include ... in）。
   收尾用 -DwarningAsError=true 编译，并对填完的顶层定理 #print axioms，只允许 propext / Classical.choice / Quot.sound。
5. 语法：`∞` 需 `open scoped ContDiff`；`∆` 需 `open scoped symmDiff`；`μH[d]` 需 `open MeasureTheory`；`volume` 来自
   `measureSpaceOfInnerProductSpace`（Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean）；`push_neg` 已废弃用 `push Not`。

按层做，先易后难；卡住的留 sorry 并写明卡点。

第 0 层（RelativePerimeter.lean 新义务；难，可留）
- KLS.hausdorffNormalized_finrank_eq_volume：`(ω_n/2^n) • μH[n] = volume` 于欧氏 V。这是等周直径不等式
  （每个集合的 Lebesgue 测度 ≤ ω_n (diam/2)^n）加 Mathlib 缺失的 `μH[n]` 与 `volume` 的比较。
  Mathlib 有 `hausdorffMeasure_pi_real`（sup 范数）、`Measure.addHaar` 唯一性（`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`
  / `Measure.addHaarMeasure_unique`）：可先证 `μH[n]` 是平移不变的局部有限正测度 ⇒ `μH[n] = c • volume`，再由
  `InnerProductSpace.volume_ball`（Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean）与球的 `μH[n]`（这一步需要
  等周直径不等式，Mathlib 无）确定 c。做不动就留 sorry，写明缺等周直径不等式。

第一层（纯 Mathlib，应全部完成）
- SmoothDomain.frontier_superlevel_subset：`frontier_subset_closure`、`closure_lt_subset_le`（`{t<u} ⊆ closure ⊆ {t ≤ u}`）
  与 `interior` 含开集 `{t<u}`（`isOpen_lt continuous_const hu`）：边界点满足 `t ≤ u x` 且不在开集内 ⇒ `u x = t`。
- minkowskiConstant_eq_top_of_subsingleton / smoothConstant_eq_top_of_subsingleton：一点空间上 `ν B ∈ {0,1}`
  （`Set.eq_empty_or_univ`/`Subsingleton.set_cases`），前提矛盾，`iInf` 空 ⇒ `⊤`（`iInf_eq_top`、`ENNReal.iInf_eq_top`）。
- measure_closure_eq_of_minkowskiContent_ne_top：`closure B ⊆ thickening r B`（`self_subset_thickening`/`closure_subset_thickening`，
  r > 0）给 `ν(closure B) − ν B ≤ ν(B^r) − ν B`；若 `ν(closure B) > ν B` 则差值 `δ > 0` 使 `(ν(B^r) − ν B)/r ≥ δ/r → ⊤`，
  与 `liminf ≠ ⊤` 矛盾（`Filter.liminf_eq_top`/`le_liminf_of_le`，`ENNReal.div_eq_top`，`tendsto_inv_zero_atTop`）。
- lintegral_measure_symmDiff_superlevel：对 `x` 固定，`{t ∈ (0,1) : x ∈ {t<u} ∆ B}` 是 `Ioo 0 1 ∩ Ico (u x) 1`（x ∈ B）
  或 `Ioo 0 (u x)`（x ∉ B），一维长度即 `|u x − 𝟙_B x|`；用 `lintegral_lintegral_swap`（可测性：`measurableSet_lt`、
  `MeasurableSet.symmDiff`）把 `∫⁻ t, ν(...) = ∫⁻ t ∫⁻ x 𝟙 = ∫⁻ x ∫⁻ t 𝟙`，再 `Real.volume_Ioo`/`Real.volume_Ico`、
  `Real.enorm_eq_ofReal_abs`。
- min_measure_le_add_measure_symmDiff：`ν A ≤ ν B + ν(A ∆ B)`（`measure_le_measure_union_symmDiff`?：用 `A ⊆ B ∪ (A ∆ B)` +
  `measure_union_le`）与对称式，再 `min_le_min`、`tsub_le_iff_right`，注意 ENNReal 中 `1 − ν A`。
- tendsto_lintegral_min_superlevel：由上一条逐 `t` 有 `|min(ν{u_j>t}) − min(ν B)| ≤ ν({u_j>t} ∆ B)`，积分后用
  `lintegral_measure_symmDiff_superlevel` 得两边差 ≤ `∫⁻ ‖u_j − 𝟙_B‖ₑ → 0`；`ENNReal.Tendsto` 用夹逼
  （`tendsto_of_tendsto_of_tendsto_of_le_of_le'` 或 `ENNReal.tendsto_nhds` 的 ε 形式）。注意 `∫⁻ t in Ioo 0 1, min(...)` ≤ 1 有限。
- distanceCutoff_mem_Icc：`le_max_left`、`max_le`、`Metric.infDist_nonneg`、`div_nonneg`。
- lipschitzWith_distanceCutoff：`Metric.lipschitz_infDist_pt`（常数 1），`LipschitzWith.const_max`/`LipschitzWith.max_const`、
  `LipschitzWith.const_sub`、`LipschitzWith.const_mul`/`div` 的组合；常数 `Real.toNNReal r⁻¹`。
- distanceCutoff_eq_one_of_mem_closure：`Metric.mem_closure_iff_infDist_zero hB`，`div_zero`。
- distanceCutoff_eq_zero_of_notMem_thickening：`Metric.mem_thickening_iff_infDist_lt`（需 B 非空；空集时 `thickening r ∅ = ∅`，
  `infDist x ∅ = 0`，此时结论为假？——检查：B = ∅ 时 `distanceCutoff ∅ r x = max 0 (1 − 0) = 1 ≠ 0`，而 `x ∉ thickening r ∅` 成立。
  **该陈述在 B = ∅ 时为假**：报告时指出，留 sorry；或建议补前提 `hB : B.Nonempty`（不要自行改陈述）。
- tendsto_distanceCutoff_indicator：`tendsto_lintegral_filter_of_dominated_convergence`（控制 1，`𝓝[>] 0` 可数生成），
  逐点：`x ∈ closure B` ⇒ 值恒 1；`x ∉ closure B` ⇒ `infDist x B > 0`（`Metric.infDist_pos_iff_notMem_closure hB`），
  `r < infDist` 时值 0；`hcl` 把 `closure B \ B` 化为 `ν`-零测（`measure_diff_null`/`ae`）。
- constant_eq_minkowskiConstant_intrinsic：展开 `KLS.Isoperimetry.constant` 的 `if`：`finrank = 0` ↔ 方向空间 `Subsingleton`
  ↔ `minkowskiConstant = ⊤`（零维引理）；否则 `⨅` 换元：`B ↦ intrinsicMap μ '' B`（或用 `retraction`/`coordinateEquiv` 的
  `AffineIsometryEquiv`），`carrierMeasure μ = intrinsicMeasure μ` 沿等距推前（`Probability.measurePreserving_intrinsicMap`、
  `Probability.coe_retraction_ae`），等距保 `thickening`（`IsometryEquiv.image_thickening` 或 `Metric.thickening` 的 `infDist`
  刻画 + `Isometry.infDist_image`?），`boundaryContent` 与 `minkowskiContent` 逐项相等。这是本层最长的一条。

第二层（Mathlib + 仓库输入，应能完成）
- lintegral_enorm_gradient_distanceCutoff_le：Rademacher `LipschitzWith.ae_differentiableAt`（Mathlib/Analysis/Calculus/Rademacher.lean）
  对 `m`，经 `hac` 转到 `ν`-a.e.；在开集 `thickening r B \ closure B` 上 `‖∇w‖ ≤ 1/r`
  （`LipschitzWith.norm_fderiv_le`/`norm_gradient_le_of_lipschitz`，仓库 `Energy.Euclidean.LipschitzApproximation.norm_gradient_le_of_lipschitz`）；
  在开集 `(closure B)ᶜ ∩ (thickening r B)ᶜ`（值恒 0）与 `interior (closure B)`（值恒 1）上 `∇w = 0`；剩余
  `frontier (closure B) ∪ frontier (thickening r B)` 上需要"Lipschitz 函数在水平集上梯度 a.e. 为零"：
  可用 `w` 在 `{w = 1}` 上 a.e. 可微点的导数为 0 的论证（可微点 x ∈ {w=c} 若为该集合的密度点则 ∇w x = 0；Lebesgue 密度定理
  `Besicovitch.ae_tendsto_measure_inter_div` 或 `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`）；或绕开：
  用 `lintegral_mono` + 分块 `lintegral_union`，把 `thickening r B \ closure B` 外的贡献按 a.e. 为零处理。
- exists_smooth_approximation_lipschitz：`u_j := LipschitzApproximation.mollify m (radius j) w`
  （FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean：`contDiff_mollify`、`lipschitzWith_mollify`、
  `mollify_le`/`le_mollify` 给 `[0,1]`、`norm_mollify_sub_le` 给一致收敛 ⇒ `L¹(ν)` 收敛）；梯度：`∇(mollify) = mollify(∇w)`
  经 `Energy.Euclidean.WeakDerivative.integral_mul_inner_gradient`（Lipschitz 分部积分）或直接对 `mollify_apply` 微分
  + `hasFDerivAt_kernel`；`mollify(∇w) → ∇w` m-a.e.（`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` 或
  Lebesgue 点论证），有界 `K`，`ν` 有限 ⇒ `tendsto_lintegral_of_dominated_convergence`。
- lintegral_minkowskiContent_superlevel_le（ADG 2017 Lemma 3.2）：对 `r > 0`，`x ∈ thickening r {u ≥ t}` ⇒ ∃ y, `u y ≥ t`,
  `dist x y < r` ⇒ `u x ≥ t − r·Lip_{B(x,r)}(u)`；Fubini：`∫ (ν({u≥t}^r) − ν({u≥t})) dt ≤ ∫ ν{t − r L_r(x) ≤ u < t} dt
  = ∫ r L_r(x) dν(x)`，其中 `L_r(x) = sup_{B(x,r)} ‖∇u‖`（`C¹` ⇒ 连续 ⇒ `L_r → ‖∇u‖` 逐点递减，单调收敛
  `lintegral_tendsto_of_tendsto_of_antitone`）；再 `liminf` 与积分交换用 Fatou `lintegral_liminf_le`。
- minkowskiConstant_mul_lintegral_min_superlevel_le：`{u>t} ⊆ {u≥t}`，`ν{u = t} = 0` 除可数个 `t`
  （`Measure.countable_meas_level_set_pos`/`Measure.finite_meas_level_set_pos`）⇒ 两者 a.e. 同测；对每个 `t` 有 `0<ν<1` 时
  `minkowskiConstant ν ≤ ν⁺({u≥t})/min(...)`（`iInf_le`），乘回、`lintegral_mono` 后接上一条。

第三层（缺基础设施，尽力而为）
- SmoothDomain.ae_exists_superlevel（Sard）：对 `t` 正则值（`∀ x, u x = t → fderiv ℝ u x ≠ 0`），`U := {t<u}` 开，
  定义函数 `φ := u − t`，`W := {x | fderiv ℝ u x ≠ 0}`（开，`ContDiff.continuous_fderiv`），`frontier_superlevel_subset` 给
  边界点 ∈ `{u = t} ⊆ W`，`{t<u} ∩ W = {φ<0} ∩ W` 显然。剩下"临界值集 `u '' {fderiv = 0}` Lebesgue 零测"即 Sard；
  Mathlib 只有同维数版本 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`（Mathlib/MeasureTheory/Function/Jacobian.lean）。
  `n = 1` 时可直接用它；一般 `n` 需 Sard 定理（`C^n` 情形），Mathlib 无——留 sorry 写明。
- lintegral_enorm_gradient_mul_eq_lintegral_levelSet（coarea）：Mathlib 有面积公式 `lintegral_image_eq_lintegral_abs_det_fderiv_mul`
  （同维数），无 coarea。局部路线：在 `‖∇u‖ ≠ 0` 的开集上用隐函数把 `u` 局部拉直为坐标投影（`HasStrictFDerivAt.implicitFunction`），
  面积公式 + Fubini 得局部 coarea；`{∇u = 0}` 上左边为 0、右边由 Sard 为 0。这是本节点最重的义务。
- smoothConstant_mul_lintegral_min_superlevel_le：给定上两条：coarea 取 `g := ofReal ∘ ρ`（`hρ.withDensity_eq` 把
  `∫‖∇u‖dν` 化为 `∫‖∇u‖ ρ dvolume`），对 a.e. `t`：`{t<u}` 为光滑区域（Sard）、`frontier ⊆ {u=t}`（`frontier_superlevel_subset`）
  ⇒ `relativePerimeter ρ Ω {t<u} ≤ ∫_{u=t} ρ dsurfaceMeasure`；`0<ν{t<u}<1` 时 `smoothConstant ≤ P/min`（`iInf_le`），否则
  `min = 0`；`lintegral_mono_ae` + `ENNReal.mul_le_of_le_div'`。

第四层（组装）
- minkowskiConstant_le_smoothConstant：对每个可取 `U`：`RelativePerimeter.exists_smooth_recovery_sequence hρ U hU`
  给 `u_j`；`minkowskiConstant_mul_lintegral_min_superlevel_le` 对每个 `u_j`（`ContDiff ℝ ∞ → ℝ 1` 用 `.of_le le_top`）；
  `tendsto_lintegral_min_superlevel` 给左边趋于 `h_M · min(ν U)`；右边 `limsup ≤ P_ρ(U)`；`le_of_tendsto_of_tendsto'` +
  `ENNReal.Tendsto.const_mul`；再 `le_iInf` + `ENNReal.le_div_iff_mul_le`（`min ≠ 0`, `≠ ⊤`）。若 `P_ρ(U) = ⊤` 平凡。
- smoothConstant_le_minkowskiConstant：对每个可取 Borel `B`（`minkowskiContent ν B = ⊤` 平凡）：`measure_closure_eq_...`，
  取 `r_j → 0` 实现 `liminf`（`Filter.exists_seq_tendsto_liminf`? 或 `Filter.liminf` 的 `frequently` 刻画 +
  `exists_seq_tendsto_sInf`），`w_j := distanceCutoff B r_j`，`lintegral_enorm_gradient_distanceCutoff_le`
  （`hac := hρ.withDensity_eq ▸ withDensity_absolutelyContinuous`），`exists_smooth_approximation_lipschitz` 得光滑替代
  `u_{j,k}`，对角化；`smoothConstant_mul_lintegral_min_superlevel_le`；`tendsto_distanceCutoff_indicator` +
  `tendsto_lintegral_min_superlevel`；`hB.Nonempty` 由 `0 < ν B`。
- minkowskiConstant_eq_smoothConstant：`le_antisymm`。
- constant_eq_smoothConstant_intrinsic：`constant_eq_minkowskiConstant_intrinsic` + `minkowskiConstant_eq_smoothConstant hρ`
  于 `V := (affineSupport μ).direction`（实例：`Submodule` 上的 `InnerProductSpace`、`Subtype.borelSpace` 等，`hμ` 只用于文档一致性，
  可 `omit`；若 linter 报未用，需在陈述前加 `include hμ in`——不要改类型）。
- inverseScale_eq_inv_smoothConstant_intrinsic：`unfold inverseScale` + 上一条。

报告格式：每条义务一行：名称 | 完成/未完成 | 关键 API | 卡点。给出 `-DwarningAsError=true` 编译摘要与 `#print axioms` 结果。
不要声称未编译通过的内容已完成。若发现某条陈述为假（如 `distanceCutoff_eq_zero_of_notMem_thickening` 的 `B = ∅`），
在报告中单列"陈述问题"。
```
