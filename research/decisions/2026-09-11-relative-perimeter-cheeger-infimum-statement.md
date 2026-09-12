# 2026-09-11 — `lem:relative-perimeter-cheeger-infimum`：陈述（仅陈述，无证明）

## 决定

- 为 Blueprint 附录 A 的 `lem:relative-perimeter-cheeger-infimum`（两种 Cheeger 下确界相等）写 Lean 陈述，并顺带写出
  `thm:klartag-density-frontend-identification` 的 `h_μ = h^{sm,rel}_ν`、`Ψ_KLS(μ) = ψ_ν` 两个子句。全部证明体为 `sorry`，
  放在独立 WIP 模块 `formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean`，导入同目录的
  `RelativePerimeter.lean`（其 olean 用 `lake build FunctionalInequalities.KLS.WIP.RelativePerimeter` 单模块构建，
  不进任何库根）。
- 坐标空间层定义：`KLS.Isoperimetry.minkowskiContent ν B`（开加厚的外 Minkowski 含量，`boundaryContent` 的坐标空间版）、
  `minkowskiConstant ν`（`h_M`）、`smoothConstant ρ Ω ν`（`h_S`，对 `SmoothDomain` 取下确界）。均以 `⨅` 定义，无可取集时为 `⊤`，
  与 `KLS.Isoperimetry.constant` 的零维约定一致。平衡量 `m(t) = min{t, 1−t}` 内联为 `min (ν B) (1 − ν B)`，与 `constant` 同写法。
- 主定理对"任意带 Borell 密度（相对 Lebesgue `volume`）的概率律"陈述，比 Blueprint 的"满维对数凹律"更强。
- 发现并修正了上一节点骨架的两处陈述错误（Hausdorff 归一化、参考测度须为 Lebesgue），见
  [平滑引理记录补记](2026-09-11-relative-perimeter-smoothing-statement.md)。
- 不填 sorry；不注册；不提交、不推送；不改共享文件。

## Lean 陈述（formech 风格）

主张：
1. `KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant (hρ : IsBorellDensity ν volume ρ) :
   minkowskiConstant ν = smoothConstant ρ (interior ν.support) ν` —— Blueprint 引理本体。
2. `constant_eq_minkowskiConstant_intrinsic (μ) : constant μ = minkowskiConstant (intrinsicMeasure μ)` —— 仿射支撑定义
   与坐标空间定义的传输（对任意 `μ`）。
3. `constant_eq_smoothConstant_intrinsic (hμ : LogConcave μ) (hρ : IsBorellDensity (intrinsicMeasure μ) volume ρ)`、
   `inverseScale_eq_inv_smoothConstant_intrinsic` —— `thm:klartag-density-frontend-identification` 的
   `h_μ = h^{sm,rel}_ν`、`Ψ_KLS = ψ_ν` 子句（Dirac 律两边为 `⊤`/`0`）。

不主张：单个集合的 `ν⁺(B)` 与 `P_ρ(B)` 的任何关系（Blueprint 原句"compares infima, not the two perimeters of each test
set"）、BV 周长、Cheeger–Buser、Poincaré 常数子句。

有限范围：无附加维数假设。`smoothConstant_mul_lintegral_min_superlevel_le` 依赖 Borell 密度前提（coarea 中要用密度）。

零维：无 `0 < ν B < 1` 的集合，两边 `⊤`（`minkowskiConstant_eq_top_of_subsingleton`、`smoothConstant_eq_top_of_subsingleton`）。

编译：`lake env lean FunctionalInequalities/KLS/WIP/CheegerInfimum.lean` 仅 25 条 `sorry` 警告，无其他警告。`#check`：
`minkowskiConstant` 只需 `NormedAddCommGroup`、`MeasurableSpace`；`smoothConstant` 与 `relativePerimeter` 一样只需到 `BorelSpace`；
定理带完整欧氏实例表。

## 逐句对齐（Blueprint ↔ Lean）

| Blueprint | Lean | 结论 |
|---|---|---|
| "For a full-dimensional log-concave probability" | `hρ : IsBorellDensity ν volume ρ`（对数凹律经 `exists_isBorellDensity` 得到；密度存在已蕴含满维） | 更强 |
| 左边 `inf_{0<ν(B)<1} ν⁺(B)/m(ν(B))` | `minkowskiConstant ν`；`minkowskiContent` 与 45 章 `def:isoperimetric-cheeger-scale` 的 `μ⁺`（开加厚、`liminf_{r↓0}`）逐字对应 | 一致 |
| 右边 `inf_{U smooth, 0<ν(U)<1} P_ρ(U)/m(ν(U))` | `smoothConstant ρ (interior ν.support) ν`，`P_ρ` 为修正后的 `relativePerimeter`（标准 `ℋ^{n−1}`，Lebesgue 密度） | 一致 |
| 45 章 `h_μ` 定义在仿射支撑上（`KLS.Isoperimetry.constant`） | `constant_eq_minkowskiConstant_intrinsic` | 一致（桥接为独立义务） |
| 证明："weighted coarea and Sard's theorem give `h_S ∫₀¹ m(ν{u>t}) dt ≤ ∫‖∇u‖dν`" | `SmoothDomain.ae_exists_superlevel`（Sard）、`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（加权 coarea）、`smoothConstant_mul_lintegral_min_superlevel_le` | 一致 |
| 证明："Minkowski coarea inequality `∫₀¹ ν⁺({u≥t}) dt ≤ ∫‖∇u‖dν`, Lemma 3.2 of ADG 2017" | `lintegral_minkowskiContent_superlevel_le`（对全体 `t ∈ ℝ`，闭超水平集，`C¹` Lipschitz `u`） | 更强（无需 `u ∈ [0,1]`） |
| "Open and closed superlevel sets have the same measure for a.e. t" | 吸收进 `minkowskiConstant_mul_lintegral_min_superlevel_le` | 一致 |
| "`∫₀¹ ν({u_j>t} ∆ B) dt = ‖u_j − 𝟙_B‖_{L¹(ν)} → 0`"，"Since m is 1-Lipschitz, the denominator integral tends to m(ν(B))" | `lintegral_measure_symmDiff_superlevel`、`min_measure_le_add_measure_symmDiff`、`tendsto_lintegral_min_superlevel` | 一致 |
| "Applying the smoothing lemma to a smooth U proves `h_M m(ν(U)) ≤ P_ρ(U)`, hence `h_M ≤ h_S`" | `minkowskiConstant_le_smoothConstant`（用 `RelativePerimeter.exists_smooth_recovery_sequence`） | 一致 |
| "Finiteness implies `ν(B̄) = ν(B)`" | `measure_closure_eq_of_minkowskiContent_ne_top` | 一致 |
| "`w_j = (1 − d(·,B)/r_j)₊` … converge in L¹(ν) to 𝟙_B, and `∫‖∇w_j‖dν ≤ (ν(B^{r_j}) − ν(B))/r_j`" | `distanceCutoff`、`distanceCutoff_mem_Icc`、`lipschitzWith_distanceCutoff`、`_eq_one_of_mem_closure`、`_eq_zero_of_notMem_thickening`、`tendsto_distanceCutoff_indicator`、`lintegral_enorm_gradient_distanceCutoff_le`（右边用 `ν(closure B)`） | 更强（分母用闭包） |
| "The bounded L¹ convolution assertion of lem:covariance-test-core-density gives smooth replacements preserving the limit of these gradient integrals" | `exists_smooth_approximation_lipschitz`（光滑、Lipschitz、`[0,1]` 值、`L¹(ν)` 收敛、梯度积分收敛） | 一致 |
| "Weighted coarea now yields `h_S m(ν(B)) ≤ ν⁺(B)` … proving `h_S ≤ h_M`" | `smoothConstant_le_minkowskiConstant` | 一致 |
| 45 章 `h_μ = h^{sm,rel}_ν`，`Ψ_KLS(μ) = ψ_ν` | `constant_eq_smoothConstant_intrinsic`、`inverseScale_eq_inv_smoothConstant_intrinsic` | 一致 |

## sorry 义务（25 条）

见同日提示词 [2026-09-11-relative-perimeter-cheeger-infimum-sorry-prompt.md](2026-09-11-relative-perimeter-cheeger-infimum-sorry-prompt.md)。分层：

- 纯 Mathlib 可证（13）：`frontier_superlevel_subset`、两条零维、`measure_closure_eq_of_minkowskiContent_ne_top`、
  `lintegral_measure_symmDiff_superlevel`、`min_measure_le_add_measure_symmDiff`、`tendsto_lintegral_min_superlevel`、
  `distanceCutoff` 四条性质、`tendsto_distanceCutoff_indicator`、`constant_eq_minkowskiConstant_intrinsic`（传输）。
- 中等（4）：`lintegral_enorm_gradient_distanceCutoff_le`（Rademacher + 水平集上梯度 a.e. 为零）、
  `exists_smooth_approximation_lipschitz`（磨光 + `WeakDerivative.lean` 的 Lipschitz 分部积分）、
  `lintegral_minkowskiContent_superlevel_le`（ADG Lemma 3.2 的初等证明）、`minkowskiConstant_mul_lintegral_min_superlevel_le`。
- 缺基础设施（3）：`SmoothDomain.ae_exists_superlevel`（`ℝⁿ → ℝ` 的 Sard 定理需 `C^n`；Mathlib 只有同维数版本）、
  `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（coarea 公式，Mathlib 只有面积公式）、以及依赖它们的
  `smoothConstant_mul_lintegral_min_superlevel_le`。
- 组装（5）：`minkowskiConstant_le_smoothConstant`（另需上一节点的 `exists_smooth_recovery_sequence`）、
  `smoothConstant_le_minkowskiConstant`、`minkowskiConstant_eq_smoothConstant`、`constant_eq_smoothConstant_intrinsic`、
  `inverseScale_eq_inv_smoothConstant_intrinsic`。

## 环境事件

今天 19:04 系统安装了 "Command Line Tools for Xcode 27.0"（仅 arm64）。`~/.elan` 的 lake/lean 是 x86_64（Rosetta），它们经
`/usr/bin/git` 垫片调用 git 时 `libxcrun` 缺 x86_64 切片而失败。19:1x 我的 `lake build`（此后第一次 lake 调用）在依赖重解析时
把读不到远端 URL 当作"URL 变了"，删除了 `.lake/packages/checkdecls`；此后**任何** `lake` 命令都会重复删除/克隆失败。
临时处理：用设置 `GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core` 后 `exec` CLT 真实 git 的包装脚本
置于 PATH 前端运行 lake，已恢复 checkdecls 并完成本次编译；包装脚本不在仓库内。持久修复需用户决定：把该包装目录加入
shell PATH，或改装原生 arm64 的 elan/工具链。

## 未做

- 未注册；未提交、未推送；未改共享文件。`lake build` 单模块构建只写入 `.lake/build`。
- 若日后转正：模块拆到 `KLS/Isoperimetry/{Minkowski,SmoothDomainInfimum}.lean`；`research/naming.md` 加入
  `KLS.Isoperimetry.{minkowskiContent,minkowskiConstant,smoothConstant,distanceCutoff}` 与 `KLS.{unitBallVolume,hausdorffNormalized,surfaceMeasure}`。
