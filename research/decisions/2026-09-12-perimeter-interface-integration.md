# 2026-09-12 — 周长链已有证明接入与模块依赖拆分

Owner 要求接通三处数学输入已经存在、只差依赖方向的接口，并解除这三处的"保留 sorry"限制；
其他开放证明保持原状。本轮不提交、不推送。承接
[当前状态审计](2026-09-12-status-audit-and-wip-retention.md)、
[外法向接口收尾](2026-09-12-outward-normal-interfaces-closeout.md)与
[CI 重放范围与路线复核](2026-09-12-ci-replay-scope-and-route-audit.md)；那三份记录保持为各自
日期的历史快照，其中的计数不因本轮改写。

## 模块依赖拆分

`AnalyticPrerequisites` 为 `mollifiedIndicator` 导入 `RelativePerimeter`，因此无法反向 import
把已证的通用几何接回周长层。实际依赖检查显示：原 A 段（Prékopa–Leindler、Brunn–Minkowski、
等周直径、Hausdorff 归一化）和 B 段（正则水平集的 Lipschitz 图与 `μH[n−1]` 有限性）在
`RelativePerimeter` 中只用到 `KLS.unitBallVolume` 一个符号，与 `SmoothDomain`、相对周长、
恢复序列都无关。据此做最小拆分：

| 层 | 模块 | 内容 | hole |
| --- | --- | --- | ---: |
| 基础定义 | `KLS/Geometry/SurfaceMeasure.lean`（新） | `unitBallVolume`、`hausdorffNormalized`、`surfaceMeasure`，只有定义 | 0 |
| 通用几何 | `Analysis/LevelSet.lean`（新） | 原 A、B 两段逐字迁入，命名、命名空间、陈述不变 | 0 |
| 周长应用 | `KLS/WIP/RelativePerimeter.lean` | `SmoothDomain`、相对周长、恢复序列；导入上面两层 | 3 |
| 未完成 WIP | `KLS/WIP/AnalyticPrerequisites.lean` | 仅剩 Gauss–Green、coarea、Sard；仍导入 `RelativePerimeter` | 5 |

迁移是移动而非复制：没有新增兼容别名，没有重复证明，没有保留转发声明。所有消费者已迁移
（`AnalyticPrerequisites` 的 C 段引用改指 `Analysis.exists_hausdorffMeasure_levelSet_lt_top`）。
新增的 `FunctionalInequalities/Analysis/` 目录的规则是：KLS 无关的几何分析，不得含 `sorry`。
正式聚合入口和 24 个证书都不导入这四个模块中的任何一个，本轮没有改动库根或证书 import。

## 三个目标

1. `KLS.hausdorffNormalized_finrank_eq_volume`（`RelativePerimeter.lean`）。
   由 `Analysis.hausdorffMeasure_finrank_eq_smul_volume` 给出 `μH[n] = (2^n/ω_n) • volume`，
   而 `hausdorffNormalized` 的因子 `ω_n/2^n` 正是它的逆；`ω_n = √π^n / Γ(n/2+1) > 0` 对一切
   维数成立，所以两个 `ENNReal.ofReal` 相乘为 `1`。零维不需要单独分支：通用引理自身已按
   `Subsingleton V` 讨论，且 `ω_0 = 1`，两边都是单点上的单位质量。归一化常数与零维情形都由
   独立客户端另行核对（见下）。

2. `KLS.SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`（`RelativePerimeter.lean`）。
   逐个定义邻域使用已证的点态正则水平集有限性：在定义邻域 `W` 内，`frontier U ∩ W = {φ = 0} ∩ W`
   （已有的 `frontier_inter_eq`），而 `φ` 在 `W` 上导数非零，于是
   `Analysis.exists_hausdorffMeasure_levelSet_lt_top` 给出一个测度有限的邻域；边界外的点用闭集
   `frontier U` 的补作为零测邻域。**无界区域仍在范围内**，边界总测度可以是无穷，没有增加任何
   有限性假设。零维时光滑区域的边界为空，只走第二个分支。
   证明未使用 `CompleteSpace V` 与 `SecondCountableTopology V`（二者都由 `FiniteDimensional ℝ V`
   导出），按本文件既有写法用 `omit ... in` 去掉，而不是新增 linter 抑制；这不削弱结论。

3. `KLS.Isoperimetry.exists_smooth_approximation_lipschitz`（`CheegerInfimum.lean`）。
   由正式库的 `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`（`a = 0`、`b = 1`）
   给出光滑、保持 `[0,1]`、保持同一全局 Lipschitz 常数 `K` 的逼近列，以及函数与梯度在 `L¹(ν)`
   的收敛。梯度那一项正是所需：把两侧实现到 `Lp V 1 ν`，用 `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`
   得到 `Lp` 收敛，再由 `Filter.Tendsto.enorm`、`Lp.enorm_toLp` 和 `eLpNorm_one_eq_lintegral_enorm`
   得到 `∫⁻‖∇u_j‖ₑ → ∫⁻‖∇w‖ₑ`。`[0,1]` 范围、光滑性、全局 Lipschitz 性与原有测度假设
   （`m` 为 Haar、`ν ≪ m`）全部保留，陈述未改。该证明未使用 `SecondCountableTopology V`，同样用
   `omit` 处理。

没有新增公理，没有隐藏 `sorry`，没有削弱结论、增加实质假设或缩小数学范围；三条陈述的类型与
接入前逐字相同（除上述两处可由 `FiniteDimensional` 导出的冗余实例绑定）。

## 范围边界

本轮**没有**证明 Gauss–Green（C1/C2）、coarea、Sard、恢复序列，也没有证明一般奇异测度的
Cheeger 比较，没有启动其他 KLS 路线。三个接口完成**不**意味着整条周长链已证：
`lem:relative-perimeter-smoothing` 与 `lem:relative-perimeter-cheeger-infimum` 的 task
基础设施状态保持 `missing` / `unchecked`，没有新增 ledger 节点，没有 Blueprint `\lean`/`\leanok`
锚点，证书数仍是 24。

WIP 直接 hole 由 24 降至 21：`RelativePerimeter` 5 → 3，`CheegerInfimum` 9 → 8，
`AnalyticPrerequisites` 5 不变，`Energy/WIP/Cheeger` 5 不变。hole 数不等于独立数学难题数。

## 验证

- **独立客户端**：`build/audit/PerimeterInterfaceAudit.lean`（在忽略目录中，用
  `lake env lean` 直接 elaborate，不进 `lake build`、不进重放集合、不进认证闭包）。五条客户端
  定理都是目标的**推论**而非复述：单位球上的归一化常数 `ℋ^n(B(0,1)) = ω_n`、零维的
  `ℋ^0(univ) = 1`、光滑边界任一紧片测度有限（含闭球片，覆盖无界边界）、以及由两条极限
  同时取出的单个 `ε`-逼近函数。五条的传递公理都只有
  `propext / Classical.choice / Quot.sound`，没有 `sorryAx`。
- **直接公理检查**：三个目标本身以及迁移后的
  `Analysis.hausdorffMeasure_finrank_eq_smul_volume`、`exists_hausdorffMeasure_levelSet_lt_top`、
  `exists_lipschitzOnWith_levelSet_subset_image`、`isodiametric`、`prekopaLeindler`、
  `volume_le_ofReal_mul_hausdorffMeasure`、两条 Brunn–Minkowski 与
  `exists_smooth_bounded_L1`，传递公理均只有标准三条。
- **严格模式**：`KLS/Geometry/SurfaceMeasure.lean`、`Analysis/LevelSet.lean` 与审计客户端在
  `lake env lean -DwarningAsError=true` 下退出 0。对照组：同一命令对
  `KLS/WIP/RelativePerimeter.lean` 退出 1 并把 3 条 `declaration uses sorry` 升级为 error，
  证明该选项确实生效。
- **含 hole 的 WIP**：四个文件在普通模式下实际重新 elaborate，退出 0，诊断恰好是预期的
  3 / 5 / 8 / 5 条 `declaration uses sorry`，没有其他警告或错误。**这不是严格模式通过**，
  不能作为无 hole 的证据。
- 完成默认 `lake build`，并从仓库根运行 `python3 research/verify.py`；最终回执由
  `build/verification/latest.json` 指向，与本轮最终源码快照匹配。

所有证据都信任固定版本的第三方编译依赖，不代表独立从零重建 Mathlib、远端 CI 或 Blueprint
排版通过。审计脚本与日志留在忽略的 `build/`。本轮按 owner 要求不提交、不推送。
