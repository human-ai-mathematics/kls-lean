# KLS 文件导航

本目录组织 KLS 目标使用的定义、对数凹工具和具体路线对象。数学来源写在各 Lean 模块开头；
证明状态由[ledger](../../../research/a-series/ledger.yaml)与当前声明、证明共同记录。

## 阅读入口

| 文件或目录 | 职责与边界 |
| --- | --- |
| [Definitions.lean](Definitions.lean) | 紧集对数凹定义、局部斜率、文献测试域和常数；共享定义入口 |
| [Statement.lean](Statement.lean) | 协方差归一化的 KLS 猜想命题；没有 KLS 证明 |
| [LogConcave/](LogConcave/README.md) | 对数凹传输、紧集/Borel 等价、内禀绝对连续性、Borell 密度表示、仿射协方差常数的对数凹契约与闭形式、环境平移下的对数凹性与重心、KLS 的仿射/各向同性归约、实轴上的一维 `4·Var` Poincaré 界（`LogConcave/Line/`，Bobkov 的 `12·Var` 作为推论保留） |
| [Gradient.lean](Gradient.lean) | 局部斜率与梯度关系，以及绝对连续性前提下的能量和测试域识别；已证明 |
| [Isotropic.lean](Isotropic.lean) | 有限二阶矩、零均值和单位协方差的定义；白化在 `Probability/CovarianceWhitening.lean`，仿射/各向同性归约在 `LogConcave/Isotropic.lean` |
| [Isoperimetry.lean](Isoperimetry.lean) | 仿射载体上的边界含量、等周常数及逆尺度定义；不提供 Cheeger 比较 |
| [ConditionalFiber.lean](ConditionalFiber.lean) | 条件纤维能量的构造及六条已证明的良定义性契约；本文件不提供闭性、Markov 性或框架界 |
| [ConditionalFiber/Closed.lean](ConditionalFiber/Closed.lean) | 条件纤维形式的两点跳跃表示、两点测度的交换不变性、Lipschitz 界 `d·L²`、稠密定义域、下半连续与 Markov 性，合成 `Energy.Dirichlet`；对任意 Borel 律与方向律成立，不提供与梯度能量的比较或框架界 |
| [ConditionalFiber/EnergyComparison.lean](ConditionalFiber/EnergyComparison.lean) | 纤维 Poincaré 输入 `FiberBound μ ρ κ` 下，条件纤维能量与局部斜率（梯度）能量的比较 `energy_le_of_fiberBound`（`D_{μ,ρ}(f) ≤ κ·∫‖∇f‖²`，有限）及形式差界 `C` 到 `C_P^lit(μ) ≤ κC` 的传递 `literatureConstant_le_of_fiberBound`；要求 `μ ≪ Haar` 与可容许框架，不固定 `κ` 的取值，不提供纤维对数凹性或框架界 |
| [ConditionalFiber/SliceKernel.lean](ConditionalFiber/SliceKernel.lean) | 给定 Haar 密度 `p` 时沿直线的显式切片核 `sliceKernel`（密度 `t ↦ p(z+tθ)/Z(θ,z)`，坏基点取狄拉克律）；`compProd_baseLaw_sliceKernel`（`baseLaw ⊗ₘ sliceKernel = jointLaw`）与 `ae_sliceKernel_eq`（与所选条件核几乎处处相等）；不假设对数凹，只要一个 Haar 密度 |
| [LogConcave/ConditionalFiber.lean](LogConcave/ConditionalFiber.lean) | 全维对数凹律的条件纤维几乎处处对数凹 `ae_conditionalFiber_logConcave`，由此得 `FiberBound μ ρ 4`、`D_{μ,ρ}(f) ≤ 4·∫‖∇f‖²` 与 `C_P^lit(μ) ≤ 4C`（Blueprint 的 `12` 版本带 `_of_four` 后缀保留）；不提供框架界，`q:conditional-fiber-frame` 仍开放 |
| [WIP/](WIP/) | **未注册**、不进聚合导入的进行中模块，任何证书都不依赖它们：`RelativePerimeter.lean`（光滑区域 `SmoothDomain`、归一化面积测度 `surfaceMeasure`、相对周长与 `lem:relative-perimeter-smoothing` 的骨架，5 条 `sorry`）、`CheegerInfimum.lean`（两种 Cheeger 下确界相等的骨架，9 条 `sorry`）、`AnalyticPrerequisites.lean`（上述两文件所缺分析前提的 KLS 无关陈述：等周直径不等式经 Brunn–Minkowski、正则水平集的 Lipschitz 图与 `μH[n−1]` 局部有限、光滑区域的 Gauss–Green、加权 coarea、Sard；5 条 `sorry`；Prékopa–Leindler、Brunn–Minkowski、等周直径、Hausdorff 归一化和正则水平集局部有限性已有证明，Gauss–Green、coarea、Sard 仍待完成）。记录见 `research/decisions/2026-09-1{1,2}-relative-perimeter-*.md` |

三个 KLS WIP 文件共 19 个直接 `sorry`，另有 `Energy/WIP/Cheeger.lean` 的 5 个；本轮按 owner
要求全部保留。部分完整证明体仍传递依赖 `sorryAx`。已有几何输入尚未接入不等于仍需新数学，
详见[当前审计与保留策略](../../../research/decisions/2026-09-12-status-audit-and-wip-retention.md)。

先读 `Definitions` 和 `Statement` 确定目标；对数凹分析沿子目录的阅读顺序展开。
文献常数比较的结论位于
[KLS/LogConcave/Poincare.lean](../KLS/LogConcave/Poincare.lean)，
完整使用说明见[Poincaré 比较指南](../Poincare/Euclidean/README.md)。

## 文件放置

对数凹性质及其表示定理放在 `LogConcave/`；共享目标定义和其余路线对象保留在本层。
`LogConcave` 谓词目前仍定义在 `Definitions.lean`，子目录直接导入该定义。
目录名不表示证明完成；每个节点的证明状态以 ledger 与证书为准，不能从根模块编译成功推断。

声明命名空间继续使用 `FunctionalInequalities.KLS`，模块路径按主题组织。
后续文件按数学职责放置，证明完成不触发文件移动。旧路径与新路径的对应关系见
[迁移记录](../../../research/explorations/2026-09-07-logconcave-module-layout.md)。
