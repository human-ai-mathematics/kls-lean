# Energy 文件导航

本目录按数学职责组织扩展非负能量、序列松弛和欧氏实现。整理依据是
[模块放置规则](../../README.md#placement-rules)；数学定义、适用假设和证明边界见
[Poincaré 基础指南](../Poincare/README.md)。

## 阅读顺序

| 目的 | 入口与后续模块 |
| --- | --- |
| 一般能量与大小比较 | `Functional.lean` → `Comparison.lean` |
| 从有限测试能量定义松弛 | `Relaxation/Basic.lean`（含沿连续映射的松弛比较 `sequentialRelaxation_comp_le` 与带常数因子的 `_comp_le_mul`）→ `Relaxation/Approximation.lean` |
| 下半连续性与恢复序列 | `Relaxation/LowerSemicontinuous.lean`、`Relaxation/Recovery.lean` |
| 二次性与闭包 | `QuadraticPreEnergy.lean`、`ClosedQuadratic.lean` → `Relaxation/Quadratic.lean` |
| 核心与 Markov 性质 | `FormCore.lean`、`Dirichlet.lean`；条件性转移见 `Relaxation/Contraction.lean` |
| 光滑梯度松弛的 Dirichlet 性 | `SmoothGradient/Dirichlet.lean`：磨光正规收缩 `NormalContraction.smoothed`、测试复合 `Test.compSmoothed`、`SmoothGradient.markovian`/`dirichlet` 与内禀版本 `Intrinsic.dirichlet`；对任意 Borel 概率律成立 |
| 光滑梯度实现 | `SmoothGradient/Basic.lean` → `Quadratic.lean`、`Density.lean` → `Closed.lean`；`SmoothGradient/NormalDirection.lean`：真仿射支撑上的法向坐标是 L² 零类但原始能量为 1，环境预能量不满足 `RespectsAmbientFibers`；`SmoothGradient/Core.lean`：局部密度假设 `LocalDensity` 下的 raw/sequential-core 一致性 `preEnergy_agreesOnTests`、`preEnergy_isSequentialCoreFor` 及内禀律实例 |
| 仿射支撑内的实现 | `SmoothGradient/Intrinsic/Basic.lean` → `Closed.lean` |
| 两种实现的比较与 Lipschitz 逼近 | `SmoothGradient/Intrinsic/Comparison.lean`、`Euclidean/LipschitzApproximation.lean` |
| 局部斜率与渐近 Lipschitz 的 L² 松弛 | `LocalSlope/Relaxation.lean`：`AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`、`LocalSlope.{preEnergy,relaxation}` 及无条件比较 `relaxation_le_asymptoticLipschitz`；两种约定相等未证 |
| 度量 Cheeger 能量与 `𝓔^can = 2·Ch` | `Cheeger.lean`：`Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`；内禀律绝对连续时 `SmoothGradient.relaxation = LocalSlope.relaxation` 与 `𝓔^can_μ = 2·Ch_μ`，对数凹律自动满足前提；奇异情形的五条开放义务留在 `WIP/Cheeger.lean`，不在聚合导入中 |
| 协方差加权的 Lipschitz 梯度定义 | `CovarianceGradient/Basic.lean`：预能量、序列松弛、内禀律上的 `Energy.CovarianceGradient.Intrinsic.energy` |
| 算子形式与可闭性 | `Relaxation/LinearPMap.lean`（任意可闭 `LinearPMap` 的松弛等于闭包范数平方 `normSqEnergy`；Hilbert 选择引理）→ `Euclidean/WeakDerivative.lean`（Lipschitz 函数分部积分）→ `WeightedGradient/Basic.lean`、`Closable.lean`、`Core.lean`（含 ℝ + C_c^∞ 核 `constantSmoothCore`） |
| 平移不变性 | `CovarianceGradient/Translation.lean`：平移律、L² 拉回等距 `L2.Translation.pullbackEquiv`、方差与协方差不变、协方差松弛与最优常数不变 |
| 一般线性等价传输 | `CovarianceGradient/LinearEquiv.lean`：像律 `KLS.LogConcave.mapContinuousLinearEquiv`、协方差算子经映射与伴随共轭、梯度复合公式、L² 拉回等距 `L2.ContinuousLinearEquiv.pullbackEquiv`、协方差松弛与最优常数不变、仿射支撑的像；白化的传输部分 |
| 线性等距传输 | `CovarianceGradient/Isometry.lean`：等距像律 `Probability.mapLinearIsometryEquiv`、协方差算子共轭、梯度复合公式、L² 拉回等距 `mapL2`、协方差松弛与最优常数不变；与 Translation 合起来覆盖内禀坐标的任意仿射等距变换 |

表格是阅读路线；精确的依赖关系以各文件的 `import` 为准。

## 导入示例

```lean
import FunctionalInequalities.Energy.Relaxation.Recovery
import FunctionalInequalities.Energy.SmoothGradient.Closed
import FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Closed
```

库内模块导入实际需要的具体文件。下游完整使用示例可从
`FunctionalInequalities.Poincare.Foundation` 和
[`examples/PoincareFoundation.lean`](../../../examples/PoincareFoundation.lean) 开始。

## 后续文件放置

- 同一主题的基础定义放在 `Basic.lean`，后续文件以职责命名；目录提供共同前缀。
- 通用能量接口放在根目录；一般松弛定理放在 `Relaxation/`。
- 具体实现放在对应欧氏主题目录；跨实现的比较保留在 `Euclidean/`。
- 按数学职责和依赖拆分，不按证明状态、任务编号或日期拆分。

文件路径与声明命名空间各自独立。本次整理保留所有数学声明，闭二次性仍不自动提供
Dirichlet 性质或原始测试能量与松弛能量的一致性。旧导入路径的逐项替换见
[迁移记录](../../../research/explorations/2026-09-07-energy-module-layout.md)。
