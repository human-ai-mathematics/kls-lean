# 对数凹工具与表示定理

本目录沿用 [Definitions.lean](../Definitions.lean) 中基于紧集的 `KLS.LogConcave` 定义。
对数凹测度可以在环境空间中奇异；内禀结论使用仿射支撑的方向空间，并包含零维情形。
具体假设和数学来源以各模块的声明与说明为准。

## 阅读顺序

| 模块 | 内容 | 当前边界 |
| --- | --- | --- |
| [Transport.lean](Transport.lean) | 仿射等距传输、内禀坐标与支撑几何 | 已证明 |
| [Borel.lean](Borel.lean) | 紧集与 Borel 集版本的对数凹等价 | 已证明；不预设密度或二阶矩 |
| [AbsoluteContinuity.lean](AbsoluteContinuity.lean) | 小球估计、内禀绝对连续性及支撑边界结论 | 已证明；不构造完整对数凹密度代表 |
| [BorellRepresentation.lean](BorellRepresentation.lean) | 密度代表、内部正性、局部界和矩结论 | 已证明；由 `Solutions.ThmBorellLogconcaveDensity.certificate` 打包 |
| [AffineCovariance.lean](AffineCovariance.lean) | 仿射协方差预能量在对数凹律上的良定义契约：内禀二阶矩、Lipschitz 测试 a.e. 可微、能量只依赖 L² 类 | 已证明；定义节点 `def:affine-poincare-constant` 的契约，不含闭性或 Poincaré 结论 |
| [CovarianceClosure.lean](CovarianceClosure.lean) | 全维对数凹律上加权梯度算子 `g ↦ B∇g` 的稠密定义、可闭性、光滑核闭包相等、松弛等于闭包范数平方；内禀律版本 | 已证明；由 `Solutions.LemCovarianceCoreClosure.certificate` 打包，不含 Poincaré、平移不变或 KLS 结论 |
| [AffineClosedForm.lean](AffineClosedForm.lean) | 仿射协方差松弛是闭二次型、测试为序列核、内禀律平移下的等距与常数不变、与 ℝ + C_c^∞ 核上闭算子范数平方（CMH 闭形式）相等 | 已证明；由 `Solutions.ThmAffineCovarianceRelaxationClosed.certificate` 打包，不含 Poincaré 不等式、环境平移不变或 KLS |
| [AffineTranslation.lean](AffineTranslation.lean) | 环境平移保持紧集对数凹；对数凹律的环境二阶矩与重心；平移到负重心得到零均值律 | 已证明；与 `Poincare/Euclidean/AffineTranslation.lean` 的常数不变性一起由 `Solutions.LemAffinePoincareTranslationInvariance.certificate` 打包，不含 Poincaré 不等式、各向同性归约或 KLS |
| [IsotropicReduction.lean](IsotropicReduction.lean) | 连续线性等价保持对数凹；三条 KLS 表述 `IsotropicBound`、`CovarianceBound`、`AffineBound` 及其两两等价；中心化、白化后的各向同性律；`AffineBound → Conjecture` | 已证明；由 `Solutions.ThmAffineIsotropicReduction.certificate` 打包，不断言任一表述对某个 K 成立 |

局部依赖关系为：

```text
Definitions → Transport → AbsoluteContinuity → BorellRepresentation → AffineCovariance → AffineTranslation ─┐
            → Borel ─────────────────────────────┘                  → CovarianceClosure → AffineClosedForm   → IsotropicReduction
```

`CovarianceClosure` 使用 `Energy/Euclidean/CovarianceGradient/{Operator,Closable,Core}`：对数凹律
只负责提供三条前提（`ν ≪ Haar`、支撑边界零测、Haar 在支撑内部紧集上被 `ν` 局部支配）。

`IsotropicReduction` 另外使用 `Energy/Euclidean/CovarianceGradient/LinearEquiv`（一般线性等价下的传输）、
`Probability/CovarianceWhitening`（正定协方差的自伴逆平方根）与 `Poincare/Euclidean/LipschitzComparison`
（单位权 Lipschitz 梯度松弛与文献常数的桥）；对数凹只负责像律的对数凹性、全支撑与内禀协方差正定。

`AffineTranslation` 另外使用 `Poincare/Euclidean/AffineTranslation`（平移后的仿射支撑、方向与内禀律的识别，
以及对任意 Borel 律成立的常数不变性）与 `Transport` 的仿射等距传输；对数凹只负责平移律的对数凹性与环境二阶矩。

`AffineCovariance` 另外使用 `Energy/Euclidean/CovarianceGradient/Basic`，那里定义了对任意概率律
的协方差加权 Lipschitz 梯度预能量；对数凹律只负责给出契约的前提（绝对连续性、支撑边界零测、矩）。

`AbsoluteContinuity` 另外使用 `Probability/BallAverages`。`BorellRepresentation` 同时使用
绝对连续性（密度代表的构造）和 Borel 集表述（Borell 尾引理与指数矩）。

## 导入与使用

```lean
import FunctionalInequalities.KLS.LogConcave.Borel
import FunctionalInequalities.KLS.LogConcave.AbsoluteContinuity

#check FunctionalInequalities.KLS.LogConcave.borel_iff
#check FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous
```

文献 Poincaré 常数的比较在
[LogConcaveComparison.lean](../../Poincare/Euclidean/LogConcaveComparison.lean) 中组合这些工具。
现有声明名称保持不变；旧模块路径不保留转发文件。路径映射见
[迁移记录](../../../../research/explorations/2026-09-07-logconcave-module-layout.md)。
