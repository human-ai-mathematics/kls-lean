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

局部依赖关系为：

```text
Definitions → Transport → AbsoluteContinuity → BorellRepresentation
            → Borel ─────────────────────────────┘
```

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
