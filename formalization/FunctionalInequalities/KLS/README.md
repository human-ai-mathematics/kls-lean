# KLS 文件导航

本目录组织 KLS 目标使用的定义、对数凹工具和具体路线对象。数学来源写在各 Lean 模块开头；
证明状态由[ledger](../../../research/a-series/ledger.yaml)与当前声明、证明共同记录。

## 阅读入口

| 文件或目录 | 职责与边界 |
| --- | --- |
| [Definitions.lean](Definitions.lean) | 紧集对数凹定义、局部斜率、文献测试域和常数；共享定义入口 |
| [Statement.lean](Statement.lean) | 协方差归一化的 KLS 猜想命题；没有 KLS 证明 |
| [LogConcave/](LogConcave/README.md) | 对数凹传输、紧集/Borel 等价、内禀绝对连续性、Borell 密度表示、仿射协方差常数的对数凹契约与闭形式、环境平移下的对数凹性与重心、KLS 的仿射/各向同性归约 |
| [LocalSlopeGradient.lean](LocalSlopeGradient.lean) | 局部斜率与梯度关系，以及绝对连续性前提下的能量和测试域识别；已证明 |
| [Isotropic.lean](Isotropic.lean) | 有限二阶矩、零均值和单位协方差的定义；白化在 `Probability/CovarianceWhitening.lean`，仿射/各向同性归约在 `LogConcave/IsotropicReduction.lean` |
| [Isoperimetry.lean](Isoperimetry.lean) | 仿射载体上的边界含量、等周常数及逆尺度定义；不提供 Cheeger 比较 |
| [ConditionalFiber.lean](ConditionalFiber.lean) | 条件纤维能量的构造及六条已证明的良定义性契约；不提供闭性、Markov 性或框架界 |

先读 `Definitions` 和 `Statement` 确定目标；对数凹分析沿子目录的阅读顺序展开。
文献常数比较的结论位于
[Poincare/Euclidean/LogConcaveComparison.lean](../Poincare/Euclidean/LogConcaveComparison.lean)，
完整使用说明见[Poincaré 比较指南](../Poincare/Euclidean/README.md)。

## 文件放置

对数凹性质及其表示定理放在 `LogConcave/`；共享目标定义和其余路线对象保留在本层。
`LogConcave` 谓词目前仍定义在 `Definitions.lean`，子目录直接导入该定义。
目录名不表示证明完成；每个节点的证明状态以 ledger 与证书为准，不能从根模块编译成功推断。

声明命名空间继续使用 `FunctionalInequalities.KLS`，模块路径按主题组织。
后续文件按数学职责放置，证明完成不触发文件移动。旧路径与新路径的对应关系见
[迁移记录](../../../research/explorations/2026-09-07-logconcave-module-layout.md)。
