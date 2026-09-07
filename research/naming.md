# Lean 公共命名约定

公共名称说明数学对象和结论；构造细节放在定义及文档中。目录仍按现有 Blueprint
分层组织，模块路径、节点标签和证书入口保持稳定。命名空间可以跨这些实现文件组织 API。

## 当前入口

下表省略共同前缀 `FunctionalInequalities`。

| 用途 | 公共 API |
| --- | --- |
| 项目选定的内禀仿射松弛能量 | `Energy.Canonical.energy` |
| 所选常数与有限界 | `Poincare.Canonical.constant`、`Poincare.Canonical.Holds` |
| 环境空间上的光滑梯度松弛常数 | `Poincare.Ambient.constant`、`Poincare.Ambient.Holds` |
| 任意给定 L² 能量的优化器 | `Poincare.L2Energy.constant μ energy`、`Poincare.L2Energy.Holds μ energy C` |
| legacy 与所选常数的比较 | `Poincare.Euclidean.constant_eq_canonical` |
| 一般对数凹律的文献比较 | `KLS.LogConcave.canonical_eq_literature`，可写 `hμ.canonical_eq_literature` |
| Borell 密度代表及其性质 | `KLS.IsBorellDensity`；`hμ.exists_isBorellDensity m`；对代表元 `h`：`h.pos_of_mem_interior_support`、`h.continuousOn_interior_support`、`h.exists_bounds_of_isCompact` |
| 内禀律的矩 | `hμ.intrinsic_integrable_exp_norm`、`hμ.intrinsic_integrable_norm_pow p` |
| 环境/内禀协方差比较 | `Covariance.operator_coe_intrinsic μ hμ`、`Covariance.opNorm_operator_intrinsic μ hμ`、`Covariance.intrinsic_operator_inner_self_pos μ hμ`；前提 `hμ : MemLp id 2 μ` 显式 |

`Canonical` 表示仓库选择的具体前端。其定义仍是：把原 L² 类送入内禀仿射支撑坐标，
计算该坐标上的光滑梯度松弛，再拉回原空间。这个名字本身不提供 Cheeger、Dirichlet
或谱隙识别。`Ambient` 表示在环境空间直接做光滑梯度松弛；`L2Energy` 接受能量参数。
这三类对象的相等或比较仍通过已证明的定理表达。

## 规则

- 让命名空间表达稳定的对象类别；局部名称用 `constant`、`Holds`、`energy` 和相应结论。
  不把同一串构造限定词重复拼接到每个定理名中。
- 性质专属的结论放入该性质的命名空间。对数凹结论使用 `KLS.LogConcave`，由证明
  `hμ` 调用；需要的测度从证明推断。普通函数和比较仍保留清楚的参数。
- 保留有数学作用的条件与方向，例如 `_of_finiteAt`、`Ioi`/`Iio`、`weighted`、
  `compactSupport`、`L1`/`L2`、`ae`。不使用 `main`、`result`、`bound1` 或不透明缩写。
- 以可读性和可检索性判断，不设置机械字符上限。一个较长但准确的名字可以保留。
- 重命名时同步调用、Blueprint 声明锚点、公理 guards、当前指南和来源哈希；不增加
  旧名兼容别名。历史 decisions/explorations 不改写，新记录给出映射和验证证据。

## 本次全库检查的取舍

2026-09-07 扫描 `formalization/FunctionalInequalities/` 中 498 条具名公共定义、结构与
定理声明，并检查 `solutions/`、`examples/` 及 Blueprint 的调用。本次迁移 29 个公共
声明，主要覆盖所选能量、环境/所选常数比较、通用 L² 优化器和对数凹常数比较。

| 检查区域 | 处理与理由 |
| --- | --- |
| `Poincare/Euclidean` 与内禀能量 | 重复完整构造名最严重，整理为上表入口 |
| `Poincare/L2Energy`、`L2Comparison` | 通用前缀重复出现在复合定理中，统一使用 `L2Energy` 命名空间 |
| `Energy/Relaxation/` 与 `FormCore` | 已按 `PreEnergy`、`QuadraticPreEnergy`、恢复或核心性质分组；保留 `sequentialRelaxation` 与有限性条件，区分一般能量与具体松弛 |
| `Energy/Euclidean/LipschitzApproximation` | 保留光滑性、紧支撑、加权、L¹/L² 等区别；它们对应不同结论 |
| `Poincare/Gaussian` | 保留半直线方向、密度权重、平方和导数等信息，防止混淆实际积分 |
| `Probability` 与 `KLS/LogConcave*` | 支撑、内禀坐标、闭球、最终成立与内部非空等信息都有实际作用；不按长度截短 |
| 张量化、运输、协方差、L² 和抽象优化 | 名称已按对象或操作组织，未发现需要同类批量迁移的重复构造串 |
| `solutions` 证书名、模块路径与 Blueprint 标签 | 保留与节点一一对应的稳定入口；只迁移内部所引用的公共声明 |

精确的旧名/新名映射、三处参数推断调整及本地验证记录见
[命名整理决策](decisions/2026-09-07-public-naming-cleanup.md)。
