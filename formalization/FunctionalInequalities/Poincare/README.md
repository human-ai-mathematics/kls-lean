# Poincaré 基础：从概率测度到最优常数

这套基础为实 `L²` 上的 Poincaré 不等式提供可复用接口。给定概率测度 `μ` 和能量 `E`，它定义
最优常数，并证明有限常数有效当且仅当它控制最优常数。具体欧氏实现选用仿射支撑上的光滑
梯度能量，经 `L²` relaxation 后拉回原空间。

**当前已证明闭二次型链，以及 ambient/intrinsic 与 legacy/relaxed 比较桥。** 已验收的
Gaussian 和 tensorization 定理使用光滑测试接口，可以通过有限维比较桥转到所选常数。
与 locally Lipschitz 文献常数的等价也已完成 Lean 证明：一般比较要求内禀绝对连续性；
对于对数凹概率测度，该绝对连续性已被证明，因此无需另加这一假设。见
[文献常数比较](Euclidean/LiteratureComparison.lean) 与
[一般对数凹版本](Euclidean/LogConcaveComparison.lean)。这不提供完整 Borell 密度代表与矩定理，
也不证明 Cheeger 能量识别或 KLS。

当前接口默认允许随数学设计调整，已证明的接口也不例外；证明工作不以接口冻结为前提。
认证针对当前声明与证明。修改假设、结论、测试域或归一化时，应明确记录变化，同步依赖并
重新检查原数学目标是否仍被覆盖。详见[生命周期约定](../../../research/ledger-schema.md#lifecycle)。

## 从这里开始

| 你要做的事 | 阅读入口 |
| --- | --- |
| 使用新基础 | [Foundation.lean](Foundation.lean) |
| 理解最优常数与有限能量域 | [L2Energy.lean](L2Energy.lean) |
| 使用项目选定的欧氏常数 | [Euclidean/IntrinsicAffine.lean](Euclidean/IntrinsicAffine.lean) |
| 看完整的使用与边界示例 | [PoincareFoundation.lean](../../../examples/PoincareFoundation.lean) |
| 使用已证明的 Gaussian 定理 | [Gaussian/README.md](Gaussian/README.md) |
| 查找全部模块和 import 规则 | [formalization/README.md](../../README.md) |
| 查看剩余数学桥梁与 KLS 路线 | [Blueprint](../../blueprint/README.md) |
| 使用已证明的常数比较桥 | [Euclidean/README.md](Euclidean/README.md) |

示例文件包含常数函数的方差、能量比较的方向、所选常数的使用、Dirac 原始能量反例、空测试类
的 recovery 障碍，以及 Gaussian 的数值和退化情形。所有 `example` 都进入默认 `lake build`。

## 一个可以直接使用的接口

```lean
import FunctionalInequalities.Poincare.Foundation

open MeasureTheory FunctionalInequalities

example (μ : ProbabilityMeasure ℝ) :
    Energy.ClosedQuadratic (Energy.Canonical.energy μ) :=
  Energy.Canonical.closedQuadratic μ

example (μ : ProbabilityMeasure ℝ) (C : NNReal)
    (h : Poincare.Canonical.constant μ ≤ (C : ENNReal)) :
    Poincare.Canonical.Holds μ C :=
  (Poincare.Canonical.holds_iff_constant_le μ C).mpr h
```

第一条适用于任意 Borel 概率测度，包括没有密度的测度。第二条说明如何使用一个已知的常数界；
它不提供这个界本身。上述写法也适用于任意有限维实 Borel Hilbert 空间。

新接口使用 `ProbabilityMeasure`。已有 `μ : Measure E` 和 `[IsProbabilityMeasure μ]` 时，
可用 `Probability.ofMeasure μ` 打包；再转回 `Measure E` 在定义上就是原测度。旧接口保留其
`Measure` 与概率假设形式，调用者无需迁移已验收的证明。

## 数学对象与一般性

基础按职责分成三层：

1. `L2.mean`、`L2.center`、`L2.variance` 定义在实 `L²(μ)` 的几乎处处等价类上，适用于任意
   可测空间上的概率测度。方差是中心化后的 `L²` 范数平方，取值于 `NNReal`。
2. `Energy.Functional X` 是 `X → ENNReal`。有限域 `energy.domain` 携带排除 `⊤` 的证明，
   `finiteValue` 才将该值转为 `NNReal`。无限能量不会被 `toNNReal` 静默转换为零后参与优化。
3. `Poincare.TestFamily` 只记录测试类型、有限非负方差与能量。其最优常数是扩展 Rayleigh 商
   的上确界；它不要求测度、光滑性、闭性或 Markov 性。

在有限能量域上，`Poincare.L2Energy.constant μ energy` 与 `Poincare.L2Energy.Holds μ energy C` 满足

```text
Poincare.L2Energy.Holds μ energy C ↔ Poincare.L2Energy.constant μ energy ≤ (C : ENNReal).
```

约定 `0 / 0 = 0`，正方差除以零能量为 `⊤`。空测试类的最优常数为零；有正方差、零能量测试时，
最优常数为 `⊤`。这些边界由 [Optimal.lean](Optimal.lean) 中的定理明确覆盖。

[能量比较](L2Comparison.lean) 的方向是：同一测度下，若 `lower ≤ upper`，则
`Poincare.L2Energy.constant μ upper ≤ Poincare.L2Energy.constant μ lower`。增大能量会同时缩小有限域并增大
保留下来的分母，故不需要假设两者有相同定义域。

## 从具体测试到闭二次型

[PreEnergy](../Energy/Relaxation/Basic.lean) 记录具体测试、realization `toAmbient` 和有限能量。
在 `x` 处的 sequential relaxation，是所有 realization 收敛到 `x` 的测试序列之能量 `liminf`
的下确界。没有逼近序列时，值为 `⊤`。这个定义本身只用拓扑；下半连续性定理使用伪度量假设。

```text
Relaxation/Basic
  → Relaxation/Approximation
      → Relaxation/LowerSemicontinuous
      → Relaxation/Recovery
  + QuadraticPreEnergy
      → Relaxation/Quadratic → ClosedQuadratic
```

[Relaxation/Approximation.lean](../Energy/Relaxation/Approximation.lean) 收集两处证明共用的选择步骤：
严格的 relaxed-energy 上界可由任意小邻域内的具体测试实现；稠密 realization 提供逼近序列。
它不要求最优测试存在，也不引入 closability 假设。

已证明的分析结论包括：

- 在任意伪度量环境中，sequential relaxation 下半连续，不要求二次性或密度。
- 每个有限 relaxed-energy 点都有 recovery sequence，其能量收敛到 relaxed energy。
- realization 稠密时，每个点都有 recovery sequence，包括能量为 `⊤` 的点。空测试类的例子
  说明，此处不能删除密度前提。
- 二次 pre-energy 的 relaxation 满足二次缩放和完整扩展 parallelogram identity；再加
  realization 稠密性，就得到 `ClosedQuadratic`。

`ClosedQuadratic` 包含零值、非零实数缩放、parallelogram identity、下半连续性与有限域稠密性。
有限域已封装为实子模。零倍缩放单独处理，所以即使原向量能量为 `⊤`，缩放为零后仍得到零能量。
通用二次闭包定理不要求 raw energy 在 realization 的纤维上一致。

[Relaxation/Contraction.lean](../Energy/Relaxation/Contraction.lean) 另给条件性转移：若连续变换
在具体测试的 realization 上满足 `RelaxedContractionBound`，它就在所有点降低 relaxed energy。
具体光滑梯度实现尚未提供所有 normal contractions 的这个前提。

## 欧氏实现与仿射支撑

[SmoothGradientTest](../Energy/Euclidean/SmoothGradient/Basic.lean) 是全局 `C∞` 实函数，携带
`L²(μ)` 和平方梯度可积性的证明，有限能量为 `∫ ‖gradient f x‖² ∂μ`。
**本项目固定的 Mathlib v4.33.0 中，普通 `C∞` 写作 `ContDiff ℝ ∞`；`ContDiff ℝ ⊤` 表示解析性。**

光滑梯度 pre-energy 的二次性与 realization 稠密性均已证明。密度证明使用 Mathlib 中紧支撑
光滑函数在 `L²` 的稠密性，再利用梯度连续且紧支撑获得能量可积性。这里说的是 `L²` 稠密性，
没有额外声称 graph-norm core。

具体闭二次型实现采用有限维实 Hilbert 空间、Borel measurable space 与 second-countable
拓扑。它适用于任意概率测度，不要求密度、log-concavity、紧支撑或协方差非退化。

[AffineSupport.lean](../Probability/AffineSupport.lean) 取拓扑支撑的 affine span，并证明它闭、
可测、满测度且最小。选一个支撑原点后，将测度表达在 affine support 的方向空间上。
[intrinsicL2Equiv](../Energy/Euclidean/IntrinsicAffine/Basic.lean) 是原 `L²` 与 intrinsic `L²` 之间的
双向线性等距等价；在 intrinsic 空间计算 smooth-gradient relaxation，再沿等价拉回，得到
`Energy.Canonical.energy` 及其闭二次型定理。

这包含 proper affine support 与零维载体。它消除了法向方向，但不会自动消除仿射支撑内部的
其他奇异性。ambient 与 intrinsic relaxation 能量相等现已证明；原始测试能量只在
正交延拓构造中保证保持，不能对任意环境测试假定逐点一致。

## 四个接口如何区分

| 接口 | 使用的测试或能量 | 当前状态 |
| --- | --- | --- |
| `Poincare.constant` | 全局光滑、`L²`、有限梯度能量测试 | Gaussian 与 tensorization 使用此接口 |
| `Poincare.L2Energy.constant μ energy` | 任意扩展能量的有限域 | 通用优化器与 order law 已证明 |
| `Poincare.Canonical.constant` | 项目选定的 intrinsic-affine relaxation | 能量、闭二次型与 order law 已证明 |
| Blueprint 的 `C_P^lit` | locally Lipschitz 文献测试 | 本地 Lean 定义与比较仍待完成 |

Blueprint 的 `C_P^can` 是第三行的简写。当前 Lean 名称保留 `SmoothGradientRelaxation`，避免将
项目选择当成已完成的文献识别。协方差加权的 `C_P^aff` 是 CMH 路线的另一能量常数，不是同一
测度上无权常数的别名。

已证明的桥接顺序是 ambient/intrinsic 相等、legacy/relaxed 常数相等，然后在一般 log-concave
情形下接通 locally Lipschitz 文献常数（`Euclidean/LogConcaveComparison.lean`）。legacy/relaxed 桥可使用 relaxation 上界、逼近序列和
`L²` 方差连续性，不依赖 raw/core agreement 或 Cheeger identification。

前两步已有 [12 条已证明比较定理](Euclidean/README.md)，并由 `Foundation` 导出。
两份证书包含全部结论，公理 guards 同时覆盖 12 条定理及新增的关键辅助定理。

## 原始能量、一致性与剩余工作

对 `μ = δ₀`，函数 `0` 与 `id` 表示同一个零 `L²` 元素，但原始梯度能量分别为 `0` 和 `1`。
因此，对任意奇异测度都要求原始能量在 `L²` fibers 上一致是不成立的。

[FormCore.lean](../Energy/FormCore.lean) 明确区分：

- `RespectsAmbientFibers`：原始能量在同一 realization fiber 上一致；
- `AgreesOnTests`：指定环境能量在每个测试上等于原始能量；
- `SequentiallyGenerates`：该环境能量等于 sequential relaxation；
- `IsSequentialCoreFor`：同时具有 agreement 与 generation。

最后一个是项目内的精确规格，尚未与文献 graph-norm core 建立等价。以上性质均不属于
`ClosedQuadratic` 的字段。

当前还没有具体 smooth-gradient 的 Markov/Dirichlet witness、raw/core agreement、
`Ecan = 2 Chμ`、whitening、自伴生成元、半群或 reciprocal spectral-gap 定理。
旧光滑测试常数、ambient relaxed 常数与所选 intrinsic-affine 常数的等价已经由 Lean 证明；
locally Lipschitz 文献常数的本地定义与比较仍待形式化。以上剩余工作由 Blueprint 中不同的
节点承载；KLS 主命题也尚未成为本地 Lean 声明。

## 来源与检查

数学来源在声明附近分别记录：旧光滑测试接口说明历史手稿 Definition 2.1 的公式与本地测试域
选择；光滑密度证明指向固定 Mathlib 的 `Lp.dense_hasCompactSupport_contDiff`；通用 relaxation
与优化层是此项目已经证明的构造。文献识别与长路线的来源和状态由 Blueprint 另行记录。

本文参考 [formech 的固定版本](https://github.com/lyw-ops/formech/tree/d0bb1913acc1f710ba6eadf1244b633abbc75fb9)
组织“数学含义、具体例子、接口入口、范围与构建”。该参考仅影响书写方式，不提供 KLS 的数学依据。

从 `formalization/` 运行：

```sh
lake build Examples
lake build solutions.FoundationAxiomAudit
lake build
```

[FoundationAxiomAudit.lean](../../../solutions/FoundationAxiomAudit.lean) 在默认构建中固定八个核心
声明的传递公理集为 `propext`、`Classical.choice`、`Quot.sound`。它补充现有四个节点证书及
Gaussian audit，不新增 ledger 节点。完整构建验证 Lean 证明；文献含义的一致性仍须结合上述
接口边界审阅。
