# Poincaré 新基础：从光滑梯度到闭二次型

**当前状态：闭二次型链已完成，canonical identification 尚未完成。**

有限维实 Borel Hilbert 空间上的 `C∞` 光滑梯度 pre-energy 已证明二次性与实现稠密性；其
sequential relaxation 已经是稠密定义的下半连续闭二次泛函。对任意概率测度，还可以先约化到
最小闭满测度 affine support 的方向空间，再把闭二次型沿双向线性等距等价拉回原来的实
`L²` 空间。

这仍不是 Markov/Dirichlet 定理，也没有证明 relaxation 在每个具体测试上保留 raw gradient
energy，更没有把该能量识别成 `2 · Chμ`。这些边界是当前 API 的一部分，不是待补的注释。

建议按以下顺序阅读：

1. [`Foundation.lean`](Foundation.lean)：新分层 API 的 aggregate 入口；
2. [`SmoothGradientClosed.lean`](../Energy/Euclidean/SmoothGradientClosed.lean)：ambient
   smooth-gradient relaxation 的闭二次型实例；
3. [`IntrinsicAffineClosed.lean`](../Energy/Euclidean/IntrinsicAffineClosed.lean)：intrinsic
   affine 版本及等距 transport；
4. 本文余下部分：通用定理、具体实现与当前 non-claims。

## 1. 先固定 `C∞` 的 Lean 语义

本仓库固定 Lean/Mathlib `v4.33.0`。在这个版本中，普通无限次可微写作

```lean
ContDiff ℝ ∞ f
```

而 `ContDiff ℝ ⊤ f` 表示更强的 analytic 正则性。旧文曾把 `⊤` 误当作普通 `C∞`；当前
legacy Poincaré 测试类和新的 smooth-gradient 测试类都已迁移到 `∞`。因此本文中的“全局光滑”
始终表示 `ContDiff ℝ ∞`，不暗含解析性。

## 2. 数学对象

一个有限 pre-energy `P : Energy.PreEnergy X` 记录

```text
P.Test                    concrete tests
P.toAmbient : P.Test → X  realization in the ambient space
P.energy : P.Test → ℝ≥0   finite concrete energy
```

它的 sequential relaxation 是扩展非负泛函

```text
P.sequentialRelaxation : X → ℝ≥0∞,
```

在 `x` 处对所有满足 `toAmbient (f n) → x` 的测试序列取 energy `liminf` 的下确界。常值
序列总给出

```lean
P.sequentialRelaxation (P.toAmbient f) ≤ P.energy f
```

但这里一般只有 `≤`，不能无条件改成等号。

[`QuadraticPreEnergy.lean`](../Energy/QuadraticPreEnergy.lean) 中的
`PreEnergy.Quadratic` 另外要求：测试空间与环境空间都是实模，realization 保持 `0`、加法和
实数缩放，有限能量满足二次缩放与 parallelogram identity。它导出线性 realization
`toAmbientₗ` 以及 neg/sub 的相容性，但本身不假定闭性、稠密性、closability 或测试上一致性。

闭包后的目标结构是 [`ClosedQuadratic.lean`](../Energy/ClosedQuadratic.lean) 中的
`Energy.ClosedQuadratic`：

```text
E(0) = 0
E(c • f) = ENNReal.ofReal (c²) * E(f)       (c ≠ 0)
E(f + g) + E(f - g) = 2 E(f) + 2 E(g)
E is lower semicontinuous
{f | E(f) < ⊤} is dense
```

有限能量域因而成为实子模。此结构仍不自动包含 normal-contraction/Markov 性。

Poincaré 优化层则把任意扩展 `L²` 能量的有限域变成有限值测试族：

```text
rayleigh f = variance f / energy f : ℝ≥0∞
constant   = ⨆ f, rayleigh f        : ℝ≥0∞
Holds C    ↔ ∀ f, variance f ≤ C * energy f
```

已经证明 `Holds C ↔ constant ≤ C`（把有限 `C : NNReal` 强制转换到 `ENNReal`）。值为 `⊤` 的
能量点不进入测试族；不会通过 `ENNReal.toNNReal` 被静默改成零。

## 3. Live source map

下列是当前可编译的基础链；箭头表示主要依赖方向。

```text
Probability/
├── Basic.lean
└── AffineSupport.lean
    # affineSpan(support), minimality, intrinsic law and affine reconstruction

L2/
└── MeanVariance.lean
    # real L² constants, mean, centering and NNReal variance

Energy/
├── Functional.lean
├── Comparison.lean
├── Relaxation.lean
├── QuadraticPreEnergy.lean
├── RelaxationLowerSemicontinuous.lean
├── RelaxationRecovery.lean
├── RelaxationQuadratic.lean
├── RelaxationContraction.lean
├── FormCore.lean
├── ClosedQuadratic.lean
├── Dirichlet.lean
└── Euclidean/
    ├── SmoothGradient.lean
    ├── SmoothGradientQuadratic.lean
    ├── SmoothGradientDensity.lean
    ├── SmoothGradientClosed.lean
    ├── IntrinsicAffine.lean
    └── IntrinsicAffineClosed.lean

Poincare/
├── Foundation.lean
├── Optimal.lean
├── Comparison.lean
├── L2Energy.lean
├── L2Comparison.lean
└── Euclidean/
    ├── SmoothGradient.lean
    └── IntrinsicAffine.lean
```

通用闭包链是

```text
Relaxation
  ├── LowerSemicontinuous
  ├── Recovery
  ├── QuadraticPreEnergy ──→ RelaxationQuadratic ──→ ClosedQuadratic
  └── Contraction (conditional transfer only)
```

具体欧氏链是

```text
SmoothGradient
  ├── SmoothGradientQuadratic
  ├── SmoothGradientDensity
  └── SmoothGradientClosed

AffineSupport ──→ IntrinsicAffine ──→ IntrinsicAffineClosed
```

旧的 [`Basic.lean`](Basic.lean)、`LinearTest`、`Transport`、product、finite product 与 Gaussian
模块继续提供已验收的实际函数接口。新名称主要位于 `Poincare.TestFamily` 与
`Energy` namespace；新旧常数可以同时导入，但目前没有桥定理证明二者相等。

## 4. 通用 relaxation 已精确证明什么

### Lower semicontinuity

[`RelaxationLowerSemicontinuous.lean`](../Energy/RelaxationLowerSemicontinuous.lean) 证明：在
任意 pseudometric 环境空间中，`P.sequentialRelaxation` 下半连续。该定理不需要二次性、
realization 稠密性或 Markov 假设。它是可度量环境中的 sequential 结论；本文不把它推广成
任意拓扑空间的抽象 l.s.c. envelope 声明。

### Recovery sequences

[`RelaxationRecovery.lean`](../Energy/RelaxationRecovery.lean) 证明：

- 每个有限 relaxed-energy 点都有 recovery sequence；
- 如果 `P.DenseRealization`，则每个环境点都有 recovery sequence，包括 energy 为 `⊤` 的点。

第二条的稠密性不能删除：测试类型为空时，relaxation 的值仍可为 `⊤`，但根本没有逼近序列。

### Quadratic closure

[`RelaxationQuadratic.lean`](../Energy/RelaxationQuadratic.lean) 已证明完整的 extended-valued
结论，而不只是单向不等式：

```lean
PreEnergy.Quadratic.sequentialRelaxation_smul_of_ne_zero
PreEnergy.Quadratic.sequentialRelaxation_parallelogram
PreEnergy.Quadratic.closedQuadratic_sequentialRelaxation
```

最后一个定理精确地说：

```text
P.Quadratic + P.DenseRealization
  ⇒ ClosedQuadratic P.sequentialRelaxation.
```

parallelogram identity 本身不需要密度；密度只用于 `ClosedQuadratic` 的稠密有限能量域。这个
定理也不需要 `AgreesOnTests` 或 closability，因为 relaxation 可以在 realization 的纤维上
严格降低 concrete energy。

### Conditional contraction transfer

[`RelaxationContraction.lean`](../Energy/RelaxationContraction.lean) 定义
`PreEnergy.RelaxedContractionBound C`。若该 bound 已在 realized concrete tests 上建立，且
`C : X → X` 连续，则

```lean
P.sequentialRelaxation (C x) ≤ P.sequentialRelaxation x
```

对所有 `x` 成立。模块也给出由 transformed recovery sequences 建立该 bound 的方法。它没有
证明 smooth-gradient relaxation 对所有 normal contractions 都满足这个前提，因此不能把这条
条件性 transport 定理称为 Markov 定理。

## 5. Smooth-gradient 实例

[`SmoothGradient.lean`](../Energy/Euclidean/SmoothGradient.lean) 的测试对象是全局
`ContDiff ℝ ∞` 的实函数，并携带 `L²(μ)` 与平方梯度可积性证明。其有限能量为

```text
∫ x, ‖gradient f x‖² ∂μ.
```

公开 frontend 采用有限维实 Hilbert 空间、Borel measurable space 与 second-countable
topology；这些假设使梯度、可测性和 Mathlib 密度定理在一个稳定边界内工作。

[`SmoothGradientQuadratic.lean`](../Energy/Euclidean/SmoothGradientQuadratic.lean) 构造测试的
`0/+/-/-/ℝ-smul`，证明 `toL2` 相容性、梯度能量二次缩放和 parallelogram identity，并导出

```lean
smoothGradientPreEnergy_quadratic
```

[`SmoothGradientDensity.lean`](../Energy/Euclidean/SmoothGradientDensity.lean) 使用 Mathlib 的
compactly supported `C∞` density 结果证明

```lean
smoothGradientPreEnergy_denseRealization
```

二者代入通用闭包定理，得到 [`SmoothGradientClosed.lean`](../Energy/Euclidean/SmoothGradientClosed.lean)
中的命名结论

```lean
smoothGradientRelaxation_closedQuadratic (μ : ProbabilityMeasure E) :
  ClosedQuadratic (smoothGradientRelaxation μ)
```

因此 smooth-gradient relaxation 的零值、二次缩放、完整 parallelogram identity、下半连续性和
稠密有限能量域均已正式证明。

## 6. Affine support 与 intrinsic `L²`

[`AffineSupport.lean`](../Probability/AffineSupport.lean) 定义

```text
affineSupport μ = affineSpan ℝ (support μ).
```

它证明该 affine subspace 闭、可测且具有满测度，并给出 minimality：若闭 affine subspace
`A` 满足 `x ∈ A` 几乎处处成立，则 `affineSupport μ ≤ A`。

选择支撑中的一个原点后，`intrinsicMap` 把环境点送到 affine support 的 direction space，
`intrinsicMeasure` 是相应 pushforward law；`reconstruct` 被封装为从 direction space 到环境空间
的 `AffineIsometry`。已经证明

```text
intrinsicMap (reconstruct v) = v
reconstruct (intrinsicMap x) = x        μ-a.e.
```

以及两个方向的 measure-preserving 性。

[`IntrinsicAffine.lean`](../Energy/Euclidean/IntrinsicAffine.lean) 把这两个映射提升到实 `L²`：

```lean
toIntrinsicL2 : L²(μ) →ₗᵢ[ℝ] L²(intrinsicMeasure μ)
toAmbientL2   : L²(intrinsicMeasure μ) →ₗᵢ[ℝ] L²(μ)
intrinsicL2Equiv : L²(μ) ≃ₗᵢ[ℝ] L²(intrinsicMeasure μ)
```

两个复合都已证明为恒等，因此这里是**双向线性等距等价**，不是只有单向 embedding。
`intrinsicAffineSmoothGradientRelaxation` 先经该等价进入 direction space，再计算该空间上的
smooth-gradient relaxation。

[`IntrinsicAffineClosed.lean`](../Energy/Euclidean/IntrinsicAffineClosed.lean) 用
`ClosedQuadratic.comap_linearIsometryEquiv` 拉回全部结构，得到

```lean
intrinsicAffineSmoothGradientRelaxation_closedQuadratic
```

这会删除 affine support 的法向方向，但不会自动解决 support 内更细的奇异性。

[`Poincare/Euclidean/IntrinsicAffine.lean`](Euclidean/IntrinsicAffine.lean) 再把这一扩展能量
接到通用 `L²` 优化器，定义

```lean
intrinsicAffineSmoothGradientRelaxationConstant
IntrinsicAffineSmoothGradientRelaxationHolds
intrinsicAffineSmoothGradientRelaxationHolds_iff_constant_le
```

最后一个定理刻画有限常数有效当且仅当它控制最优 `ENNReal` 常数。它没有比较 intrinsic 与
ambient 两个 smooth-gradient relaxation constant。

## 7. 为什么仍保留 form-core 层

[`FormCore.lean`](../Energy/FormCore.lean) 分别记录：

- `RespectsAmbientFibers`：concrete energy 在同一 realization fiber 上一致；
- `AgreesOnTests`：relaxation 在每个 concrete test 上等于原能量；
- `SequentiallyGenerates`：concrete tests 生成整个 relaxed energy；
- `IsSequentialCoreFor`：项目内由 agreement 与 generation 组成的精确 core 规格。

这些不是 `ClosedQuadratic` 的字段。对 `μ = δ₀`，函数 `f = 0` 与 `g(x) = x` 表示同一个零
`L²` 元素，但 ambient gradient energy 分别为 `0` 与 `1`。因此 raw ambient tests 一般不可能
无条件满足 fiber consistency 或 `AgreesOnTests`；sequential relaxation 正是允许降低这种
presentation-dependent energy 的机制。

## 8. 当前明确不声称

当前代码没有证明：

- `smoothGradientRelaxation` 或 intrinsic 版本满足所有 normal contractions，因此没有
  Markov/Dirichlet witness；
- smooth-gradient tests 满足 `AgreesOnTests`、`IsSequentialCoreFor`，或 graph-norm core
  等价；
- raw ambient gradient energy 对奇异测度在 `L²` fibers 上一致；
- smooth-gradient relaxation 与文献中的 canonical energy `2 · Chμ` 相等；
- intrinsic-affine relaxation constant 与 ambient smooth-gradient relaxation constant 相等；
- 新 `L²` 扩展能量常数等于 legacy `Poincare.Basic` 的光滑测试常数；
- 已有自伴生成元、半群、`constant = 1 / spectralGap`、Bakry–Émery、localization 或 KLS
  主定理。

标准 metric-measure 归一化的预期目标仍是

```text
Ecan(f) = 2 · Chμ(f) = ∫ |Df|_*² dμ,
```

但当前 API 有意保留 `smoothGradientRelaxation` 名称，直到 identification theorem 真正完成。
带参数的 anisotropic energy `∫ ⟨Q∇f, ∇f⟩ dμ` 也应保持为另一对象，不能与无参数 canonical
energy 混名。

## 9. 可复现构建

从 `formalization/` 运行以下命令；它们可直接复制：

```sh
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/RelaxationQuadratic.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/Euclidean/SmoothGradientClosed.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Energy/Euclidean/IntrinsicAffineClosed.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Poincare/Euclidean/IntrinsicAffine.lean
lake build FunctionalInequalities.Poincare.Foundation
lake build
```

`Foundation.lean` 是下游应用和 smoke test 的便利入口；可复用低层模块仍应 import 精确依赖，
避免让 aggregate 反向进入基础层。
