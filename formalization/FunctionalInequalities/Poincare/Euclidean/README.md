# 从光滑测试接到所选 Poincaré 常数

这批已证明的比较定理接通三个对象：legacy 光滑测试常数、ambient relaxation
常数，以及项目选定的 intrinsic-affine relaxation 常数。已有 Gaussian 和有限维 tensorization
结论现在可以通过等式用于所选常数。

**12 条比较定理均已证明，两份证书通过传递公理检查，ledger 状态为
`proved / checked_by: lean`。** 原有声明的假设和类型保持不变，现由
`Poincare.Foundation` 与 root aggregate 导出。后续批次已进一步证明一般对数凹
测度的文献 locally Lipschitz 常数比较；Cheeger 和 KLS 仍未证明。

一般对数凹版本位于 [LogConcaveComparison.lean](LogConcaveComparison.lean)：从现有
`KLS.LogConcave μ` 推出 legacy、intrinsic 和 literature 常数相等，进而得到 selected 常数等式。
内禀绝对连续性由 [AbsoluteContinuity.lean](../../KLS/LogConcave/AbsoluteContinuity.lean) 证明，未作为额外假设。
包含环境奇异和零维支撑；完整 Borell 密度代表及矩定理仍未完成。见
[本地证明记录](../../../../research/decisions/2026-09-06-general-logconcave-comparison.md)。

公共命名按数学角色组织：`Poincare.Canonical.constant` 是所选常数，
`Poincare.Ambient.constant` 是环境空间上的松弛常数，`Poincare.L2Energy.constant μ energy`
是通用优化器。对 `hμ : KLS.LogConcave μ`，直接使用 `hμ.canonical_eq_literature`。
名称整理的范围与保留长名的理由见 [命名约定](../../../../research/naming.md)。

## 阅读入口

| 目的 | 文件 | 内容 |
| --- | --- | --- |
| 先看几何比较和退化情形 | [LemAmbientIntrinsicPoincareComparison.lean](../../../../solutions/LemAmbientIntrinsicPoincareComparison.lean) | 5 条声明、4 个应用 |
| 看抽象比较和 Gaussian 的未来用法 | [LemLegacyRelaxedPoincareComparison.lean](../../../../solutions/LemLegacyRelaxedPoincareComparison.lean) | 7 条比较声明、8 个应用 |
| 任意具体 pre-energy 的常数比较 | [Poincare/Relaxation.lean](../Relaxation.lean) | 原始测试族定义、有限常数等价、扩展最优常数等式 |
| 比较两种坐标下的能量 | [Energy/Euclidean/AffineComparison.lean](../../Energy/Euclidean/AffineComparison.lean) | 测试限制、测试延拓、relaxation 等式 |
| 从能量等式得到常数等式 | [AffineComparison.lean](AffineComparison.lean) | 两种 relaxed `Holds` 与常数比较 |
| 接到旧光滑测试接口 | [LegacyComparison.lean](LegacyComparison.lean) | 原始测试域识别及两级常数比较 |

## 要表达的数学结论

给定任意概率律 `μ` 和实 `L²(μ)` 上的具体有限 pre-energy `P`，定义

```text
TestFamily.ofPreEnergy μ P
  Test     = P.Test
  variance = L2.variance μ ∘ P.toAmbient
  energy   = P.energy
```

抽象比较定理证明：对每个 `C : NNReal`，原始测试族上的不等式与 relaxation
有限能量域上的不等式等价，两个 `ENNReal` 最优常数也相等。这里不要求密度、二次性或
raw/core agreement。测试类可以为空，常数可以是零，最优常数可以是无穷。

有限维欧氏实现证明：ambient smooth-gradient relaxation 与已经拉回原 `L²(μ)` 的
intrinsic-affine relaxation 完全相等。因此二者的有限能量域、有效有限常数和扩展最优
常数一致。测度允许奇异、proper affine support 或零维支撑，不要求二阶矩或 log-concavity。

最后一组将 legacy 的 `Admissible` 与 `SmoothGradientTest` 对齐，得到

```text
Poincare.constant μ
  = Poincare.Ambient.constant μ
  = Poincare.Canonical.constant μ.
```

这里略去了 `ProbabilityMeasure → Measure` 的 coercion。真正的有限常数接口明确使用
`C : NNReal` 和旧接口的 `(C : ℝ)`；没有将无穷最优常数转成实数。两种测试都要求普通
`ContDiff ℝ ∞`、`L²` 及平方梯度可积，归一化始终是 `Var ≤ C ∫ ‖gradient‖²`。

## 一个可直接使用的调用方式

以下调用已在第二份证书入口中编译检查，使用已证明的 Gaussian 定理与比较桥：

```lean
import FunctionalInequalities.Poincare.Euclidean.LegacyComparison
import FunctionalInequalities.Poincare.Gaussian.Real

open FunctionalInequalities

#check (fun (m : ℝ) (v : NNReal) ↦
  (Poincare.Euclidean.holds_iff_canonical
    (Probability.ofMeasure (ProbabilityTheory.gaussianReal m v)) v).mp
      (Poincare.holds_gaussianReal m v))
```

这里 `v` 是方差，包括 `v = 0` 的 Dirac 情形。比较桥把 legacy Gaussian 的有效常数与
精确最优值传到所选接口。入口还检查任意维数、空测试类型及无穷常数的传递。

## 证明与来源

1. 限制 ambient 测试到 affine support：梯度投影到切向方向，原始能量只能减小。
2. 将 intrinsic 测试沿正交投影延拓：消除法向变化，保持原始能量。这一步不能使用现有
   `Probability.intrinsicMap` 的支撑外分支，因为该映射只保证可测。
3. 对逼近序列逐项应用这两个构造，利用已有 intrinsic `L²` 等距等价，得到能量等式。
4. 对任意 pre-energy，relaxation 在原始测试上不增能量，给出一个常数比较方向；反向在
   每个有限能量点使用 recovery sequence 和 `L²` 方差连续性。这样也处理 `C = 0`，且不
   需要无限能量点的 recovery 或稠密性。
5. 用 `L2.coe_variance_eq_pointwise`、代表元的几乎处处相等和相同梯度积分识别旧测试域。
   有效有限常数因而是 relaxed 最优常数的有限上界；最优值有限时取其 `toNNReal`，
   无穷时有效集合为空，得到 legacy 下确界等式。无需另行假设最优值取到。

数学规格来自本地 Blueprint 的
`thm:ambient-intrinsic-relaxation-equality`、`cor:ambient-intrinsic-constant-equality`、
`thm:legacy-relaxed-holds-equivalence`、`thm:legacy-canonical-constant-comparison`。
抽象 pre-energy 版本和具体 helper 切分是本地设计。历史手稿 Definition 2.1 只提供
方差与梯度能量的归一化；它不是这些比较声明在任意 Borel 测度下的直接出处。

这些定理不要求同一个原始测试的能量等于 relaxed energy。文献 locally Lipschitz 常数
等式已由后续模块接通；Cheeger energy、Markov 性和 whitening 仍未证明。`LogConcave`
及 KLS 主命题已有公开定义，KLS 本身未获证明。书写延续项目采用的 formech 风格：先给用途与例子，
再说明精确范围、来源和未完成部分。

## 构建与状态

从 `formalization/` 运行：

```sh
lake build solutions.LemAmbientIntrinsicPoincareComparison
lake build solutions.LemLegacyRelaxedPoincareComparison
lake build
```

默认构建检查十份证书、公理 guards 和使用示例；这批比较模块没有证明占位。
新增的方差连续性与连续测试映射的 relaxation 比较也有公理 guards。
两个节点的数学规格在 [ledger](../../../../research/a-series/ledger.yaml)，原草案设计保留在
[历史记录](../../../../research/decisions/2026-09-06-poincare-comparison-statements.md)，
证明、签名审计与本轮 Blueprint 修正在
[验收记录](../../../../research/decisions/2026-09-06-poincare-comparison-proofs.md)。
