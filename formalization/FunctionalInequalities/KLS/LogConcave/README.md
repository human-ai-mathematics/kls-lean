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
| [Covariance.lean](Covariance.lean) | 仿射协方差预能量在对数凹律上的良定义契约：内禀二阶矩、Lipschitz 测试 a.e. 可微、能量只依赖 L² 类 | 已证明；定义节点 `def:affine-poincare-constant` 的契约，不含闭性或 Poincaré 结论 |
| [WeightedGradient.lean](WeightedGradient.lean) | 全维对数凹律上加权梯度算子 `g ↦ B∇g` 的稠密定义、可闭性、光滑核闭包相等、松弛等于闭包范数平方；内禀律版本 | 已证明；由 `Solutions.LemCovarianceCoreClosure.certificate` 打包，不含 Poincaré、平移不变或 KLS 结论 |
| [ClosedForm.lean](ClosedForm.lean) | 仿射协方差松弛是闭二次型、测试为序列核、内禀律平移下的等距与常数不变、与 ℝ + C_c^∞ 核上闭算子范数平方（CMH 闭形式）相等 | 已证明；由 `Solutions.ThmAffineCovarianceRelaxationClosed.certificate` 打包，不含 Poincaré 不等式、环境平移不变或 KLS |
| [Translation.lean](Translation.lean) | 环境平移保持紧集对数凹；对数凹律的环境二阶矩与重心；平移到负重心得到零均值律 | 已证明；与 `Poincare/CovarianceGradient/Translation.lean` 的常数不变性一起由 `Solutions.LemAffinePoincareTranslationInvariance.certificate` 打包，不含 Poincaré 不等式、各向同性归约或 KLS |
| [Isotropic.lean](Isotropic.lean) | 连续线性等价保持对数凹；三条 KLS 表述 `IsotropicBound`、`CovarianceBound`、`AffineBound` 及其两两等价；中心化、白化后的各向同性律；`AffineBound → Conjecture` | 已证明；由 `Solutions.ThmAffineIsotropicReduction.certificate` 打包，不断言任一表述对某个 K 成立 |
| [Line/Density.lean](Line/Density.lean) | 实轴对数凹律的 Borell 密度结构 `LineDensity`；支撑内部为区间且承载全部质量；分布值严格在 (0,1) 的点落在支撑内部；`log ρ` 的弦下界、外推上界与中位数处的支撑指数 | 已证明；不含 Poincaré 结论 |
| [Line/Hazard.lean](Line/Hazard.lean) | 四点不等式 `ρ a ρ e ≤ ρ b ρ c`；单调失效率 `ρ x μ(Ioi y) ≤ ρ y μ(Ioi x)` 及其镜像；中位数界 `2ρ(m)(1−F) ≤ ρ`、`2ρ(m)F ≤ ρ`；支撑线界 `ρ ≤ ρ(m) + k(F − 1/2)` | 已证明；使用 `Probability/Line/{Cdf,ExpIntegral}` |
| [Line/Hardy.lean](Line/Hardy.lean) | 区间上的分部积分 Hardy 步骤；半直线上的有理端点有向并，锚点可取中位数同侧任意内点（常数仍为 `1/ρ(m)²`）；光滑测试 Poincaré 不等式 `SmoothTest.Holds ν (1/ρ(m))²` | 已证明；常数以中位数密度表达，不含方差 |
| [Line/Variance.lean](Line/Variance.lean) | 比较函数 `φ(F x) − (x − m)` 的单调性；`∫(x−m)(F−1/2) dν ≥ 1/(12ρ(m))`；Bobkov 方差界 `1/(12ρ(m)²) ≤ Var` | 已证明；对均匀律取等 |
| [Line/Poincare.lean](Line/Poincare.lean) | Bobkov 常数：`C_P^lit(ν) ≤ 12·Var_ν`（实与扩展方差两种形式）；零维仿射支撑时常数为零；`logConcave_dirac` | 已证明；独立于常数 4 的路线，作为历史推论保留 |
| [Line/Isoperimetry.lean](Line/Isoperimetry.lean) | 一维等周（2026-09-19）：`LineDensity.mul_min_le_relativePerimeter`（`2ρ(m)·min(νU,1−νU) ≤ P_ρ(U)`，对任意光滑域，不用边界离散）、`two_mul_le_minkowskiConstant`（`2ρ(m) ≤ h_M`，经 `h_M = h_S`）、`le_two_mul`（`ρ ≤ 2ρ(m)`）、`one_div_le_evariance`（`Var ≥ 1/(12M²)`）、`interior_support_nonempty` |
| [Line/Buser.lean](Line/Buser.lean) | Buser 半阶段一（2026-09-19）：`evariance_le_smoothTest_constant`（线性测试）、`Isoperimetry.minkowskiConstant_map`（等距搬运）、`LogConcave.inv_minkowskiConstant_sq_le`（直线上 `Ψ² ≤ 12·C_P^smooth`）、`LogConcave.inverseScale_sq_le_of_finrank_le_one`（仿射支撑维数 `≤ 1` 时 `Ψ_KLS² ≤ 12·C_P^lit`）；`n ≥ 2` 与常数 `π` 未证 |
| [Line/Profile.lean](Line/Profile.lean) | 均值落在支撑内部；支撑线 `ρ ≤ A(1−F)+BF`（`A,B ≥ 0`）；仿射模型方差下界 `1/(√A+√B)⁴ ≤ Var`；轮廓界 `F(1−F) ≤ σρ` | 已证明；使用 `Probability/Line/AffineProfile.lean` 的仿射分位数模型 |
| [Line/SharpHardy.lean](Line/SharpHardy.lean) | 截断测试 `clip a b f`、居中版本与尾积分 `G̃`；分部积分 `∫h² dμ = −∫_a^b f' G̃`；基态恒等式与边界项控制；`∫_a^b G̃²ρ/W² ≤ 4∫h² dμ`；`Var(clip) ≤ 4·Var_ν·∫f'² dν` | 已证明；区间 `[a,b] ⊆ Ω` 需跨越中位数 |
| [Line/SharpPoincare.lean](Line/SharpPoincare.lean) | 尾项消失（锚定半直线 Hardy 界 + 积分的绝对连续性）；`(1+δ)` 分裂；`SmoothTest.Holds ν (4·Var)`；`C_P^lit(ν) ≤ 4·Var_ν`（实与扩展方差两种形式），`12` 作为推论 | 已证明；由 `Solutions.ThmOneDimensionalLogConcavePoincare.certificate` 打包，常数 4 在指数律取等，不断言高维结论 |
| [Line/OfDensity.lean](Line/OfDensity.lean) | 反方向：有对数凹 Lebesgue 密度的实轴概率律是紧集对数凹 `LineDensity.logConcave` | 已证明；用 `Probability/Line/BrunnMinkowski.lean` 的一维 Prékopa–Leindler，与 `LogConcave.exists_lineDensity` 互逆 |

局部依赖关系为：

```text
Definitions → Transport → AbsoluteContinuity → BorellRepresentation → Covariance → Translation ─┐
            → Borel ─────────────────────────────┘                  → WeightedGradient → ClosedForm   → Isotropic
```

`Line/` 的局部依赖为 `Density → Hazard → {Hardy, Variance} → Poincare`；`Density` 使用
`BorellRepresentation` 与 `Probability/Line/Cdf`，`Poincare` 另外使用 `Poincare.lean`（光滑测试
与文献常数相等）及 `Isotropic`（全仿射支撑给出支撑内部非空）。

`WeightedGradient` 使用 `Energy/WeightedGradient/{Basic,Closable,Core}`：对数凹律
只负责提供三条前提（`ν ≪ Haar`、支撑边界零测、Haar 在支撑内部紧集上被 `ν` 局部支配）。

`Isotropic` 另外使用 `Energy/CovarianceGradient/LinearEquiv`（一般线性等价下的传输）、
`Probability/CovarianceWhitening`（正定协方差的自伴逆平方根）与 `Poincare/LipschitzGradient/Comparison`
（单位权 Lipschitz 梯度松弛与文献常数的桥）；对数凹只负责像律的对数凹性、全支撑与内禀协方差正定。

`Translation` 另外使用 `Poincare/CovarianceGradient/Translation`（平移后的仿射支撑、方向与内禀律的识别，
以及对任意 Borel 律成立的常数不变性）与 `Transport` 的仿射等距传输；对数凹只负责平移律的对数凹性与环境二阶矩。

`Covariance` 另外使用 `Energy/CovarianceGradient/Basic`，那里定义了对任意概率律
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
[Poincare.lean](../../KLS/LogConcave/Poincare.lean) 中组合这些工具。
现有声明名称保持不变；旧模块路径不保留转发文件。路径映射见
[迁移记录](../../../../research/explorations/2026-09-07-logconcave-module-layout.md)。
