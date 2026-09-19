# Lean 公共命名与参数组织

公共名称表达数学对象、操作和结论。命名空间可以跨实现模块组织；证书入口、ledger
节点 ID 和来源标签保留稳定身份。完整本轮映射见
[迁移记录](decisions/2026-09-08-mathematical-api-organization.md)及
[声明映射](api-migration/2026-09-08-name-map.json)。以下省略 `FunctionalInequalities`。

## 短名不重复命名空间

命名空间已经说明的对象或角色，不再写进声明短名。操作用 `apply`、`energy`、
`toL2`、`constant` 等名称；定理短名描述操作的性质。不要把所有假设拼进名称。
本轮补充迁移见 [短名记录](decisions/2026-09-08-namespace-short-names.md)及
[完整映射](api-migration/2026-09-08-short-name-map.json)。例如：

- `WeightedGradient.IsTest.memLp_apply`、`apply_add_ae`、`apply_smul_ae`。
- `LocalSlope.apply`、`apply_const`，不再写 `LocalSlope.slope`。
- `LipschitzApproximation.exists_smooth_weighted_L2`，不再重复 `approximation`。
- `ConditionalFiber.energyAt` 是单个基点处的能量；`energy` 是积分后的能量。
- `SmoothTest.linear`、`energy_linear`；`ProductVariance.decomposition`、`integral_le`。

按数学含义去重：跨对象比较的另一侧、另一个算子或空间仍要标明。
`WeightedGradient` 中关于普通 `gradient` 的辅助引理不能据此伪装成加权梯度结论；
`pullbackEquiv` 的 `Equiv` 表示 L² 拉回构成等价，与底层空间的等价不同。

比较定理的短名也不复述完整类型：两侧共有的 `relaxation`、`constant` 或 `holds`
只写一次，目标使用可区分的短称；完整的数学前提保留在定理类型与文档中。例如
`CovarianceGradient.relaxation_eq_lipschitz`、`relaxation_eq_ofLinearPMap`、
`relaxation_le_mul_lipschitz`，以及 `SmoothTest.constant_eq_ambient`、
`constant_eq_intrinsic`、`constant_eq_lipschitz`。
乘法比较保留 `mul`，不把带系数的不等式命名成直接支配。
详见[比较短名记录](decisions/2026-09-08-comparison-short-names.md)。

## 能量、测试与最优常数

| 数学对象 | 公共入口 | 承载空间与测试类 |
| --- | --- | --- |
| 光滑测试 Poincaré 不等式 | `Poincare.SmoothTest.Admissible`、`energy`、`Holds`、`constant` | 给定测度；全局 C∞、L²、梯度平方可积 |
| 普通光滑梯度松弛 | `Energy.SmoothGradient.Test`、`preEnergy`、`relaxation` | 给定律的 L²；普通梯度权重 |
| 环境普通梯度常数 | `Poincare.SmoothGradient.Ambient.Holds`、`constant` | 在环境空间直接松弛 |
| 内在普通梯度能量和常数 | `Energy.SmoothGradient.Intrinsic.energy`；`Poincare.SmoothGradient.Intrinsic.Holds`、`constant` | 内在支撑的普通梯度松弛，拉回原律的 L² |
| 外部加权梯度 | `Energy.WeightedGradient.apply B g`、`IsTest ν B g`、`operator ν B hac` | 给定律；外部选择的连续线性算子 B；不要求 B 是协方差因子 |
| 普通 Lipschitz 梯度松弛 | `Energy.LipschitzGradient.relaxation ν m hac` | B = id 的全局 Lipschitz L² 测试松弛，保留与光滑测试类的区别 |
| 协方差加权梯度松弛 | `Energy.CovarianceGradient.Test`、`density`、`preEnergy`、`relaxation` | 给定律；全局 Lipschitz、L²、协方差梯度密度可积 |
| 内在协方差能量和常数 | `Energy.CovarianceGradient.Intrinsic.energy`；`Poincare.CovarianceGradient.Intrinsic.Holds`、`constant` | 留在 intrinsicMeasure 的 L²，不拉回环境 L² |
| 局部斜率 | `Energy.LocalSlope.apply`、`energy`、`Admissible` | 点态局部斜率的平方积分；没有 1/2 因子 |
| 局部斜率有限界 | `Poincare.LocalSlope.Holds ν C` | 给定坐标律 ν，未自动取内在律 |
| 内在局部斜率最优常数 | `Poincare.LocalSlope.Intrinsic.constant μ` | 先取 intrinsicMeasure μ，再对有限非负常数取下确界 |
| 任意 L² 能量的优化器 | `Poincare.L2Energy.Holds μ Q C`、`constant μ Q` | 能量 Q 显式；保留无限最优常数及零能量边界 |
| 实轴概率律的分布函数 | `Probability.Line.cdf μ`、`map_cdf_eq_uniform`、`integral_cdf_sub_half_sq` | 给定 `ProbabilityMeasure ℝ`；有密度时的连续性、导数与均匀推前在同一命名空间 |
| 实轴对数凹律的 Borell 密度 | `KLS.LineDensity μ`（字段 `ρ`、`isBorell`）；`d.pos`、`d.mul_le_mul_of_add_eq`、`d.two_mul_cdf_le`、`d.smoothTest_holds`、`d.one_div_le_variance` | 密度数据用结构承载，结论以 `d.` 点记法调用；对数凹前提 `hμ` 与中位数 `hm` 作为显式参数 |
| 一维 4·Var 界 | `KLS.LogConcave.localSlope_constant_le_four_variance`、`localSlope_constant_le_four_evariance`、`smoothTest_holds_four_variance`、`KLS.logConcave_dirac` | 结论以 `hν.` 点记法调用；常数 4 写在名字里，不另设参数 |
| 一维 12·Var 界（历史推论） | `KLS.LogConcave.localSlope_constant_le_twelve_variance`、`smoothTest_holds_twelve_variance`、`localSlope_constant_le_twelve_variance_of_four` | 独立证明保留在 `Line/Poincare.lean`；由 4 推出的版本带 `_of_four` 后缀 |
| 仿射分位数模型 | `Probability.Line.unitUniform`、`affineWeight a b`、`affineQuantile a b p`、`variance_affineQuantile`、`one_div_le_variance_affineQuantile` | 参数顺序 `a b p u`：`a²(1−u)+b²u` 的权重、积分起点 `p`、自变量 `u` |
| 轮廓界与截断测试 | `d.variance_ge_of_affine_bound`、`d.cdf_mul_one_sub_cdf_le_sd_mul`、`KLS.clip a b f`、`clipCentered μ a b f`、`tailIntegral μ h`、`cdfProd μ`、`boundaryTerm μ h`；`d.variance_clip_le`、`d.variance_le_four_variance_mul` | `clip` 是 `FunctionalInequalities.KLS` 下的顶层定义，引理放在 `clip` 命名空间（`clip.of_le`、`clip.of_mem`）；`LineDensity` 上的结论以 `d.` 点记法调用 |
| 锚定半直线 Hardy 界 | `d.setIntegral_Iic_sq_sub_le_of_le hμ hi hm hf hpΩ hpm`、`d.setIntegral_Ioi_sq_sub_le_of_le`、`d.integral_sq_sub_mul_le_left_of_le` | 中位数版本是 `p = m` 的包装；`_of_le` 后缀表示锚点在中位数同侧的序前提 |
| 开集上的局部支配 | `Probability.LocallyDominatesOn ν m Ω`；`LocallyDominates ν m` 是 `Ω = interior support` 的缩写 | 引理放在 `LocallyDominatesOn` 命名空间，用 `h.exists_lintegral_le` 等点记法调用 |
| 局部密度假设与 raw/core 一致 | `Energy.SmoothGradient.LocalDensity ν m`（字段 `Ω`、`ρ` 及五条性质）；`D.absolutelyContinuous`、`D.locallyDominatesOn`；`SmoothGradient.preEnergy_agreesOnTests ν m D` | 假设打包成结构，结论以显式 `(ν m D)` 参数调用；内禀实例在 `SmoothGradient.Intrinsic` 下 |
| 法向坐标障碍 | `Energy.SmoothGradient.normalCoordinate μ n`、`Test.normalCoordinate`、`not_respectsAmbientFibers` | 与 `Poincare.Euclidean.dirac_raw_energy` 并列的命名障碍，不是 ledger 节点 |
| 两点方差恒等式 | `Probability.two_mul_evariance_eq_lintegral_prod ν hX`、`integral_sub_sq_prod` | 概率律 ν 与 a.e. 强可测 X：`2·eVar[X] = ∬‖X t − X s‖ₑ² d(ν⊗ν)`，X ∉ L² 时两边为 ⊤ |
| 条件纤维形式 | `KLS.ConditionalFiber.functional μ ρ`（`Energy.Functional`，值为 `form μ ρ`）；纤维层 `twoPointMeasure κ b`、`twoPointMeasure_swap`、`jump κ b f`、`energyAt_eq_jump_div`；形式层 `energy_le_of_lipschitzWith`、`dense_domain`、`lowerSemicontinuous_form`、`closedQuadratic`、`markovian`、`dirichlet` | 纤维层引理以 `(κ b)` 显式参数调用，形式层以 `(μ ρ)` 显式参数调用；`jump` 是未归一化的平方跳跃积分，`energyAt` 是它除以 `2·eVar[id]` 后的值 |
| 条件纤维能量比较 | `KLS.ConditionalFiber.FiberBound μ ρ κ`（纤维 Poincaré 输入）；`energy_le_of_fiberBound μ ρ hρ m hac hfiber hf`、`literatureConstant_le_of_fiberBound μ ρ hρ m hac hfiber hform` | 输入常数 `κ : NNReal` 与形式差常数 `C : NNReal` 作为隐式参数由假设推断；Haar 参考测度 `m` 与 `hac : μ ≪ m` 显式；`_of_fiberBound` 后缀标明结论来自纤维输入，不写入 `κ` 的取值 |
| 一维 Brunn–Minkowski 与 Prékopa–Leindler | `Probability.Line.volume_add_le_volume_add`、`le_volume_combination`、`prekopaLeindler` | 纯一维测度论工具，与对数凹无关；组合集写法与 `KLS.LogConcave` 一致，右端允许不可测（外测度） |
| Haar 沿直线的 Fubini 拆分 | `Probability.lineMap`、`lineEquiv hθ`、`exists_lintegral_line` | `θ^⊥ × ℝ ≃ₗ E`；比例常数随 `θ` 变化，作为存在量词给出，不计算也不要求关于 `θ` 可测 |
| 对数凹密度到紧集对数凹 | `KLS.LineDensity.logConcave` | 以 `d.` 点记法调用；与 `KLS.LogConcave.exists_lineDensity` 互为反方向 |
| 沿直线的显式切片核 | `KLS.ConditionalFiber.sliceMass`、`SliceGood`、`sliceDensity`、`sliceKernel p hp`；`compProd_baseLaw_sliceKernel`、`ae_sliceKernel_eq`、`sliceKernel_mul_sliceMass` | 可测性证明 `hp : Measurable p` 是显式参数（`Kernel.piecewise` 需要可测集）；不假设对数凹 |
| 对数凹条件纤维 | `KLS.LogConcave.ae_conditionalFiber_logConcave`、`conditionalFiber_fiberBound_four`、`conditionalFiber_energy_le_four_mul`、`conditionalFiber_literatureConstant_le_four_mul`；`conditionalFiber_energy_le_twelve_mul_of_four`、`conditionalFiber_literatureConstant_le_twelve_mul_of_four` | 结论以 `hμ.` 点记法调用；常数 4 写在名字里，由 4 推出的 12 版本带 `_of_four` 后缀 |
| 局部斜率与渐近 Lipschitz 的松弛 | `Energy.AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`；`Energy.LocalSlope.{preEnergy,relaxation}` | 两种 Cheeger 约定各自成对出现；只证无条件的 `LocalSlope.relaxation ≤ AsymptoticLipschitz.relaxation`，相等是显式义务 |
| 度量 Cheeger 能量 | `Energy.Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`；`Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous`、`Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`；`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | 约定选择只记在 `Cheeger.energy := ofLocalSlope` 一处；`_of_absolutelyContinuous` 后缀标明受限范围，无条件版本仍在 WIP |

两种测试对象均支持 `f.energy` 和 `f.toL2`；加权测试性质支持 `hf.memLp`。
不要把数学上不同的测试类、权重、承载空间或松弛构造合并。`ClosedQuadratic` 本身不包含
Markov/Dirichlet 性质；光滑梯度松弛的 Markov/Dirichlet 性是单独定理
`Energy.SmoothGradient.markovian`、`dirichlet`、`Intrinsic.dirichlet`，用磨光正规收缩
`Energy.NormalContraction.smoothed` 与测试复合 `SmoothGradient.Test.compSmoothed` 证明；
普通梯度与局部斜率的最优常数比较不自动给出能量相等。

## 运输与协方差

- 概率律推前：`Probability.translateLaw`、`mapLinearIsometryEquiv`、
  `mapContinuousLinearEquiv`。一般线性等价与欧氏等距的条件在名称中明确区分。
- L² 函数类拉回：`L2.Translation`、`L2.LinearIsometry`、`L2.ContinuousLinearEquiv`
  各自提供 `pullback`、`pullbackInv`、`pullbackEquiv`。拉回从图像律的 L² 到源律的 L²；
  `pullbackInv` 沿逆映射复合。实现复用 Mathlib 的 `Lp.compMeasurePreservingₗᵢ`。
- 能量不变性在 `Energy.CovarianceGradient`；对应最优常数不变性在
  `Poincare.CovarianceGradient`。
- `Poincare.CovarianceGradient.Intrinsic.constant_translateLaw` 是直接的环境律平移不变性。
  `constant_eq_translate_intrinsicMeasure` 比较内在律平移后的最优常数表达。
- `Covariance.exists_inner_eq_norm_sq` 与 `exists_intrinsic_inner_eq_norm_sq` 只给出
  `∃ B, ∀ v, ⟪Σ v,v⟫ = ‖B v‖²`。名称不声称 B² = Σ、自伴、正性或唯一性。
  白化仍是自伴 W 满足 WΣW = id，不升级为正的唯一逆平方根。

## 性质证明与局部名称

对数凹推论留在 `KLS.LogConcave`，从证明推断测度，支持：

```lean
hμ.intrinsicSmooth_constant_eq_localSlope
hμ.intrinsicCovariance_closedQuadratic
hμ.intrinsicCovariance_energy_eq_operator m B hB
hμ.intrinsicCovariance_constant_eq_normSq m B hB
hμ.intrinsic_frontier_support_eq_zero
```

`ConditionalFiber.Nondegenerate` 的定义要求正交基点、有限二阶矩和非零方差；
`energyWithKernel` 明示外部提供的 kernel。`Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top`
统一实数律和一般 Borel 范数空间上的二阶矩判据。
`LipschitzApproximation.kernelDerivativeMass` 是核的导数范数积分相对于核质量的归一化值。

## 作用域和参数

1. 先组织微分性质，再引入测度/L²、Haar/绝对连续和对数凹假设。局部 section 按所需
   结构分组；不在文件头堆积强假设后关闭 `unusedSectionVars`。
2. 从对象或性质证明可推断的测度和测试函数用隐式参数。构造所选择的测度、权重算子和
   必要参考测度保持显式；结构用实例；关键数学前提保留明确证明参数。
3. `variable (hμ : LogConcave μ)` 不会仅因证明体引用 hμ 而把它放入 theorem statement。
   在 theorem 头明确写出，或使用局部 `include hμ in`，并检查 elaborated 参数。
4. 不同一般性混排时允许局部 `omit ... in`；检查保持开启。删除冗余实例、参数显隐或
   次序变化、引理合并分别记录并验证，不能算作纯重命名。
5. 私有的一次性证明辅助使用 `private`。`open`、notation、include、实例和 option
   保持局部。不要用打包全部假设的新结构或 typeclass 缩短变量行。
6. 保留有数学作用的 weighted、L¹/L²、ae、紧支撑、边界、有限性和方向限定。
   Borel 集与 Borell 表示是不同概念。名称负责定位，类型和文档给出完整条件与结论，
   不把整条定理复述成名称。

重命名同步所有消费者、Blueprint 锚点、guards、快照及当前文档。历史
 decisions/explorations 不改写；经审查后更新 golden 与来源哈希，不提供旧名兼容别名。

## 文件与声明作用域

文件按主要数学对象归属：光滑测试前端在 `Poincare/SmoothTest/`，局部斜率和梯度的关系在
`Energy/LocalSlope/Gradient.lean`。对数凹推论用 `LogConcave/{Covariance,Translation,ClosedForm,WeightedGradient,Isotropic,Poincare}`。
同一对象的声明置于对应 namespace；声明头只写短名，不用 `_root_.FunctionalInequalities.…`
绕过错误的外层 namespace。跨对象比较在共同父 namespace 下分组；不为缩短调用增加别名。

### 家族词归目录，不进文件名

一个数学家族有三个以上模块时，family 名归**目录**，文件名只留区分词。已经这样做的有
`Poincare/SmoothTest/`、`Energy/LocalSlope/Gradient.lean`、`Energy/CovarianceGradient/`、
`KLS/LogConcave/Line/`，以及 `Analysis/Semigroup/` 下的 `Resolvent/`、`Exponential/`、
`Yosida/`、`Generated/`，以及 `KLS/` 下的 `ConditionalFiber/`、`Geometry/Cheeger/`、
`Geometry/Coarea/`、`Geometry/Surface/`。不要把家族词重复烤进每个 basename：`LogConcave/Covariance.lean`，
不是 `LogConcave/AffineCovariance.lean`（该次迁移见
[模块映射](api-migration/2026-09-08-library-naming-module-map.json)）。

**新增 `Analysis/` 模块按此规则放入家族子目录**，basename 去掉家族词。
历史平铺模块分批重组：2026-09-17 的 `Graph`、`RankDeficient`、`Sard`、`Vector`、
`Whitney` 迁移见 [Analysis 模块映射](api-migration/2026-09-17-analysis-module-map.json)；
2026-09-19 的半群模块迁移见
[Semigroup 模块映射](api-migration/2026-09-19-semigroup-module-map.json)，KLS 家族迁移见
[KLS 模块映射](api-migration/2026-09-19-kls-module-map.json)。历史 decision 与
exploration 按原路径冻结，不追溯改写；每轮重组必须提供路径映射表，使旧引用仍可解析。

目录只承担分组，不改数学身份：`Analysis/` 的模块无论放在哪个子目录，
namespace 都仍是 `FunctionalInequalities.Analysis`，声明名因此不随目录变动，
ledger、Blueprint、statement snapshot 与公理审计都不受目录重组影响。

例如 `Energy.LocalSlope` 中写 `theorem apply_eq_norm_gradient`。对数凹证明仍可调用
`hμ.intrinsicCovariance_closedQuadratic`、`hμ.intrinsicSmooth_constant_eq_localSlope`、
`hμ.intrinsicWeightedOperator m B`；`weighted` 保留任意外部权重 B 的含义。
完整改动见[全库命名整理](decisions/2026-09-08-library-naming.md)。
