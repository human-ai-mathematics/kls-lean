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
| 仿射协方差预能量与常数 `C_P^aff` | 通用：`Energy.Euclidean.CovarianceGradientTest ν`、`Energy.Euclidean.covariancePreEnergy ν`、`Energy.Euclidean.covarianceRelaxation ν`；内禀律：`Energy.Affine.energy μ`、`Poincare.Affine.constant μ`、`Poincare.Affine.Holds μ C`；零维 `Poincare.Affine.constant_eq_zero_of_direction_eq_bot` |
| 仿射预能量的对数凹契约 | `hμ.intrinsic_memLp_id_two`、`hμ.intrinsic_ae_hasGradientAt f`、`hμ.intrinsic_gradient_ae_eq_of_ae_eq`、`hμ.intrinsic_covarianceEnergy_eq_of_toL2_eq`；通用前提版本在 `Energy.Euclidean` |
| 加权梯度算子与闭包 | 通用：`Energy.Euclidean.gradientOperator ν B hac`、`Energy.Euclidean.smoothCore ν`、`Energy.PreEnergy.ofLinearPMap T`、`Probability.LocallyDominates ν m`；对数凹：`hν.gradientOperator m B hi`、`hν.gradientOperator_isClosable m B hi`、`hμ.intrinsicGradientOperator m B`、`hμ.affine_energy_eq m B hB` |
| 任意可闭算子的松弛 | `Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem`、`_of_notMem`、`_toAmbient`、`_eq_normSqEnergy`；`Energy.PreEnergy.normSqEnergy S`；`Energy.IsClosable.closure_domRestrict_eq`；选择引理 `Energy.exists_mem_of_isClosed_of_frequently_norm_le` |
| 协方差平方根与平移 | `Covariance.exists_sqrt μ`（通用 `exists_norm_sq_eq_inner_of_isSymmetric`）；`Energy.Euclidean.translateLaw ν c`、`translateL2 ν c`、`L2.variance_translateL2`、`Covariance.operator_translateLaw`、`covarianceRelaxation_translateLaw`、`Poincare.L2Energy.constant_covarianceRelaxation_translateLaw`；通用常数传输 `Poincare.L2Energy.constant_eq_of_linearIsometryEquiv` |
| 线性等距传输 | `Energy.Euclidean.mapLaw ν L`、`mapL2 ν L`、`L2.variance_mapL2`、`Covariance.operator_mapLaw`、`Covariance.operator_map_linearIsometryEquiv`、`Covariance.operator_of_not_memLp`、`Energy.Euclidean.gradient_comp_linearIsometryEquiv`、`covarianceRelaxation_mapLaw`、`Poincare.L2Energy.constant_covarianceRelaxation_mapLaw` |
| 一般线性等价传输与白化 | `Energy.Euclidean.mapEquivLaw ν T`、`mapEquivL2 ν T`、`L2.variance_mapEquivL2`、`Covariance.operator_mapEquivLaw`、`Covariance.operator_map_continuousLinearEquiv`、`Energy.Euclidean.gradient_comp_continuousLinearEquiv`、`covarianceRelaxation_mapEquivLaw`、`Poincare.L2Energy.constant_covarianceRelaxation_mapEquivLaw`、`Probability.affineSupport_mapEquivLaw`、`memLp_id_two_mapEquivLaw`、`integral_id_mapEquivLaw`；白化 `exists_whitening_of_isSymmetric`、`Covariance.exists_whitening μ hpos`；带因子的松弛比较 `Energy.PreEnergy.sequentialRelaxation_comp_le_mul` |
| Lipschitz 梯度松弛与文献常数 | `Energy.Euclidean.lipschitzGradientRelaxation ν m hac`、`Poincare.L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds`、`Poincare.constant_eq_lipschitzGradientRelaxation`、`Energy.Euclidean.covarianceRelaxation_eq_lipschitzGradientRelaxation`（单位协方差）、`covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation`、`KLS.literatureEnergy_eq_ofReal_integral_sq_norm_gradient` |
| KLS 的三种表述 | `KLS.IsotropicBound K`、`KLS.CovarianceBound K`、`KLS.AffineBound K`（宇宙显式）；`KLS.affine_isotropic_reduction K`、`KLS.affineBound_of_isotropicBound`、`KLS.covarianceBound_of_affineBound`、`KLS.isotropicBound_of_covarianceBound`、`KLS.conjecture_of_affineBound`；对数凹：`hμ.exists_isotropic_literatureConstant_eq`、`hμ.literatureConstant_le_opNorm_mul_affine_constant`、`hν.mapEquivLaw T`、`hμ.of_continuousLinearEquiv_map` |
| 环境平移 | 几何：`Probability.affineSupport_translateLaw`、`Probability.direction_affineSupport_translateLaw`、`Probability.translateDirectionEquiv μ b`、`Probability.translateShift μ b`、`Probability.intrinsicMeasure_translateLaw`；能量与常数（任意 Borel 律）：`Energy.Affine.exists_translateLaw_isometry μ b`、`Poincare.Affine.constant_translateLaw_ambient μ b`、`Energy.Euclidean.integral_id_translateLaw`；对数凹：`hμ.translateLaw b`、`hμ.memLp_id_two`、`hμ.integrable_id`、`hμ.integral_id_translateLaw_neg_integral` |
| 仿射闭形式（对数凹） | `hμ.affine_denseRealization`、`hμ.affine_closedQuadratic`、`hμ.affine_agreesOnTests`、`hμ.affine_isSequentialCoreFor`、`hμ.affine_energy_eq_normSqEnergy m B hB`、`hμ.affine_constant_eq_normSqEnergy m B hB`；不需对数凹的 `Energy.Affine.energy_translateLaw μ c`、`Poincare.Affine.constant_translateLaw μ c`；核 `Energy.Euclidean.constantSmoothCore ν` |

`Affine` 表示 CMH 路线的协方差加权前端：把内禀律上的全局 Lipschitz 测试按 `∫⟪Σ∇g,∇g⟫dν` 赋能量，
再取序列松弛；这个名字本身不提供闭性、平移不变性或与 `Canonical` 的比较，闭形式与环境平移不变性由
`hμ.affine_closedQuadratic`、`Poincare.Affine.constant_translateLaw_ambient` 等定理表达；`_translateLaw` 后缀指
内禀律在方向空间内的平移，`_translateLaw_ambient` 指 `μ` 在环境空间 `E` 中的平移。
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
