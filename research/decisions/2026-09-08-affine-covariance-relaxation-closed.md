# 仿射协方差松弛即闭协方差形式：statement、语义对齐与证明

日期：2026-09-08（Asia/Shanghai）。基线：`575c82c` 之上的未提交工作树，紧接
[协方差核闭包记录](2026-09-08-covariance-core-closure.md)。Lean/Mathlib 为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示："往这个方向以及按照这个风格
接着做，但是不提交"。本决定不做 commit、push、远端 CI 或发布。

## 节点选择

`lem:covariance-core-closure` 认证后，`thm:affine-covariance-relaxation-closed` 的全部 `\uses`
前提均已认证，成为 atlas 中唯一解除阻塞的 `inspect_infrastructure` 叶节点，且它是
`lem:affine-poincare-translation-invariance`、`thm:affine-isotropic-reduction`、
`thm:cmh-recovery-affine-poincare-bound` 的前提。

## Statement 设计

Blueprint：对每个有限维欧氏空间上的对数凹律 μ，P^aff_μ 是二次的、实现稠密、可闭；其序列松弛是
闭二次型并在每个全局 Lipschitz 测试上等于原始协方差能量；改变仿射原点即平移 ν，沿平移拉回是
保持方差与协方差能量的 L² 等距；在此等距识别下 𝓔^aff_μ 是 CMH 来源使用的闭协方差形式，
C_P^aff(μ) 是同一最优常数。

Lean 分四块。

| 模块 | 声明 | 内容 |
| --- | --- | --- |
| [Probability/CovarianceSqrt.lean](../../formalization/FunctionalInequalities/Probability/CovarianceSqrt.lean) | `exists_norm_sq_eq_inner_of_isSymmetric`、`Covariance.exists_sqrt μ` | 有限维对称非负算子 T 存在 B 使 ⟪Tv,v⟫ = ‖Bv‖²（谱定理特征基逐项开方）；协方差算子是这样的 T，含无二阶矩时的零算子与零维 |
| [Energy/Relaxation/LinearPMap.lean](../../formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean) | `PreEnergy.normSqEnergy S`、`sequentialRelaxation_ofLinearPMap_eq_normSqEnergy` | 部分定义算子的能量 ‖S x‖²（域外为 ⊤）；可闭 T 的松弛等于其闭包的该能量 |
| [Energy/Euclidean/CovarianceGradient/Translation.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Translation.lean) | `translateLaw ν c`、`translateL2 ν c`、`L2.variance_translateL2`、`Covariance.operator_translateLaw`、`CovarianceGradientTest.translate`、`covarianceRelaxation_translateLaw`、`Poincare.L2Energy.constant_covarianceRelaxation_translateLaw` | ν 沿 x ↦ c + x 的像；拉回 L² 等距等价；方差不变；协方差算子不变；测试按平移对应且能量相等；松弛沿等距拉回；最优常数相等 |
| [Poincare/L2Energy.lean](../../formalization/FunctionalInequalities/Poincare/L2Energy.lean) | `L2Energy.constant_eq_of_linearIsometryEquiv` | 通用：保方差且交换能量的 L² 等距等价下最优常数相等 |
| [Energy/Euclidean/CovarianceGradient/Core.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Core.lean) | `constantSmoothCore ν`、`constantSmoothCore_le_domain_gradientOperator` | ℝ + C_c^∞(V) 的 L² 类构成的子模，含于算子域 |
| [KLS/LogConcave/AffineClosedForm.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/AffineClosedForm.lean) | `exists_intrinsic_covariance_sqrt μ`、`hμ.affine_denseRealization`、`hμ.affine_closedQuadratic`、`hμ.affine_agreesOnTests`、`hμ.affine_isSequentialCoreFor`、`hμ.affine_respectsAmbientFibers` | 内禀协方差的平方根 B；P^aff 实现稠密；`Energy.Affine.energy μ` 为 `ClosedQuadratic`；松弛在测试上等于原始能量，测试为序列核 |
| | `Energy.Affine.energy_translateLaw μ c`、`Poincare.Affine.constant_translateLaw μ c` | 内禀律平移后的协方差松弛等于沿等距拉回的仿射松弛；仿射常数等于任何平移律的最优常数（不需对数凹） |
| | `hμ.affine_energy_eq_normSqEnergy m B hB`、`hμ.affine_constant_eq_normSqEnergy m B hB` | 仿射松弛 = B∇ 限制到 ℝ + C_c^∞ 核后闭包的范数平方能量（CMH 闭形式）；C_P^aff 是该闭形式的最优常数 |

证书 `Solutions.ThmAffineCovarianceRelaxationClosed.certificate`：对任意对数凹 μ 打包实现稠密、
闭二次型、序列核、对每个 c ∈ V 的四条平移结论（协方差算子不变、方差不变、松弛拉回、常数相等），
以及存在平方根 B 使 B∇ 可闭、仿射松弛等于核闭形式、仿射常数等于其最优常数。两个 `example`：
Fin n 上任意维数、Fin 0（常数为零且仍是闭二次型）。

**主张什么。** 上表全部声明及证书。**不主张什么。** 不主张任何 Poincaré 不等式或常数有限；不主张
μ 在环境空间 E 中平移时 C_P^aff 不变（`lem:affine-poincare-translation-invariance`，下一节点）；
不主张各向同性归约、白化或 KLS；不主张 B 对称或唯一；不把 `CovarianceGradientTest` 做成 Lean 模
（二次性通过算子表示表达）。**有限范围与零维。** 空间有限维；测试全局 Lipschitz；零维时 B = 0，
所有类为常数，常数为零。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| P^aff_μ 二次 | 通过 B：P^aff 与二次预能量 `ofLinearPMap (B∇)` 有相同实现与能量（`affine_energy_eq`、`isGradientTest_iff_exists_covarianceGradientTest`） | 一致；表达方式不同，记录 |
| 实现稠密 | `affine_denseRealization` | 一致 |
| 可闭 | `intrinsicGradientOperator_isClosable`（对 B∇） | 一致 |
| 松弛是闭二次型 | `affine_closedQuadratic : ClosedQuadratic (Energy.Affine.energy μ)` | 一致 |
| 在每个全局 Lipschitz 测试上等于原始协方差能量 | `affine_agreesOnTests`、`affine_isSequentialCoreFor` | 一致 |
| 改变仿射原点即平移 ν；拉回是保持方差与协方差能量的 L² 等距 | `translateL2`、`variance_translateL2`、`covarianceEnergy_translate`、`operator_translateLaw`，对任意 c ∈ V、任意 Borel 律 | Lean 更强（不需对数凹），记录 |
| 在此识别下 𝓔^aff_μ 是 CMH 闭协方差形式 | `affine_energy_eq_normSqEnergy`：等于 B∇ 在 `constantSmoothCore`（ℝ + C_c^∞ 的类）上闭包的范数平方能量；`energy_translateLaw` 给平移下的拉回等式 | 一致；CMH 来源的"限制到 K_ν"由 L² 类模 ν 自动实现 |
| C_P^aff(μ) 是同一最优常数 | `affine_constant_eq_normSqEnergy`、`constant_translateLaw` | 一致 |
| 证明末句：零维只有常数类、能量为零 | 证书 `Fin 0` 例：常数为零；`domain_gradientOperator_eq_top_of_subsingleton` | 一致 |

未发现 Lean 弱于 Blueprint 之处。Blueprint `\uses` 的五个前提在 Lean 中均实际使用：定义节点的
`covariancePreEnergy`；Borell 表示（经 CovarianceClosure 的局部支配与二阶矩）；
`lem:ambient-intrinsic-covariance` 未直接调用——Σ = Cov_ν 直接取自 `Covariance.operator (intrinsicMeasure μ)`，
与环境协方差的关系不需要；`thm:quadratic-relaxation-closed`（`closedQuadratic_sequentialRelaxation`）；
`lem:covariance-core-closure`。

## 证明路线

- 平方根：e 为 T 的特征正交基，λ 为特征值；λᵢ = ⟪T eᵢ, eᵢ⟫ ≥ 0；B v = ∑ √λᵢ ⟪eᵢ,v⟫ eᵢ；
  ‖Bv‖² = ∑ λᵢ⟪eᵢ,v⟫² = ⟪Tv,v⟫（`sum_repr'`、`apply_eigenvectorBasis`、`inner_right_fintype`）。
- 闭二次型：`affine_energy_eq` 把仿射松弛改写为 `ofLinearPMap` 的松弛，`ofLinearPMap_quadratic` 与
  域稠密给 `closedQuadratic_sequentialRelaxation`。
- 序列核：`sequentialRelaxation_ofLinearPMap_toAmbient` 给 ‖T [f]‖²，`gradientOperator_apply` 与
  `coe_covarianceEnergy_eq_norm_sq` 化为协方差能量；`SequentiallyGenerates` 是定义 `rfl`。
- 平移：`measurePreserving_translate(_symm)`、`compMeasurePreservingₗᵢ` 与 `AEEqFun.compMeasurePreserving_congr`
  给等距等价；`variance_fun_comp` 给方差；`covarianceBilin_map_const_add` 给算子；
  `fderiv_comp_add_left` 给梯度平移；`sequentialRelaxation_comp_le` 两方向给松弛拉回；
  常数经 `constant_eq_of_linearIsometryEquiv`。
- 闭形式：`sequentialRelaxation_ofLinearPMap_eq_normSqEnergy` 与核闭包相等
  `closure_domRestrict_intrinsicGradientOperator`（核在 smoothCore 与域之间）。

## 元数据同步

- ledger 新增 `thm:affine-covariance-relaxation-closed`（proved / lean，`kind: lemma` 按仓库遗留规则），
  十五个 proved 节点；`check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块。
- Blueprint 定理块锚定十七条声明与证书，声明与证明标 `leanok`；块尾补充 Lean 表达方式说明；
  证明末尾"待 Lean 实现"改为已认证的打包内容；`\uses` 未改。
- 根聚合模块导入 `KLS.LogConcave.AffineClosedForm`；`Poincare/Foundation.lean` 导入 Translation 与
  CovarianceSqrt。
- tasks.json：节点改为 `available` 并登记十二项源码与 Mathlib 哈希；被触及文件的其他任务哈希刷新。
- 当前指南：HANDOFF、README、`verification.md`、`solutions/README.md`、`blueprint/README.md`、
  `Energy/README.md`、`KLS/LogConcave/README.md`、`naming.md`。statement golden、`STATEMENT_CHECKS`、
  路线配置未动。

## 证据边界

`lake build` 通过，证书与十条库级声明有标准公理守卫。最终验证收据由 `python3 research/verify.py`
在本记录及所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任
第三方编译导入；未做隔离重建、远端 CI 或发布。
