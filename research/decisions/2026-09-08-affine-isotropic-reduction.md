# 仿射与各向同性 KLS 表述的等价：inspect、statement、语义对齐与证明

日期：2026-09-08（Asia/Shanghai）。基线：`575c82c` 之上的未提交工作树，紧接
[平移不变性记录](2026-09-08-affine-poincare-translation-invariance.md)。Lean/Mathlib 为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示：完成平移不变性后按 atlas ready 继续，
每个节点先 inspect 再 formalize，不提交、不推送。本决定不做 commit、push、远端 CI 或发布。

## 两个候选节点的 inspect

平移不变性认证后，atlas 列出两个解除阻塞的 `inspect_infrastructure` 定理：

- `thm:cmh-recovery-affine-poincare-bound`：打包两条上游 agent 审阅结果（`lem:affine-poincare-w2-liminf`、
  `thm:cmh-implies-affine-poincare`）。本地可用的只有 `Poincare.Affine.constant`、其闭形式与平移不变性；
  仓库与固定的 Mathlib 都没有二次 Wasserstein 距离及其收敛、CMH 常数（含正则紧目标矩映射类、典范矩映射核、
  弱零流闭 Stein 生成元约定）的 Lean 定义，两条上游结果也没有本地证明。tasks.json 记录为 `missing`，
  列出这四条具体缺口；不做形式化。
- `thm:affine-isotropic-reduction`：Blueprint 证明为 "Open." 加草图。需要的基础设施可全部本地实现：
  一般连续线性等价下协方差松弛的传输（Isometry 模块的非等距推广）、正定协方差的逆平方根（谱定理，
  与 `CovarianceSqrt` 同法）、单位权 Lipschitz 梯度松弛常数与文献常数的桥（`LiteratureComparison` 的
  光滑逼近论证换用 Lipschitz 测试）、带常数因子的松弛比较。Mathlib 已有 `covarianceBilin_map`、
  `ContinuousLinearEquiv.comp_right_fderiv`、`LinearEquiv.ofInjectiveEndo`、`Monotone.map_liminf_of_continuousAt`、
  `ENNReal.mul_iInf'`。故 `unchecked → available` 并同轮证明。

## Statement 设计

Blueprint：对固定 K ≥ 0，(1) 每个有限维欧氏空间上每个各向同性对数凹律 ν 满足 C_P^lit(ν) ≤ K；
(2) 每个有限维对数凹律 μ 满足 C_P^lit(μ) ≤ K‖Cov_μ‖；(3) 每个有限维对数凹律 μ 满足 C_P^aff(μ) ≤ K；三者等价，
零维律包含在内。

| 模块 | 声明 | 内容 |
| --- | --- | --- |
| [Energy/Relaxation/Basic.lean](../../formalization/FunctionalInequalities/Energy/Relaxation/Basic.lean) | `PreEnergy.sequentialRelaxation_comp_le_mul` | 沿连续映射的松弛比较，测试能量允许常数因子 κ；前提 P 的松弛有限（排除 κ = 0 与空逼近类） |
| [Energy/Euclidean/CovarianceGradient/LinearEquiv.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/LinearEquiv.lean) | `gradient_comp_continuousLinearEquiv`、`Covariance.operator_map_continuousLinearEquiv`、`mapEquivLaw ν T`、`mapEquivL2`、`L2.variance_mapEquivL2`、`integral_id_mapEquivLaw`、`memLp_id_two_mapEquivLaw`、`CovarianceGradientTest.compContinuousLinearEquiv`、`covarianceRelaxation_mapEquivLaw`、`Poincare.L2Energy.constant_covarianceRelaxation_mapEquivLaw`、`Probability.affineSupport_mapEquivLaw(_eq_top)` | 连续线性等价 T 下：∇(g∘T) = T†∇g∘T；Σ_{T#ν} = TΣT†；L² 拉回等距保方差；重心与二阶矩传输；测试对应、能量相等；松弛与最优常数不变；仿射支撑为像 |
| [Probability/CovarianceWhitening.lean](../../formalization/FunctionalInequalities/Probability/CovarianceWhitening.lean) | `exists_whitening_of_isSymmetric`、`Covariance.exists_whitening` | 正定对称算子 T 有自伴连续线性等价 W 使 ⟪T(Wu),Wv⟫ = ⟪u,v⟫（特征基逐项 λ^{-1/2}，`ofInjectiveEndo`） |
| [Poincare/Euclidean/LipschitzComparison.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/LipschitzComparison.lean) | `lipschitzGradientRelaxation ν m hac`、`KLS.literatureEnergy_eq_ofReal_integral_sq_norm_gradient`、`L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds`、`Poincare.constant_eq_lipschitzGradientRelaxation`、`covarianceRelaxation_eq_lipschitzGradientRelaxation`、`covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation` | B = 1 的加权梯度算子松弛；其有限常数恰为文献常数，最优常数等于 legacy 光滑常数；Σ = 1 时协方差松弛即此松弛；一般时协方差松弛 ≤ ‖Σ‖ × 此松弛（于其有限域） |
| [KLS/LogConcave/IsotropicReduction.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean) | `LogConcave.of_continuousLinearEquiv_map`、`hν.mapEquivLaw T`、`memLp_id_two_translateLaw`、`interior_support_nonempty_of_affineSupport_eq_top` | 对数凹在连续线性等价下的传输；平移保持二阶矩；全仿射支撑给支撑内部非空 |
| | `KLS.IsotropicBound K`、`KLS.CovarianceBound K`、`KLS.AffineBound K` | 三条表述，各对固定宇宙 u 的全部有限维欧氏空间量化 |
| | `hμ.exists_isotropic_literatureConstant_eq`、`hμ.literatureConstant_le_opNorm_mul_affine_constant` | 存在方向空间上的各向同性对数凹律 ν' 使 C_P^aff(μ) = C_P^lit(ν')；C_P^aff(μ) ≤ K ⇒ C_P^lit(μ) ≤ K·ofReal‖Cov_μ‖ |
| | `affineBound_of_isotropicBound`、`covarianceBound_of_affineBound`、`isotropicBound_of_covarianceBound`、`affine_isotropic_reduction K`、`conjecture_of_affineBound` | (1)⇒(3)、(3)⇒(2)、(2)⇒(1)；打包的两组等价；`AffineBound.{0} K → KLS.Conjecture` |

证书 `Solutions.ThmAffineIsotropicReduction.certificate K`：三组等价（(1)↔(2)、(2)↔(3)、(1)↔(3)）与
`AffineBound.{0} K → Conjecture`。两个 `example`：`Fin n` 上由 (3) 得协方差归一化文献界；`Fin 0` 上两常数皆零。

**主张什么。** 上表全部声明与证书。**不主张什么。** 不主张任一表述对某个 K 成立，不主张 KLS；不主张从
`Fin n` 族回到任意空间的反向传递（`Conjecture → CovarianceBound.{0}` 需要沿等距 `E ≃ₗᵢ EuclideanSpace` 传输文献
常数与协方差范数，未做）；不主张白化 W 唯一或正；不做 Cheeger、Dirichlet 或谱隙识别。
**有限范围与零维。** 三条表述在同一宇宙 u 内量化；空间有限维；零维律包含在每条表述中（正定性前提空真，
W 任意，两常数为零，`‖id‖ ≤ 1` 亦覆盖 `‖0‖ = 0`）。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| "每个有限维欧氏空间" | 固定宇宙 u 内的全部 `V : Type u` 及标准实例；三条表述取同一 u | 一致；宇宙固定是 Lean 表达上的限制，记录 |
| (1) 各向同性对数凹 ν：C_P^lit(ν) ≤ K | `IsotropicBound K`，`Isotropic` 为 `def:isotropic-law` 的实现 | 一致 |
| (2) C_P^lit(μ) ≤ K‖Cov_μ‖ | `literatureConstant μ ≤ K * ENNReal.ofReal ‖Covariance.operator μ‖`，与 `KLS.Conjecture` 同形式 | 一致 |
| (3) C_P^aff(μ) ≤ K | `Poincare.Affine.constant μ ≤ K` | 一致 |
| ‖Cov_μ‖ = ‖Cov_{μ,V}‖ 由 `lem:ambient-intrinsic-covariance` | `Covariance.opNorm_operator_intrinsic μ hμ.memLp_id_two`，二阶矩由 `hμ.memLp_id_two` | 一致 |
| 证明句"由平移不变性引理，中心化不改变常数" | 中心化在内禀律的方向空间内进行（`translateLaw ν c`，`constant_covarianceRelaxation_translateLaw`，属 `thm:affine-covariance-relaxation-closed` 的认证内容）；`lem:affine-poincare-translation-invariance` 保留为 `\uses` 依赖但 Lean 证明未调用 | 结论相同，路线不同，记录 |
| "正维时用 Cov^{-1/2} 白化，存在性由 ambient-intrinsic 引理" | `Covariance.exists_whitening` 用 `intrinsic_operator_inner_self_pos` 的正定性；零维不需分情形 | 一致（Lean 统一处理零维） |
| "各向同性不等式拉回给协方差形式不等式，先原始测试再松弛" | `covarianceRelaxation_mapEquivLaw` 在松弛层面直接传输（测试对应 + `sequentialRelaxation_comp_le` 双向），再经 `covarianceRelaxation_eq_lipschitzGradientRelaxation`（Σ = 1）与桥 `constant_eq_lipschitzGradientRelaxation` 到 legacy 常数，`legacy_eq_literature` 到 C_P^lit | 一致 |
| "(3)⇒(2) 由 ⟪Σv,v⟫ ≤ ‖Σ‖‖v‖² 加截断与截尾（局部→全局 Lipschitz）" | 逐点比较 + `sequentialRelaxation_comp_le_mul`；局部/全局 Lipschitz 的过渡改用已认证的光滑紧支撑逼近（`exists_smooth_weighted_L2_approximation`，`lem:covariance-test-core-density`） | 结论相同，方法不同，记录 |
| "(2) 在协方差为恒等时特化为 (1)" | `isotropicBound_of_covarianceBound`：`hiso.covariance_identity`、`norm_id_le`、`ofReal_le_one` | 一致 |
| 零维"零方差，直接成立" | 包含于统一证明；证书 `Fin 0` 例 | 一致 |
| Blueprint 证明标 "Open." | 已改为 leanok，并补充 Lean 路线说明 | — |

未发现 Lean 弱于 Blueprint 之处。`\uses` 的八个前提中，`thm:borell-logconcave-density`（经内禀二阶矩、绝对连续与
支撑边界零测）、`def:isotropic-law`、`def:literature-poincare-constant`、`lem:ambient-intrinsic-covariance`、
`def:affine-poincare-constant`、`thm:affine-covariance-relaxation-closed`（Translation 模块）、`def:log-concave-law`
在 Lean 中实际使用；`lem:affine-poincare-translation-invariance` 如上述未被直接调用。Lean 额外给出
`conjecture_of_affineBound`（Blueprint 未列）。

## 证明路线

- **线性传输。** `comp_right_fderiv` 给 fderiv (g∘T) = fderiv g ∘ T，`adjoint_inner_left` 给 ∇(g∘T) = T†∇g；
  `covarianceBilin_map` 给 Σ_{T#ν} = TΣT†（无二阶矩两侧为零）；L² 拉回沿 T、T⁻¹ 互逆；测试复合的 Lipschitz 常数 K‖T‖；
  松弛双向 `sequentialRelaxation_comp_le`；常数 `constant_eq_of_linearIsometryEquiv`。
- **白化。** e 为特征正交基，λᵢ > 0（正定性于 eᵢ）；W₀ v = ∑ λᵢ^{-1/2}⟪eᵢ,v⟫eᵢ 单射（系数消去）⇒
  `ofInjectiveEndo` 给等价；对称性由系数表达式；⟪T(Wu),Wv⟫ = ∑ λᵢλᵢ^{-1}⟪eᵢ,u⟫⟪eᵢ,v⟫ = ⟪u,v⟫（`sum_inner_mul_inner`）。
- **Lipschitz 桥。** ⇐：文献常数在 Lipschitz 测试上直接成立（Lipschitz ⇒ 局部 Lipschitz，`literatureEnergy` = ofReal∫‖∇g‖²），
  `holds_ofPreEnergy_iff` 传到松弛；⇒：文献测试 f 由光滑紧支撑 fs 逼近（B = 1），fs 是 Lipschitz 测试，
  Var(fs) ≤ C·松弛 ≤ C‖∇fs‖²，方差与能量沿 L² 收敛取极限；常数等式经 `Poincare.constant_le`/`le_constant` 两向，
  不需要下确界达到。
- **带因子比较。** 对每个 B-测试类 x = [g]（∇g ∈ L²）：‖B∇g‖² = ⟪Σ∇g,∇g⟫ ≤ ‖Σ‖‖∇g‖² 逐点，积分单调；
  `sequentialRelaxation_comp_le_mul` 用 `ENNReal.mul_iInf'` 与 `Monotone.map_liminf_of_continuousAt`。
- **(1)⇒(3) 组装。** ν 内禀律；c = −∫x dν；νc = translateLaw ν c（均值零，Σ 不变）；νt = mapEquivLaw νc W
  （均值 W 0 = 0，Σ_t = WΣW = 1，二阶矩、对数凹、仿射支撑 ⊤ 均传输）；
  C_P^aff(μ) = const(ν,cov) = const(νc,cov) = const(νt,cov) = const(νt,Lip) = Poincare.constant νt = C_P^lit(νt) ≤ K。
- **(3)⇒(2) 组装。** C_P^lit(μ) = Poincare.constant ν = const(ν,Lip)；`Poincare.Affine.Holds μ K` ⇒
  `constant_le_mul_of_energy_le_mul` ⇒ const(ν,Lip) ≤ ‖Σ_ν‖₊·K；`opNorm_operator_intrinsic` 换成 ‖Cov_μ‖。

坑：`theorem LogConcave.xxx` 体内 `translateLaw`、`integral_id_translateLaw_neg_integral` 会解析到 `KLS.LogConcave.*`
的同名定理，须写 `Energy.Euclidean.` 全名；`(x : Measure _)` 的强制转换目标留 `_` 会让 elaborator 在 whnf 上超时，
须写全 `Measure (affineSupport μ).direction`；对取值在子类型的 CLM 用 `ext u` 会继续应用 `Subtype.ext`，改用
`ContinuousLinearMap.ext`；`PreEnergy.ofLinearPMap (...)` 无期望类型时宇宙元变量卡住，需标注 `: PreEnergy (Lp ℝ 2 ν)`；
`hcov_t` 中 `↑W`（CLM 强制转换）与 `W`（等价强制转换）语法不同，`rw` 前先 `← hWadj`。

## 元数据同步

- ledger 新增 `thm:affine-isotropic-reduction`（proved / lean，`kind: lemma` 按仓库遗留规则），十七个 proved 节点；
  `check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块。
- Blueprint 定理块锚定二十六条声明与证书，声明与证明标 `leanok`；块尾补充三条表述的 Lean 名称、(2) 的写法与
  `Conjecture` 推论；证明中 "Open." 删除并补充 Lean 路线；`\uses` 未改。
  route-composition.yaml 中该节点的 claim 由 `open` 改为 `proved` 并附 Lean 证据（`check_blueprint` 要求 leanok
  节点的 claim 有显式本地 Lean 证据）。
- 根聚合模块导入 `KLS.LogConcave.IsotropicReduction`；`Poincare/Foundation.lean` 导入 `LinearEquiv`、
  `LipschitzComparison`、`CovarianceWhitening` 并更新文档要点。
- tasks.json：`thm:affine-isotropic-reduction` 改为 `available`，登记四个新模块、`Energy/Relaxation/Basic.lean`、
  `Operator.lean`、`LiteratureComparison.lean`、`LogConcaveComparison.lean`、`CovarianceClosure.lean`、
  `IntrinsicCovariance.lean`、`Isotropic.lean` 与 Mathlib `FiniteDimensional/Basic`、`Module/FiniteDimension`、
  `Spectrum`、`Adjoint`、`Order/LiminfLimsup`、`ENNReal/Inv` 的哈希；`thm:cmh-recovery-affine-poincare-bound` 改为
  `missing` 并列四条缺口；其他任务的证据文件未被触及（`Energy/Relaxation/Basic.lean` 不在既有证据中）。
- 当前指南：HANDOFF、README、`verification.md`、`solutions/README.md`、`formalization/README.md`、`blueprint/README.md`、
  `Energy/README.md`、`KLS/README.md`、`KLS/LogConcave/README.md`、`Poincare/README.md`、`Poincare/Euclidean/README.md`、
  `naming.md`（新增三行）。`KLS/Statement.lean` 的文档说明"未断言与各向同性表述等价"未改动（该文件属 statement
  golden 闭包，等价性由本记录与 `IsotropicReduction` 模块说明）。statement golden、`STATEMENT_CHECKS`、路线配置的
  逻辑结构未动。

## 证据边界

`lake build` 通过（3349 jobs），证书与十五条库级声明有标准公理守卫；`check_ledger`、`check_blueprint`、`atlas check`
与 100 项 Python 测试通过。最终验证收据由 `python3 research/verify.py` 在本记录及所有指南编辑之后生成，其源码 SHA
记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI 或发布。
