# 仿射 Poincaré 常数的环境平移不变性：statement、语义对齐与证明

日期：2026-09-08（Asia/Shanghai）。基线：`575c82c` 之上的未提交工作树，紧接
[仿射闭形式记录](2026-09-08-affine-covariance-relaxation-closed.md)。Lean/Mathlib 为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示：按 atlas 继续做
`lem:affine-poincare-translation-invariance`，先 inspect 再 formalize，不提交、不推送。
本决定不做 commit、push、远端 CI 或发布。

## 节点选择

`thm:affine-covariance-relaxation-closed` 认证后，atlas 把 `lem:affine-poincare-translation-invariance`
列为解除阻塞的 `inspect_infrastructure` 叶节点；它是 `thm:affine-isotropic-reduction` 与
`cor:cmh-recovery-sequence-suffices` 的前提。Inspect 结论：Mathlib 已有 `covarianceBilin_map`（线性映射下
协方差的伴随公式）、`LinearIsometryEquiv.adjoint_eq_symm`、`ContinuousLinearEquiv.comp_right_fderiv`（无可微前提的
复合链式法则）、`AffineSubspace.map_direction`/`map_le_iff_le_comap`、`LinearIsometryEquiv.ofEq`；仓库已有
`translateLaw`/`translateL2`（内禀律在方向空间内平移）、`LogConcave.of_affineIsometry_map` 与
`hμ.intrinsic_memLp_id_two`。缺的只是三段本地粘合：方向空间之间的线性等距传输、平移后仿射支撑与内禀律的识别、
对数凹律的环境二阶矩。全部可直接实现，故 `unchecked → available` 并同轮证明。

## Statement 设计

Blueprint：μ 为有限维欧氏空间 E 上的对数凹律，b ∈ E，τ_b(x) = x + b。则 (τ_b)#μ 对数凹且
C_P^aff((τ_b)#μ) = C_P^aff(μ)；特别地平移到负重心得到中心化律而常数不变。

Lean 中 (τ_b)#μ 取已有的 `Energy.Euclidean.translateLaw μ b`（μ 沿 x ↦ b + x 的像；`translateLaw` 对任意有限维
Hilbert 空间上的律定义，这里直接用于 E）。分三个模块，先通用后具体。

| 模块 | 声明 | 内容 |
| --- | --- | --- |
| [Energy/Euclidean/CovarianceGradient/Isometry.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Isometry.lean) | `gradient_comp_linearIsometryEquiv g L x` | ∇(g ∘ L)(x) = L⁻¹ ∇g(Lx)，无可微前提（不可微点两边同为零） |
| | `Covariance.operator_of_not_memLp`、`Covariance.operator_map_linearIsometryEquiv`、`Covariance.operator_mapLaw`、`inner_operator_mapLaw`、`inner_operator_mapLaw_apply` | 无二阶矩时算子为零；像律的协方差算子是共轭 L Σ L⁻¹；二次型经 L⁻¹/L 读取 |
| | `mapLaw ν L`、`measurePreserving_mapLaw(_symm)`、`mapForward`/`mapBackward`、`mapL2 ν L`、`L2.variance_mapL2` | 线性等距等价 L 下的像律；沿 L 拉回的 L² 等距等价；方差不变 |
| | `CovarianceGradientTest.compLinearIsometryEquiv hmp hcov g`、`covarianceEnergy_compLinearIsometryEquiv`、`toL2_compLinearIsometryEquiv` | 测试按复合对应，协方差能量相等，实现为拉回类 |
| | `covarianceRelaxation_mapLaw`、`Poincare.L2Energy.constant_covarianceRelaxation_mapLaw` | 协方差松弛沿 `mapL2` 拉回；最优常数相等 |
| [Poincare/Euclidean/AffineTranslation.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/AffineTranslation.lean) | `Probability.coe_intrinsicMap_of_mem`、`affineSupport_translateLaw`、`direction_affineSupport_translateLaw` | 支撑上内禀坐标 = x − supportPoint；平移律的仿射支撑是 `(affineSupport μ).map (constVAdd b)`；方向子模相等 |
| | `Probability.translateDirectionEquiv μ b`、`translateShift μ b`、`intrinsicMap_translateLaw`、`intrinsicMeasure_translateLaw` | 两方向子模的 `ofEq` 线性等距；坐标偏移 b + supportPoint μ − supportPoint μ'；内禀律的识别 ν' = translateLaw (mapLaw ν L) c |
| | `Energy.Euclidean.integral_id_translateLaw`、`integral_id_translateLaw_neg_integral` | 平移律的重心 = c + 重心；平移到负重心后均值为零（前提 `Integrable id`） |
| | `Energy.Affine.exists_translateLaw_isometry μ b` | 存在 L²(ν') ≃ₗᵢ L²(ν) 保方差且交换两仿射松弛 |
| | `Poincare.Affine.constant_translateLaw_ambient μ b` | `Poincare.Affine.constant (translateLaw μ b) = Poincare.Affine.constant μ`，对任意 Borel 律 |
| [KLS/LogConcave/AffineTranslation.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/AffineTranslation.lean) | `hμ.translateLaw b` | 平移律对数凹（逆平移是仿射等距，`of_affineIsometry_map`） |
| | `hμ.memLp_id_two`、`hμ.integrable_id` | 环境二阶矩：内禀二阶矩 + `reconstruct` 为仿射等距的范数界；重心存在 |
| | `hμ.integral_id_translateLaw_neg_integral` | 平移到负重心后均值为零 |

证书 `Solutions.LemAffinePoincareTranslationInvariance.certificate`：对任意对数凹 μ 打包，对每个 b：平移律对数凹、
环境协方差算子不变（已有 `Covariance.operator_translateLaw`）、仿射支撑方向不变、存在保方差且交换两仿射松弛的
L² 等距等价、常数相等；另加 `MemLp id 2 μ` 与负重心平移的零均值。两个 `example`：`Fin n` 上平移到负重心保持对数凹、
零均值、常数不变；`Fin 0` 上两常数皆零且平移律对数凹。

**主张什么。** 上表全部声明与证书。**不主张什么。** 不主张任何 Poincaré 不等式或常数有限；不主张各向同性归约或
白化（`thm:affine-isotropic-reduction`）；不主张 E 上非平移仿射映射下的不变性（内禀层面的线性等距传输是通用的，
但环境层面只对平移做了支撑/内禀律识别）；不把 `exists_translateLaw_isometry` 的等距做成具名 `def`（它是
`translateL2 ∘ mapL2` 经内禀律等式 `intrinsicMeasure_translateLaw` 重写后的组合，用 ∃ 表达避免沿测度等式的类型转换）。
**有限范围与零维。** 空间有限维；测试全局 Lipschitz；零维方向空间包含在每条结论中（此时 `mapLaw`、`translateLaw`
的 L² 皆为常数类，两常数为零）。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| μ 对数凹 | 常数等式、协方差不变、方向不变与 L² 等距对任意 Borel 律成立；对数凹只用于平移律的对数凹性与重心存在 | Lean 更强（前提更弱），记录 |
| τ_b(x) = x + b | `translateLaw μ b` 是 x ↦ b + x 的像（加法交换，同一映射） | 一致 |
| (τ_b)#μ 对数凹 | `hμ.translateLaw b`；证明用逆平移（仿射等距）把平移律送回 μ，紧集像作为测试集 | 一致；Blueprint 证明句"紧集与 Minkowski 组合与平移交换"在 Lean 中由 `of_affineIsometry_map` 的一般仿射等距版本承担 |
| C_P^aff((τ_b)#μ) = C_P^aff(μ) | `Poincare.Affine.constant_translateLaw_ambient` | 一致 |
| 证明句"平移保持协方差" | 环境：`Covariance.operator_translateLaw`；内禀：`Covariance.operator_mapLaw`（共轭 L Σ L⁻¹，L 为 `ofEq`，取值上是恒等）与 `Covariance.operator_translateLaw` | 一致 |
| 证明句"把两个内禀律用 L² 等距识别" | `intrinsicMeasure_translateLaw` 给 ν' = translateLaw (mapLaw ν L) c；等距为 `(translateL2 _ c).trans (mapL2 ν L)`；`exists_translateLaw_isometry` | 一致 |
| 证明句"等距保方差并交换协方差预能量，故交换松弛与最优常数" | `L2.variance_mapL2`/`variance_translateL2`；测试对应 `compLinearIsometryEquiv`/`translate`；`covarianceRelaxation_mapLaw`/`_translateLaw`；`constant_covarianceRelaxation_mapLaw`/`_translateLaw` | 一致 |
| 特别地平移到负重心得到中心化律 | `hμ.memLp_id_two` 给重心存在；`hμ.integral_id_translateLaw_neg_integral` 给 ∫ x d(τ_{−m}#μ) = 0 | 一致；"中心化"取 `KLS.Isotropic.mean_zero` 同一形式 ∫ x dμ = 0 |
| 重心存在由 `thm:borell-logconcave-density` 给出 | 经 `hμ.intrinsic_memLp_id_two`（Borell 矩定理）加 `reconstruct` 的仿射等距范数界传到环境律 | 一致 |
| 零维 | 证书 `Fin 0` 例：两常数皆零 | 一致 |

未发现 Lean 弱于 Blueprint 之处。Blueprint `\uses` 的四个前提在 Lean 中均实际使用：`def:log-concave-law`
（`LogConcave`）、`def:affine-poincare-constant`（`Poincare.Affine.constant`）、`thm:borell-logconcave-density`
（经内禀二阶矩）、`thm:affine-covariance-relaxation-closed`（其 Translation 模块的 `translateL2`、
`covarianceRelaxation_translateLaw`、`constant_covarianceRelaxation_translateLaw`）。

## 证明路线

- **梯度复合。** `toDual` 单射；`ContinuousLinearEquiv.comp_right_fderiv` 给 fderiv (g∘L) x = fderiv g (Lx) ∘ L；
  对每个 v，⟪∇g(Lx), Lv⟫ = ⟪L L⁻¹∇g(Lx), Lv⟫ = ⟪L⁻¹∇g(Lx), v⟫（`inner_map_map`）。
- **协方差共轭。** 有二阶矩：`covarianceBilin_map` + `adjoint_eq_symm` + `inner_map_map`；无二阶矩：像律亦无二阶矩
  （`memLp_map_measure_iff` 与 L⁻¹ 复合），两侧算子为零（`covarianceBilin_of_not_memLp`）。
- **L² 等距与松弛。** 与 Translation 模块逐条平行：`compMeasurePreservingₗᵢ` 沿 L、L⁻¹，`compMeasurePreserving_comp_apply`
  与 `AEEqFun.compMeasurePreserving_congr` 给互逆；`variance_fun_comp` 给方差；`sequentialRelaxation_comp_le` 两方向给松弛拉回；
  `constant_eq_of_linearIsometryEquiv` 给常数。
- **仿射支撑。** ≤：平移律 a.e. 落在 `map (constVAdd b)`（`ae_map_iff`），且该像闭；≥：`map_le_iff_le_comap`，
  μ a.e. 点经平移落在 μ' 的仿射支撑（`ae_of_ae_map`），comap 闭。方向：`map_direction` 与 `constVAdd` 线性部分为恒等。
- **内禀律识别。** 支撑上 `intrinsicMap μ x = x − supportPoint μ`（`coordinateEquiv` 为 `vaddConst` 的逆）；
  intrinsicMap μ' (b + x) = (b + supportPoint μ − supportPoint μ') + (x − supportPoint μ)（`abel`）；
  `ProbabilityMeasure.toMeasure_injective` + `Measure.map_map` + `Measure.map_congr`（a.e. 于仿射支撑）。
- **常数。** 展开 `Poincare.Affine.constant`，`rw [intrinsicMeasure_translateLaw]`（motive 在 `covarianceRelaxation ν'` 形式下
  类型正确），再用 `constant_covarianceRelaxation_translateLaw` 与 `constant_covarianceRelaxation_mapLaw`。
- **环境二阶矩。** ‖reconstruct v‖ ≤ ‖reconstruct 0‖ + ‖v‖（`AffineIsometry.dist_map`），`MemLp.of_le` 于内禀律，
  `memLp_map_measure_iff` 拉回 μ，`reconstruct_intrinsicMap_ae` 换成恒等。
- **重心。** `integral_map` 与 `integral_add`、`integral_const`（概率测度 `probReal_univ`）。

坑：`LinearIsometryEquiv.ofEq` 的取值引理不要用 `rfl` 证（kernel 超时），用 Mathlib 的 `coe_ofEq_apply`；
`closed_of_finiteDimensional` 需显式给出子空间，否则实例问题因元变量卡住；`Fin n` 例中 `Measure _` 需写全类型，
否则积分变量被推断为 ℕ；`have` 中的 `∀ (W : Type*)` 会锁死宇宙，改为顶层通用引理 `Covariance.operator_of_not_memLp`。

## 元数据同步

- ledger 新增 `lem:affine-poincare-translation-invariance`（proved / lean，`kind: lemma`），十六个 proved 节点；
  `check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块。
- Blueprint 引理块锚定十六条声明与证书，声明与证明标 `leanok`；块尾补充 Lean 中 (τ_b)#μ 的表达、内禀律识别与
  "常数等式对任意 Borel 律成立"的说明；`\uses` 未改。
- 根聚合模块导入 `KLS.LogConcave.AffineTranslation`；`Poincare/Foundation.lean` 导入 `CovarianceGradient.Isometry`
  与 `Poincare.Euclidean.AffineTranslation` 并更新文档要点。
- tasks.json：节点改为 `available`，登记三个新模块、`Translation.lean`、`Transport.lean`、`AffineSupport.lean`、
  `KLS/LogConcave/AffineCovariance.lean` 与 Mathlib `FDeriv/Equiv`、`InnerProductSpace/Adjoint`、`CovarianceBilin`、
  `AffineSubspace/Basic`、`LinearIsometry` 的哈希；本次未改动其他任务的证据文件，哈希扫描全部匹配。
- 当前指南：HANDOFF、README、`verification.md`、`solutions/README.md`、`formalization/README.md`、`blueprint/README.md`、
  `Energy/README.md`、`KLS/README.md`、`KLS/LogConcave/README.md`、`Poincare/README.md`、`Poincare/Euclidean/README.md`、
  `naming.md`（新增"线性等距传输"与"环境平移"两行，并区分 `_translateLaw` 与 `_translateLaw_ambient` 后缀）。
  statement golden、`STATEMENT_CHECKS`、路线配置未动。

## 证据边界

`lake build` 通过（3344 jobs），证书与十二条库级声明有标准公理守卫。最终验证收据由 `python3 research/verify.py`
在本记录及所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；
未做隔离重建、远端 CI 或发布。
