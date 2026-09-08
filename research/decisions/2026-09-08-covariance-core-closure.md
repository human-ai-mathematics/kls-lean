# 协方差核闭包：statement、语义对齐与证明

日期：2026-09-08（Asia/Shanghai）。基线：`575c82c` 之上的未提交工作树，紧接
[仿射常数定义记录](2026-09-07-affine-poincare-constant-definition.md)。Lean/Mathlib 为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示："暂时先不提交，接着做"，
即按 atlas 继续下一个节点。本决定不做 commit、push、远端 CI 或发布。

## 节点选择

`def:affine-poincare-constant` 认证后 atlas 没有 `formalize` 项，剩余叶节点均为
`inspect_infrastructure` 的定理。`lem:covariance-core-closure` 是 `thm:affine-covariance-relaxation-closed`
唯一未认证前提，进而解锁 `lem:affine-poincare-translation-invariance`、`thm:affine-isotropic-reduction`
与两个 CMH 路线节点，因此优先。

## Statement 设计

Blueprint：ν = ρ dx 全维对数凹律，Σ ⪰ 0 常自伴算子，T g = Σ^{1/2}∇g 在全局 Lipschitz L²(ν)
函数上稠密定义且可闭，图闭包等于 ℝ + C_c^∞(V) 限制的图闭包，‖Tg‖² 的序列松弛为
Q(f) = ‖T̄f‖²（f ∈ Dom T̄）、+∞（否则）。

Lean 分五个模块，先通用后具体。

| 模块 | 声明 | 内容 |
| --- | --- | --- |
| [Energy/Relaxation/LinearPMap.lean](../../formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean) | `Energy.exists_mem_of_isClosed_of_frequently_norm_le` | Hilbert 选择引理：闭子空间 G ⊆ X × H 含 (xₙ, yₙ)，xₙ → x₀，‖yₙ‖ ≤ L 频繁成立，则 G 含 (x₀, y₀) 且 ‖y₀‖ ≤ L；用尾部凸包的最小范数元与平行四边形律，不用弱拓扑 |
| | `Energy.PreEnergy.ofLinearPMap T` | 预能量 f ↦ ‖T f‖²，实现为包含映射；`ofLinearPMap_quadratic`、`ofLinearPMap_denseRealization_iff` |
| | `sequentialRelaxation_ofLinearPMap_of_mem` / `_of_notMem` / `_toAmbient` | 可闭 T：松弛在 Dom T̄ 上等于 ‖T̄ f‖²，之外为 ⊤，测试上等于原能量 |
| | `Energy.isClosable_of_graph_closure_snd_eq_zero`、`mem_graph_topologicalClosure_iff`、`IsClosable.closure_domRestrict_eq`、`_of_le` | 可闭性判据、图闭包的序列刻画、图范数稠密核的闭包相等及单调性 |
| [Energy/Euclidean/WeakDerivative.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/WeakDerivative.lean) | `integral_fderiv_apply_eq_zero`、`integral_mul_fderiv_apply`、`integral_mul_inner_gradient` | 紧支撑 C¹ 函数方向导数的 Haar 积分为零（平移不变性 + 参数积分求导）；光滑分部积分；全局 Lipschitz g 的弱导数恒等式 ∫φ⟪∇g,w⟫ = −∫ g (Dφ)w（磨光 + 控制收敛） |
| [Energy/Euclidean/CovarianceGradient/Operator.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Operator.lean) | `weightedGradient B g`、`IsGradientTest ν B g`、`gradientGraph`、`gradientOperator ν B hac` | 测试：全局 Lipschitz、L²(ν)、B∇g ∈ L²(ν;V)；图 {([g],[B∇g])} 在 ν ≪ Haar 下是子模（Rademacher 给 a.e. 线性），在支撑边界零测下是函数图（代表元无关）；`Submodule.toLinearPMap` 给出算子；域与取值刻画 |
| | `covarianceRelaxation_eq_sequentialRelaxation_ofLinearPMap` | 若 ∀v, ⟪Σv,v⟫ = ‖Bv‖²，则定义节点的协方差松弛等于该算子的松弛 |
| | `gradientOperator_apply_eq_zero_of_subsingleton`、`domain_gradientOperator_eq_top_of_subsingleton` | 零维：算子为零，域为全空间 |
| [Energy/Euclidean/CovarianceGradient/Closable.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Closable.lean) | `Probability.LocallyDominates ν m` | 支撑内部每个紧集上 m|_K ≤ C·ν|_K |
| | `gradientOperator_isClosable` | 前提 ν ≪ m、ν(∂supp) = 0、LocallyDominates：算子可闭 |
| [Energy/Euclidean/CovarianceGradient/Core.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Core.lean) | `smoothCore ν`、`dense_smoothCore`、`dense_domain_gradientOperator` | 光滑紧支撑类构成子模、在 L²(ν) 稠密（Mathlib），故域稠密，对任意律成立 |
| | `closure_domRestrict_smoothCore`、`closure_domRestrict_eq_of_smoothCore_le` | 由已证 `exists_smooth_weighted_L2_approximation`：光滑核与全域同闭包；夹在中间的任何核亦然 |
| [KLS/LogConcave/CovarianceClosure.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/CovarianceClosure.lean) | `hν.absolutelyContinuous_haar`、`hν.frontier_support_eq_zero`、`hν.locallyDominates` | 全维对数凹律满足三条前提；局部支配由 Borell 密度紧集正下界得到 |
| | `hν.gradientOperator m B hi`、`_isClosable`、`dense_domain_`、`closure_domRestrict_eq_of_smoothCore_le`、`sequentialRelaxation_gradientOperator_of_mem/_of_notMem/_toAmbient`、`covarianceRelaxation_eq` | Blueprint 五条结论的对数凹版本 |
| | `hμ.intrinsicGradientOperator m B`、`_isClosable`、`dense_domain_`、`closure_domRestrict_`、`hμ.affine_energy_eq` | 任意对数凹 μ 的内禀律版本，含零维；`Energy.Affine.energy μ` 与算子松弛相等 |

证书 `Solutions.LemCovarianceCoreClosure.certificate`：对全维对数凹 ν、任意 Haar m 与任意 B，打包
域稠密、可闭、核独立（任何 smoothCore ≤ S ≤ Dom 的 S）、Dom T̄ 上松弛 = ‖T̄f‖²、其外 = ⊤。
三个 `example`：Fin n 上任意对数凹律的内禀律、Fin 0（算子为零且域为 ⊤）、与 `Energy.Affine.energy` 的等式。

**主张什么。** 上表全部声明及证书。**不主张什么。** 不主张 Q 的 Poincaré 不等式、平移不变性、
各向同性归约、Σ^{1/2} 的存在性（下游节点用谱定理构造 B）、raw/core agreement 之外的任何
Dirichlet/Markov 性质、`Energy.Affine.energy` 与 `Energy.Canonical.energy` 的比较，或 KLS。
**有限范围与零维。** 空间有限维；测试全局 Lipschitz；B 任意（含零与奇异）；零维方向空间包含
在每条结论中，此时算子为零、域为全空间、松弛恒为零。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| ν = ρ dx 全维对数凹律 | `hν : LogConcave ν`、`hi : (interior ν.support).Nonempty`；密度由 Borell 表示内部产生，不作前提 | 一致（Lean 前提更弱：不需给定 ρ） |
| Σ ⪰ 0 常自伴，T g = Σ^{1/2}∇g | 任意 `B : V →L[ℝ] V`，T g = B∇g；Σ = B†B | Lean 更强（B 任意），记录；Σ^{1/2} 的存在性留给消费者 |
| 在全局 Lipschitz L²(ν) 函数上稠密定义 | `IsGradientTest`（另要求 B∇g ∈ L²，与 Blueprint 的 T 定义域一致）；`dense_domain_gradientOperator` 对任意律成立 | 一致（稠密性更一般） |
| 可闭 | `gradientOperator_isClosable`，前提 ν ≪ m、ν(∂supp)=0、LocallyDominates；对数凹全维律满足 | 一致 |
| 图闭包等于 ℝ + C_c^∞(V) 限制的图闭包 | `closure_domRestrict_eq_of_smoothCore_le`：任何含光滑紧支撑类、含于域的子模 S；ℝ + C_c^∞ 是其中之一 | Lean 更强（任意中间核），记录；ℝ + C_c^∞ 未单独命名为 Lean 对象 |
| Q(f) = ‖T̄f‖² 于 Dom T̄，+∞ 于其外 | `sequentialRelaxation_gradientOperator_of_mem` / `_of_notMem`，通用形式对任何可闭算子成立 | 一致（Lean 更一般） |
| 证明末句：零维时函数皆常数、梯度为零 | `domain_gradientOperator_eq_top_of_subsingleton`、`gradientOperator_apply_eq_zero_of_subsingleton` | 一致 |
| 证明中"光滑紧支撑函数在 L²(ν) 稠密" | Mathlib `Lp.dense_hasCompactSupport_contDiff` | 一致 |
| 证明中的弱紧性论证（弱收敛子列、图弱闭） | 改为 Hilbert 选择引理（尾部凸包最小范数元 + 平行四边形律），无弱拓扑 | 结论相同，证法不同，记录 |

未发现 Lean 弱于 Blueprint 之处。Blueprint 的 \uses 中 `thm:borell-logconcave-density` 在 Lean 中确有
使用（`exists_isBorellDensity_of_interior_support_nonempty` 与 `exists_bounds_of_isCompact` 给出局部支配），
`lem:covariance-test-core-density` 用于核闭包相等。

## 证明路线

- **选择引理。** Pₙ = {(x_j,y_j) : j ≥ n}，Cₙ = closure(convexHull(snd '' Pₙ))，zₙ 为 Cₙ 的最小范数元
  （`exists_norm_eq_iInf_of_complete_convex`）。‖zₙ‖ 单调有界 → S ≤ L；中点 (zₙ+zₘ)/2 ∈ Cₙ 与平行四边形律
  给 ‖zₙ − zₘ‖² ≤ 2(‖zₘ‖² − ‖zₙ‖²)，故 Cauchy → z₀。取凸组合 pₙ ∈ convexHull Pₙ ⊆ G 使 (pₙ).2 逼近 zₙ，
  (pₙ).1 落在 x₀ 的收缩闭球（`LinearMap.image_convexHull`），G 闭 ⇒ (x₀,z₀) ∈ G。
- **松弛识别。** ≤：(x, T̄x) ∈ closure(graph T)（`IsClosable.graph_closure_eq_closure_graph`），取图点序列。
  ≥ 与 ⊤：liminf < L² 给出频繁 ‖T fₙ‖ ≤ L（`frequently_lt_of_liminf_lt`），选择引理给 (x, y₀) ∈ graph T̄。
- **弱导数。** 紧支撑 C¹ 的 u：F(t) = ∫ u(t•w + x) dm 为常数（`integral_add_left_eq_self`），
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` 求导得 ∫ (Du) w = 0；乘积法则给光滑分部积分；
  Lipschitz g 用 `mollify m (radius j) g`：`tendsto_gradient_mollify`（可微点）+ Rademacher + 一致界 K，
  `norm_mollify_sub_le` 给一致收敛，两边控制收敛后由极限唯一性得恒等式。
- **可闭性。** (0, y) ∈ closure(graph)：fₙ → 0，T fₙ → y。对 tsupport φ ⊆ Ω 的 φ ∈ C_c^∞：局部支配把 L²(ν) 收敛
  变为 supp φ 上的 L¹(m) 控制（`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`），∫ φ•(T fₙ) → ∫ φ•y；
  ∫ φ•B∇gₙ = B(∫ φ•∇gₙ)，‖∫ φ•∇gₙ‖² = −∫ gₙ (Dφ)(∫φ•∇gₙ) ≤ ‖∫φ•∇gₙ‖·∫‖gₙ‖‖Dφ‖，再由局部支配 → 0。
  故 ∫ φ•y dm = 0，`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` 给 y = 0 m-a.e. 于 Ω，
  ν ≪ m 与 ν(Ωᶜ) = 0 给 y = 0。
- **核与稠密。** 光滑紧支撑 ⇒ Lipschitz（`lipschitzWith_of_nnnorm_fderiv_le`）、有界 ⇒ 测试；
  Mathlib 稠密性；`exists_smooth_weighted_L2_approximation` 给图范数逼近。
- **对数凹前提。** ν ≪ Haar（已证）；∂supp 为凸集边界，Haar 零测（`Convex.addHaar_frontier`）；
  Borell 密度 ρ ≥ a > 0 于紧集 K ⇒ m(s ∩ K) ≤ a⁻¹ ∫_{s∩K} ρ dm = a⁻¹ ν(s ∩ K)。

## 元数据同步

- ledger 新增 `lem:covariance-core-closure`（proved / lean，`solutions/LemCovarianceCoreClosure.lean`），
  十四个 proved 节点；`check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块。
- Blueprint 引理块锚定十四条声明与证书，声明与证明标 `leanok`；块尾补充 B 替代 Σ^{1/2}、任意中间核、
  与仿射松弛等式的说明；`\uses` 未改。
- 根聚合模块导入 `KLS.LogConcave.CovarianceClosure`；`Poincare/Foundation.lean` 导入五个新 Energy 模块并
  更新文档要点。
- tasks.json：节点改为 `available`，登记新模块、`LipschitzApproximation.lean`、`BorellRepresentation.lean`
  与 Mathlib `LinearPMap`、`Projection/Minimal`、`ParametricIntegral`、`AEEqOfIntegralContDiff`、
  `SmoothApprox`、`MeanValue` 的哈希；被本次编辑触及的其他任务证据哈希同步刷新。
- 当前指南：HANDOFF、README、`verification.md`、`solutions/README.md`、`formalization/README.md`、
  `blueprint/README.md`、`Energy/README.md`、`KLS/LogConcave/README.md`、`naming.md`。
  statement golden、`STATEMENT_CHECKS`、路线配置未动。

## 证据边界

`lake build` 通过，证书与十一条库级声明有标准公理守卫。最终验证收据由 `python3 research/verify.py`
在本记录及所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任
第三方编译导入；未做隔离重建、远端 CI 或发布。
