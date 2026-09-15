# 2026-09-13 — 全局 Gauss–Green：有限光滑单位分解拼接与下游闭合

Owner 要求用已证明的图表内局部公式，通过有限光滑单位分解拼接，消除全局向量场 Gauss–Green 的
`sorry`，并核验两个下游公式不再传递依赖 `sorryAx`；直接实施证明与验证，本轮不提交、不推送。承接
[子图散度记录](2026-09-13-subgraph-divergence-and-local-gauss-green.md)、
[边界图表与面积接口记录](2026-09-13-boundary-chart-and-area-interface.md)、
[Gauss–Green 面积公式记录](2026-09-12-gauss-green-area-formula.md)与
[接口接入记录](2026-09-12-perimeter-interface-integration.md)。此前未提交的模块拆分、周长接口证明、
图面积公式、边界图表、子图散度公式与局部 Gauss–Green 全部保留，未重置、未覆盖、未重复实现；
历史记录保持原文与原计数。

## 结论先说

| 目标 | 状态 | 传递公理 |
| --- | --- | --- |
| 1. 全局向量场 Gauss–Green `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | **完成** | 标准三条 |
| 2. 有限光滑分解接口 `Analysis.exists_finset_sum_eq_of_isOpen_cover` | **完成** | 标准三条 |
| 2'. 可积性接口 `integrableOn_inner_outwardNormal`、散度的连续性/紧支撑/有限可加性 | **完成** | 标准三条 |
| 3. 标量形式 `setIntegral_gradient_eq_integral_smul_outwardNormal` | **完成**（归约，不再含洞） | 标准三条 |
| 3'. 磨光 indicator 梯度 `gradient_mollifiedIndicator_eq` | **完成**（归约，不再含洞） | 标准三条 |
| coarea、Sard、恢复序列、Cheeger 下确界、奇异测度比较 | 未动 | 仍含 `sorryAx` |

证书数仍是 24，没有新增 ledger 节点，没有 Blueprint `\lean`/`\leanok` 锚点，
`lem:relative-perimeter-smoothing` 的 infrastructure 状态仍为 `missing`。
WIP 直接 hole 从 20 降到 **19**（`RelativePerimeter` 3、`AnalyticPrerequisites` 4→**3**、
`CheegerInfimum` 8、`Energy/WIP/Cheeger` 5）。**完成全局 Gauss–Green 不等于相对周长链完成。**

## 1. 陈述未变

`FunctionalInequalities/KLS/Geometry/GaussGreen.lean`：

```
theorem KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal
    (U : SmoothDomain V) {F : V → V} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∫ x in U.carrier, Analysis.divergence F x
      = ∫ x in frontier U.carrier, ⟪F x, U.outwardNormal x⟫ ∂(surfaceMeasure V)
```

名称、命名空间、假设、`surfaceMeasure` 归一化与外法向方向都与此前的 `sorry` 版本逐字相同。
**没有**增加区域有界、边界总测度有限、`F` 更高阶光滑或 `V` 非零维的假设，也没有削弱结论。

## 2. 三类局部块的完整覆盖

覆盖的是紧集 `K = tsupport F`，索引类型是 `Bool ⊕ ↥(frontier U.carrier)`，三族开集：

* **图表柱**：对每个边界点 `z`，`exists_boundaryChart` 给一张图表，本轮新增的
  `BoundaryChart.self_mem_cylinder`（`graphCoord x₀ x₀ = 0 ∈ param`，`graphHeight x₀ x₀ = 0 < depth`）
  保证 `z` 落在自己的柱内；
* **区域内部** `U.carrier`（开）；
* **区域外部** `(closure U.carrier)ᶜ`（开）。

覆盖性来自开集 `U` 的 `interior U = U`：任一点若不在 `U`、也不在 `frontier U`，则不在 `closure U`。
**不能只用边界柱**——支撑可能整个落在内部或外部，两个独立客户端（下文 Client 1、2）就是这两种情形。

三块分别处理，都在 `KLS/Geometry/GaussGreen.lean` 内：

* **图表块**：直接调用已证的
  `BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`；
* **内部块** `integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_carrier`：
  `tsupport Gᵢ ⊆ U.carrier` 使 `Gᵢ` 与 `divergence Gᵢ` 在 `U` 外为零，于是
  `∫_U div Gᵢ = ∫_V div Gᵢ = 0`（`setIntegral_eq_integral_of_forall_compl_eq_zero` 加
  `Analysis.integral_divergence_eq_zero`）；通量侧为零，因为开集 `U` 与 `frontier U` 不交，
  故 `Gᵢ` 在边界上恒为零；
* **外部块** `…_of_tsupport_subset_compl_closure`：`U ⊆ closure U` 与
  `frontier U ⊆ closure U` 使两侧被积函数都恒为零。

零维空间、空支撑与空边界都由同一条路径覆盖：`Subsingleton V` 时 `frontier U = ∅`，单位分解在
`tsupport F = ∅` 上的求和条件是空条件，分解式 `F = Σᵢ Gᵢ` 在支撑外由 `F x = 0` 成立。
全程没有 `Nonempty`、`Nontrivial` 或维数下界假设。

## 3. 单位分解：接口与"全局等式"这一关键点

`FunctionalInequalities/Analysis/PartitionOfUnity.lean`，`Analysis.exists_finset_sum_eq_of_isOpen_cover`：
对有限维实赋范空间 `V`、紧支撑 `C^n` 映射 `F : V → E` 与 `tsupport F` 的开覆盖 `W`，

```
∃ (s : Finset γ) (G : γ → V → E),
  (∀ i, ContDiff ℝ n (G i)) ∧ (∀ i, HasCompactSupport (G i)) ∧
  (∀ i, tsupport (G i) ⊆ W i) ∧ ∀ x, ∑ i ∈ s, G i x = F x
```

三点是刻意写进陈述的：

1. **`tsupport (G i) ⊆ W i`，不是 `support (G i) ⊆ W i`**。闭支撑的包含才让 `G i` 在 `W i` 外的
   每一点的**邻域**上为零，从而 `fderiv ℝ (G i)` 也为零——这正是三类局部块各自需要的局部化条件；
2. **`∀ x` 的全局等式**，不是只在 `tsupport F` 上的逐点等式。只在支撑上成立的等式不能求导；
   本轮因此**不**走"先在 `K` 上分解再求导、再消去 `Σ ∇χᵢ = 0`"的路线，而是让散度直接对**全局
   函数等式**使用 `fderiv` 的有限可加性，分解导数项根本不出现；
3. **有限求和**，不是 `finsum`。有限性来自
   `LocallyFinite.finite_nonempty_inter_compact` 作用在紧集 `tsupport F` 上：支撑与 `tsupport F`
   不相交的指标给出的 `G i` 是**处处**为零的函数，不只是在支撑上为零。

路线是 Mathlib 的 `SmoothPartitionOfUnity.exists_isSubordinate`，取流形 `V` 以自身为模型
（`𝓘(ℝ, V)`；`V` 是 Hausdorff、σ-紧、有限维），`contMDiff_iff_contDiff` 把流形意义的 `C^∞` 换成
`ContDiff ℝ ∞`，再取 `G i = χ i • F`。没有自己重建 bump 函数或覆盖引理。

## 4. 可积性与有限求和：全部证明，没有假设

`Analysis/Divergence.lean` 新增（并把 `fderiv_eq_zero_of_notMem_tsupport` 从
`Analysis/SubgraphDivergence.lean` **下移**到此处，名称与陈述不变，原处不留重复证明也不留别名）：

* `traceLM`：`(V →L[ℝ] V) →ₗ[ℝ] ℝ` 的迹泛函，有限维上自动连续（`continuous_traceLM`）；
* `continuous_divergence`：`C¹` 场的散度连续（`traceLM ∘ fderiv`）；
* `divergence_eq_zero_of_notMem_tsupport` 与 `hasCompactSupport_divergence`；
* `divergence_finset_sum`：逐点可微时散度对有限族可加（`HasFDerivAt.sum` 加迹的线性）。

`KLS/Geometry/GaussGreen.lean` 新增：

* `norm_outwardNormal_le_one`：外法向处处是压缩（边界上为单位向量，边界外为零）；
* `integrableOn_inner_outwardNormal`：连续紧支撑向量场的通量被积函数在 `frontier U` 上对
  `surfaceMeasure` 可积。控制项是 `‖G x‖`，用 `abs_real_inner_le_norm` 与 `‖ν‖ ≤ 1`；
  测度侧只用到 `measurable_outwardNormal` 与 `isLocallyFiniteMeasure_surfaceMeasure_frontier`，
  **没有**用任何关于 `surfaceMeasure (frontier U)` 总量的界，所以无界边界仍在范围内。

于是两次 `integral_finsetSum` 的可积性前提都被实际证明：体积侧由"连续 + 紧支撑"给出
`IntegrableOn (divergence (G i)) U.carrier volume`，边界侧由上面那条给出。
被积函数的逐点分解分别是 `Analysis.divergence_finset_sum`（体积侧）与 `sum_inner`（边界侧）。
Lean 的全定义积分确实会让不可积项给 0，但本轮没有借此省略任何一步可积性检查。

## 5. 模块组织与迁移

* 通用件下沉：`Analysis/PartitionOfUnity.lean`（新）与 `Analysis/Divergence.lean`（扩充）；
  `fderiv_eq_zero_of_notMem_tsupport` 从 `SubgraphDivergence` 下移到 `Divergence`。
* `SmoothDomain` 的全局结论放在应用层新模块 `KLS/Geometry/GaussGreen.lean`，位于
  `KLS/Geometry/LocalGaussGreen.lean` 之上、`KLS/WIP/AnalyticPrerequisites.lean` 之下。
* **最小拆分迁移**：`isLocallyFiniteMeasure_surfaceMeasure_frontier` 与
  `integrableOn_smul_outwardNormal` 由 `AnalyticPrerequisites` 原样迁入同一新模块（同命名空间、
  同名称、同陈述），因为它们是本轮证明要用到的无洞边界可积性接口。**没有**兼容别名、
  重复证明或转发声明；唯一的消费者 `AnalyticPrerequisites` 改为导入新模块。
* `Analysis/PartitionOfUnity.lean` 与 `KLS/Geometry/GaussGreen.lean` 都不导入 coarea、Sard 或
  任何含洞模块。依赖方向仍无环：
  `Analysis/{AreaFormula, ImplicitGraph, SubgraphDivergence, GraphIntegral, PartitionOfUnity}`
  → `KLS/Geometry/{BoundaryChart, LocalGaussGreen, GaussGreen}` → `KLS/WIP/AnalyticPrerequisites`。
* 没有新增公理、没有隐藏 `sorry`、没有削弱结论、没有增加实质假设。陈述未发现问题，因而未改题。

## 6. 计数订正

`AnalyticPrerequisites` 现有 **6 条公开定理、0 条定义**：3 条已填证明体
（`ae_forall_fderiv_ne_zero`、`setIntegral_gradient_eq_integral_smul_outwardNormal`、
`gradient_mollifiedIndicator_eq`），3 条直接 `sorry`
（`aemeasurable_lintegral_levelSet`、`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`、`sard`）；
已填的 3 条里 **2 条**无传递 `sorryAx`，只有 `ae_forall_fderiv_ne_zero` 因 `sard` 仍含 `sorryAx`。
迁移前是 9 条公开定理、5 条已填、4 条洞、2 条无 `sorryAx`；更早（`outwardNormal` 迁出前）是
13 条公开定理与 1 条定义。历史记录保持原文。

## 7. 验证

* **传递公理**：`KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`、
  两条局部块引理、`integrableOn_inner_outwardNormal`、`integrableOn_smul_outwardNormal`、
  `isLocallyFiniteMeasure_surfaceMeasure_frontier`、
  `Analysis.exists_finset_sum_eq_of_isOpen_cover`、`Analysis.divergence_finset_sum`、
  `Analysis.continuous_divergence`，以及下游的
  `setIntegral_gradient_eq_integral_smul_outwardNormal` 与 `gradient_mollifiedIndicator_eq` ——
  全部只有 `propext / Classical.choice / Quot.sound`。
* **独立客户端**：`build/audit/GaussGreenAudit.lean`（忽略目录，`lake env lean` 直接 elaborate，
  不进 `lake build`、重放集合或认证闭包）。十一条客户端定理，传递公理都只有标准三条：
  1. `client_support_inside`：支撑完全落在 `U` 内时，由 Gauss–Green 反推 `∫_U div F = 0`；
  2. `client_support_outside`：支撑完全落在 `closure U` 外时，边界通量为零；
  3. `client_halfSpace_global`：半空间 `{⟪a,x⟫<0}`（`‖a‖=1`）上**不带支撑限制**地使用全局公式，
     外法向是具体的 `+a`——这是与上一轮图表局部客户端的实质区别；
  4. `client_halfSpace_flux_sign`：边界通量非负则总散度非负，**方向约定的符号检验**；
  5/6. `client_interval_normal_left` / `_right`：一维区间 `(α,β)` 的外法向在左端是 `-1`、
     右端是 `+1`；
  7. `client_interval_endpoints`：全局公式在 `(α,β)` 上给出 `∫_α^β F' = F β - F α`，
     两端法向符号都被检验（`ℋ^0` 上的两点积分逐点算出，`surfaceMeasure ℝ = μH[0]`，
     `unitBallVolume 0 = 1`）；
  8. `client_empty_frontier`：`U = univ` 时边界为空，公式退化为全空间散度定理（任意维数）；
  9. `client_subsingleton`：零维空间上边界必空、两侧都为零，无 `Nontrivial` 假设；
  10/11. `client_scalar_form`、`client_mollified_gradient`：两个下游公式，符号为
     `∫_U ∇η = ∫_∂U η n` 与磨光 indicator 梯度的负号，均保持原样。
  上三轮的 `AreaFormulaAudit.lean`、`BoundaryChartAudit.lean`、`PerimeterInterfaceAudit.lean`、
  `SubgraphDivergenceAudit.lean` 重新运行，结论与公理不变。
* **严格模式**：`Analysis/{Divergence, PartitionOfUnity, SubgraphDivergence, GraphIntegral,
  ImplicitGraph, AreaFormula, LevelSet}`、`KLS/Geometry/{SurfaceMeasure, BoundaryChart,
  LocalGaussGreen, GaussGreen}` 与五个审计客户端在 `lake env lean -DwarningAsError=true` 下退出 0。
* **含 hole 的 WIP**：四个文件普通模式实际重新 elaborate，退出 0，诊断恰好是预期的
  3 / 3 / 8 / 5 条 `declaration uses 'sorry'`，无其他警告或错误。**这不是严格模式通过。**
* 完成默认 `lake build`（3393 jobs），并从仓库根运行 `python3 research/verify.py`；
  `lem:relative-perimeter-smoothing` 的 infrastructure 证据哈希按本轮源码重算并加入两个新模块，
  note 与 gaps 同步更新，状态仍为 `missing`。最终回执由 `build/verification/latest.json` 指向，
  与最终源码快照匹配。

证据都信任固定版本的第三方编译依赖，不代表独立重建 Mathlib、远端 CI 或 Blueprint 排版通过。
审计脚本与日志留在忽略的 `build/`。本轮按 owner 要求不提交、不推送。

## 距离相对周长链完成还剩什么

1. **加权 coarea 公式**与其可测性（`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`、
   `Analysis.aemeasurable_lintegral_levelSet`）。Mathlib 只有等维的 Jacobian 面积公式。
2. **实值函数的 Sard 定理**（`Analysis.sard`）。Mathlib 只有等维版本
   `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`。
3. **磨光外扩的梯度积分估计与相对周长恢复序列**：现在可以用已闭合的
   `gradient_mollifiedIndicator_eq` 与面积测度的局部有限性推进，但本轮未动。
4. `RelativePerimeter` 3 条、`CheegerInfimum` 8 条、`Energy/WIP/Cheeger` 5 条洞仍在，
   奇异律的 Cheeger 比较仍开放。
