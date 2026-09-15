# 2026-09-13 — Gauss–Green 前置：光滑子图上的散度公式、带权边界换元与图表局部 Gauss–Green

Owner 要求完成 Gauss–Green 的下一项前置工作：光滑子图上的局部散度积分公式，补齐所需的带权边界积分
换元，并接通 `SmoothDomain.BoundaryChart`；直接实施证明与验证，本轮不提交、不推送。承接
[边界图表与面积接口记录](2026-09-13-boundary-chart-and-area-interface.md)、
[Gauss–Green 面积公式记录](2026-09-12-gauss-green-area-formula.md)与
[接口接入记录](2026-09-12-perimeter-interface-integration.md)。此前未提交的模块拆分、周长接口证明、
图面积公式、局部图表与外法向公式全部保留，未重置、未覆盖、未重复实现；历史记录保持原文与原计数。

## 结论先说

| 目标 | 状态 | 传递公理 |
| --- | --- | --- |
| 1. 全局光滑子图上的散度公式 `Analysis.integral_divergence_subgraph` | **完成** | 标准三条 |
| 2. 带权边界积分换元 `Analysis.setIntegral_image_graphChartMap` / `setLIntegral_image_graphChartMap` | **完成** | 标准三条 |
| 3. 图表局部 Gauss–Green `BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal` | **完成**（支撑限于单张图表柱） | 标准三条 |
| 全局向量场 Gauss–Green `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | **未完成**，仍是直接 `sorry` | 含 `sorryAx` |
| 标量 Gauss–Green、`gradient_mollifiedIndicator_eq` | 证明体已填，仍由向量形式归约 | 含 `sorryAx` |

本轮**没有**做有限光滑单位分解，**没有**闭合完整 Gauss–Green，**没有**推进 coarea、Sard 或恢复序列。
证书数仍是 24，没有新增 ledger 节点，没有 Blueprint `\lean`/`\leanok` 锚点，
`lem:relative-perimeter-smoothing` 的 infrastructure 状态仍为 `missing`。
WIP 直接 hole 总数不变，仍是 20（`RelativePerimeter` 3、`AnalyticPrerequisites` 4、
`CheegerInfimum` 8、`Energy/WIP/Cheeger` 5）。

## 1. 子图上的散度公式

### 陈述

`FunctionalInequalities/Analysis/SubgraphDivergence.lean`，`Analysis.integral_divergence_subgraph`：
设 `H`、`V` 为有限维实内积空间，`hsp : IsGraphSplitting ι e` 给出正交分解 `V = ι H ⊕ ℝ e`，
`x₀ : V`，`g : H → ℝ` 为 `ContDiff ℝ 1`，`F : V → V` 为紧支撑 `C¹` 向量场。记
`Ψ = graphChartMap ι e x₀ g`，`S = {x | graphHeight e x₀ x < g (graphCoord ι x₀ x)}`，则

```
∫_S divergence F = ∫_H ⟪F (Ψ y), ι (-(∇g y)) + e⟫ dy .
```

右端是**未归一化**的法向通量：沿图的单位外法向是 `(ι(-∇g)+e)/√(1+‖∇g‖²)`，图 Jacobian 恰是
`√(1+‖∇g‖²)`，两者在本式中已经互相抵消，既没有漏掉切向项 `ι(-∇g)`，也没有多留一个 Jacobian 因子。

保留的一般性：任意正交分解与任意平移 `x₀`；`g` 只要 `C¹`，**不**要求全局 Lipschitz 或有界梯度
（本轮把假设从 owner 所写的 `C^∞` 放宽到 `C¹`，结论不变）；子图与其边界可以无界；`F` 只需 `C¹` 紧支撑；
`H` 可以零维，此时结论即一维半直线上的微积分基本定理（审计客户端 3 实际导出）。

### 路线：测度分裂 + 剪切 + 迹分解 + FTC

**(a) 测度分裂，无行列式。** `splitIsometry` 把 `WithLp 2 (H × ℝ)` 线性等距地等同于 `V`
（`LinearIsometryEquiv.ofSurjective`，范数等式由勾股 `IsGraphSplitting.norm_add_smul_sq` 与
`WithLp.prod_norm_sq_eq_of_L2` 给出），于是 `splitHomeomorph (y,t) = x₀ + ι y + t • e` 保测度
（`WithLp.volume_preserving_toLp` + `LinearIsometryEquiv.measurePreserving` + 平移不变性）。
剪切 `shearEquiv (y,s) = (y, s + g y)` 保乘积测度：按 `Measure.prod_apply` 做 Fubini，逐纤维用
`measure_preimage_add_right`，只需 `g` 可测（`measurePreserving_shearEquiv`）。两者复合得
**图表 `Ξ (y,s) = x₀ + ι y + (s + g y) • e`**，它是同胚且保测度
（`measurePreserving_graphChartHomeomorph`），并把半空间 `{s < 0}` 打到 `S` 上。
**没有**计算任何 Jacobian 行列式，也没有引用未证的 Piola 恒等式或一般散度定理。

**(b) 散度的迹分解，无基底。** `divergence_eq_tangentDiv_add`：

```
divergence F x = tangentDiv ι (DF x) + ⟪e, DF x e⟫,   tangentDiv ι M = tr_H (P ∘ M ∘ ι)
```

其中 `P = graphProj ι` 是 `ι` 的伴随。证明把恒等映射写成 `ι∘P + e⊗e`，法向部分用
`Analysis/Divergence.lean` 已有的秩一迹恒等式 `trace_smulRight`，切向部分用
`LinearMap.trace_comp_comm'`（`tr_V (g∘f) = tr_H (f∘g)`）。**不选取正交基**，因此零维与高维统一处理。

**(c) 逐点恒等式。** 在图表坐标下，记 `T(y,s) = Ξ(y,s)`，则

```
divergence F (T(y,s)) = divergence (z ↦ P (F (T(z,s)))) y + d/ds ⟪e - ι(∇g y), F (T(y,s))⟫ .
```

左边用 (b)；右边第一项用链式法则 `divergence_graphProj_comp` 与
`graphTrace_comp_graphLinear`，得 `tangentDiv ι (DF) + ⟪∇g y, P (DF e)⟫`；第二项由
`∂_s T = e` 得 `⟪e, DF e⟫ - ⟪∇g y, P (DF e)⟫`。两个 `∇g` 项**精确抵消**，这正是切向 `-∇g` 项的来源。
这里只用到 `g ∈ C¹`：切片场 `z ↦ P(F(T(z,s)))` 的 `C¹` 性只需 `T(·,s)` 是 `C¹`。

**(d) 两项积分。** 切向项对每个固定的 `s` 在 `H` 上积分为零（下节）；法向项沿每条纤维用
`HasCompactSupport.integral_Iic_deriv_eq` 积到 `s = 0` 的值 `⟪e - ι(∇g y), F (Ψ y)⟫`。
`Iio 0` 与 `Iic 0` 的替换用 `Iio_ae_eq_Iic`。Fubini 的可积性全部来自"连续 + 紧支撑"：
紧支撑由同胚 `Ξ` 传递（`HasCompactSupport.comp_homeomorph`），切片与纤维的紧支撑由
`hasCompactSupport_comp_of_norm_le`（参数范数被像的范数控制）给出。

### 无边界的散度定理：按维数归纳

`Analysis.integral_divergence_eq_zero`：紧支撑 `C¹` 向量场 `W : H → H` 满足 `∫_H div W = 0`。
Mathlib 的散度定理只覆盖 `Fin (n+1) → ℝ` 中的长方体，因此本轮自证，路线与主定理同构，
不额外引入 `EuclideanSpace` 坐标：

* `finrank = 0`：空间是 `Subsingleton`，`fderiv W y = 0`，迹为零；
* `finrank = n+1`：取单位向量 `u`，用新加入 `Analysis/ImplicitGraph.lean` 的
  `isGraphSplitting_orthogonal` 得到分解 `H = (ℝ∙u)ᗮ ⊕ ℝu`，`finrank (ℝ∙u)ᗮ = n`；
  按 (b) 分解被积函数，法向项沿每条直线由 `integral_deriv_eq_zero` 积为零，
  切向项对每个固定高度由**归纳假设**在 `(ℝ∙u)ᗮ` 上积为零；两次 Fubini 的可积性同样来自紧支撑。

`isGraphSplitting_orthogonal` 是把 `KLS/Geometry/BoundaryChart.lean` 中
`isGraphSplitting_tangent` 的证明**上移**到通用层的结果：原定理名称与陈述不变，证明体改为一行调用，
**没有**保留重复证明，也没有兼容别名。

## 2. 带权边界积分换元

现有面积公式 `hausdorffNormalized_image_graphChartMap` 是**可测参数集上的测度等式**，
不能直接当作任意被积函数的换元。`FunctionalInequalities/Analysis/GraphIntegral.lean` 补齐所需接口，
且**只补本轮所需的最小通用接口**，没有扩展成一般面积/流形积分库：

* `measurableSet_image_graphChartMap`：图像可测（由 `Analysis/AreaFormula.lean` 的
  `measurableSet_image_graphMap` 经平移的**原像**表述得到）；
* `graphChartMap_injective_of_perp`：只用正交性的单射性。原有的
  `graphChartMap_injective (hsp)` 保持名称与陈述，改为调用它，**不重复证明**；
* `map_graphChartMap_withDensity`（核心）：对可测 `s`，

  ```
  map Ψ ((volume.withDensity √(1+‖∇g‖²)).restrict s) = ℋ^k ⌊ (Ψ '' s) ,
  ```

  其中 `k = finrank ℝ H`。证明：对任意可测 `E`，`(volume.withDensity J)(Ψ⁻¹E)` 由面积公式等于
  `ℋ^k (Ψ '' (Ψ⁻¹E)) = ℋ^k (E ∩ range Ψ)`，故 `map Ψ (volume.withDensity J) = ℋ^k ⌊ range Ψ`；
  再用 `Measure.restrict_map` 与**单射性** `Ψ⁻¹(Ψ''s) = s` 限制到 `s`；
* `setLIntegral_image_graphChartMap`（非负可测被积函数）与
  `setIntegral_image_graphChartMap`（Bochner 版，假设只要 `AEStronglyMeasurable`）：

  ```
  ∫_{Ψ '' s} f dℋ^k = ∫_s √(1+‖∇g y‖²) • f (Ψ y) dy .
  ```

  **没有**假设可积性：`integral_map` 与 `integral_withDensity_eq_integral_smul` 在不可积时两边同为 `0`，
  等式仍然成立。参数集、图像与限制测度在陈述中全部显式出现。

Jacobian 抵消在第 3 节与 `BoundaryChart.outwardNormal_graph` 合用时**逐点完成**：
`J • ⟪F, J⁻¹ • (ι(-∇g)+ν)⟫ = ⟪F, ι(-∇g)+ν⟫`，分母恒正（`graphJacobian_pos`），不是"几乎处处非零"。

## 3. 接通 BoundaryChart：图表局部 Gauss–Green

`FunctionalInequalities/KLS/Geometry/LocalGaussGreen.lean`，
`KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`：
对 `U : SmoothDomain V`、`x₀ ∈ frontier U.carrier`、`C : U.BoundaryChart x₀`、紧支撑 `C¹` 场 `F`，
在**明确的支撑条件 `tsupport F ⊆ C.cylinder`** 下，

```
∫_U divergence F = ∫_{frontier U} ⟪F, U.outwardNormal⟫ ∂ surfaceMeasure V .
```

这是**支撑局限于单张图表的局部版本**，不是任意紧支撑场的全局定理。

### 接入细节的处理

* **局部化对 `F` 和 `divergence F` 同时成立。** `tsupport F ⊆ C.cylinder` 蕴含柱外 `F` 在一个邻域上恒零，
  于是 `fderiv F = 0`，`divergence F = 0`（`BoundaryChart.eq_zero_of_notMem_cylinder`，
  经通用引理 `Analysis.fderiv_eq_zero_of_notMem_tsupport`）。这正是"足以保证导数也在柱外消失"的表述。
* **体积分。** `integral_divergence_carrier`：`U.carrier` 的示性函数与**全局**子图
  `S = {x | graphHeight ν x₀ x < height (graphCoord ι x₀ x)}` 的示性函数在乘以 `divergence F` 后逐点相等
  ——柱内两集合相同（`carrier_inter_cylinder`），柱外 `divergence F = 0`。**两个集合本身并不相等**：
  柱外全局延拓高度函数产生的图与 `∂U` 无关，等式只在柱内成立，正是支撑条件把差别消掉。
  然后对 `S` 用第 1 节的子图公式。
* **边界积分。** `integral_inner_outwardNormal_frontier`：被积函数在 `C.map '' C.param` 之外为零
  ——若 `x ∈ frontier U` 且 `x ∉ C.map '' C.param`，则 `x ∉ C.cylinder`（否则由
  `frontier_inter_cylinder` 落进图像），故 `F x = 0`。于是边界积分退化到**一张图片**上，
  用第 2 节的换元，再用 `outwardNormal_graph` 抵消 Jacobian；最后把参数积分从 `C.param` 扩回整个切超平面
  ——`y ∉ C.param` 时 `C.map y` 落在柱外（`BoundaryChart.map_notMem_cylinder`），被积函数为零。
* **边界可积性没有被暗中假设。** 集合替换全部通过**示性函数逐点相等**完成
  （`integral_indicator` 两次），不需要任何可积性；换元本身只需可测性
  （`Measurable.inner` 作用在连续的 `F` 与已证可测的 `outwardNormal` 上）。
  因此**没有**假设 `∂U` 总测度有限，也没有假设 `U` 有界或 `V` 非平凡。
  已证的 `isLocallyFiniteMeasure_surfaceMeasure_frontier` 与 `integrableOn_smul_outwardNormal`
  仍在原处，本轮没有用到它们，也没有削弱它们。

## 模块与范围

| 层 | 模块 | 内容 | hole |
| --- | --- | --- | ---: |
| 通用几何 | `Analysis/ImplicitGraph.lean`（既有，+1 条） | 新增 `isGraphSplitting_orthogonal`；`graphChartMap_injective` 改为调用新的 `graphChartMap_injective_of_perp` | 0 |
| 通用几何 | `Analysis/SubgraphDivergence.lean`（新） | `splitIsometry`、`splitHomeomorph`、`shearEquiv`、`graphChartHomeomorph` 及其保测度性；`hasCompactSupport_comp_of_norm_le`、`fderiv_eq_zero_of_notMem_tsupport`；`graphTrace`/`tangentDiv` 与散度分解；`integral_deriv_eq_zero`、`integral_divergence_eq_zero`；`integral_divergence_subgraph` | 0 |
| 通用几何 | `Analysis/GraphIntegral.lean`（新） | `measurableSet_image_graphChartMap`、`map_graphChartMap_withDensity`、两条积分换元 | 0 |
| 应用层 | `KLS/Geometry/BoundaryChart.lean`（既有） | `isGraphSplitting_tangent` 改为调用通用引理，名称与陈述不变 | 0 |
| 应用层 | `KLS/Geometry/LocalGaussGreen.lean`（新） | 两条局部化引理与图表局部 Gauss–Green | 0 |
| 未完成 WIP | `KLS/WIP/AnalyticPrerequisites.lean` | 仅剩全局 Gauss–Green（缺单位分解）、coarea、Sard；本轮只改模块说明 | 4 |

依赖方向无环：

```
Analysis/AreaFormula → Analysis/ImplicitGraph → {Analysis/SubgraphDivergence, Analysis/GraphIntegral}
Analysis/ImplicitGraph → KLS/Geometry/BoundaryChart → KLS/Geometry/LocalGaussGreen
```

`Analysis/` 下没有任何 `sorry`；正式聚合入口（库根）与 24 个证书都不 import 这些模块，
默认 `lake build` 的 3393 个 job 不变。没有新增公理、没有隐藏 `sorry`、没有削弱结论、
没有增加实质假设，没有兼容别名或重复证明。

## 计数（本轮重新统计）

* **定义**：新增 6 条（`splitIsometry`、`splitHomeomorph`、`shearEquiv`、`graphChartHomeomorph`、
  `graphTrace`、`tangentDiv`），全部在 `Analysis/SubgraphDivergence.lean`。
* **公开定理**：`Analysis/SubgraphDivergence.lean` 26 条（另有 1 条 `private` 归纳载体
  `integral_divergence_aux`）、`Analysis/GraphIntegral.lean` 4 条、
  `KLS/Geometry/LocalGaussGreen.lean` 5 条，合计 **35 条新公开定理 + 6 条新定义**；
  `Analysis/ImplicitGraph.lean` 净增 2 条公开定理
  （`isGraphSplitting_orthogonal`、`graphChartMap_injective_of_perp`）。
  全部无 `sorry`、无传递 `sorryAx`。
* **WIP 直接 hole**：仍为 **20**（3 / 4 / 8 / 5），四个文件都实际重新 elaborate，退出 0，
  诊断恰好是这 20 条 `declaration uses 'sorry'`，无其他警告或错误。**这不是严格模式通过。**
* **传递 `sorryAx`**：`AnalyticPrerequisites` 的计数不变——9 条公开定理、0 条定义，
  5 条已填证明体、4 条直接 hole，已填的 5 条中仍只有 2 条无传递 `sorryAx`。
  `integral_divergence_eq_integral_inner_outwardNormal`、
  `setIntegral_gradient_eq_integral_smul_outwardNormal`、`gradient_mollifiedIndicator_eq`、
  `sard`、`ae_forall_fderiv_ne_zero`、两条 coarea 仍含 `sorryAx`。

## 验证

* **直接公理检查**（只允许 `propext / Classical.choice / Quot.sound`）：
  `Analysis.integral_divergence_subgraph`、`Analysis.integral_divergence_eq_zero`、
  `Analysis.integral_deriv_eq_zero`、`Analysis.divergence_eq_tangentDiv_add`、
  `Analysis.divergence_graphProj_comp`、`Analysis.graphTrace_comp_graphLinear`、
  `Analysis.measurePreserving_splitHomeomorph`、`Analysis.measurePreserving_shearEquiv`、
  `Analysis.measurePreserving_graphChartHomeomorph`、
  `Analysis.integral_comp_graphChartHomeomorph`、`Analysis.isGraphSplitting_orthogonal`、
  `Analysis.map_graphChartMap_withDensity`、`Analysis.setLIntegral_image_graphChartMap`、
  `Analysis.setIntegral_image_graphChartMap`、`Analysis.measurableSet_image_graphChartMap`、
  `Analysis.graphChartMap_injective_of_perp`、`Analysis.graphChartMap_injective`、
  `KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`、
  `…integral_divergence_carrier`、`…integral_inner_outwardNormal_frontier`、
  `…eq_zero_of_notMem_cylinder`、`…map_notMem_cylinder`、
  以及重构后的 `KLS.SmoothDomain.isGraphSplitting_tangent`、`exists_boundaryChart`、
  `BoundaryChart.surfaceMeasure_image` —— 全部只有标准三条。
  `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`、
  `setIntegral_gradient_eq_integral_smul_outwardNormal`、`gradient_mollifiedIndicator_eq` 仍含
  `sorryAx`（如上表）。
* **独立客户端**：`build/audit/SubgraphDivergenceAudit.lean`（忽略目录，`lake env lean` 直接
  elaborate，不进 `lake build`、重放集合或认证闭包）。六条客户端定理：
  1. `client_flat_flux`：平坦子图上公式给出 `∫_H ⟪F(x₀+ι y), e⟫`；
  2. `client_flat_flux_sign`：若场沿边界指向 `+e`，则总散度非负——**方向约定的实质检验**，
     约定相反不等式即反号；
  3. `client_tilted_tangential`：倾斜线性图 `g y = ⟪c,y⟫` 上取**纯切向**场 `η • ι c`，
     法向分量 `⟪F, e⟫` 恒为零，公式给出 `-‖c‖² ∫ η∘Ψ`——**漏掉 `-∇g` 项就会得到 0**；
  4. `client_one_dimensional`：取 `V = ℝ`、切空间 `(ℝ∙1)ᗮ`（零维），公式退化为
     `∫_{(-∞,b)} F' = F b`，其中还核对了 `divergence = deriv`（一维迹）与零维空间上 `volume univ = 1`；
  5. `client_local_gaussGreen_halfSpace`：半空间 `{⟪a,x⟫<0}` 作为 `SmoothDomain`，
     对支撑落在某张图表柱内的场，局部 Gauss–Green 给出
     `∫_U div F = ∫_{{⟪a,x⟫=0}} ⟪F, a⟫ ∂surfaceMeasure`，外法向是**具体的 `+a`**；
  6. `client_halfSpace_chart_exists`：该假设非空。
  六条的传递公理都只有标准三条。上三轮的 `AreaFormulaAudit.lean`、`BoundaryChartAudit.lean`、
  `PerimeterInterfaceAudit.lean` 重新运行，结论与公理不变。
* **严格模式**：`Analysis/SubgraphDivergence.lean`、`Analysis/GraphIntegral.lean`、
  `Analysis/ImplicitGraph.lean`、`KLS/Geometry/BoundaryChart.lean`、
  `KLS/Geometry/LocalGaussGreen.lean` 与四个审计客户端在 `lake env lean -DwarningAsError=true`
  下退出 0。
* **含 hole 的 WIP**：四个文件普通模式实际重新 elaborate，退出 0，诊断恰好是预期的 3 / 4 / 8 / 5 条
  `declaration uses 'sorry'`，无其他警告或错误。**这不是严格模式通过。**
* 完成默认 `lake build`（3393 jobs，与上一轮相同——新模块不在库根聚合内），并从仓库根运行
  `python3 research/verify.py`；`lem:relative-perimeter-smoothing` 的 infrastructure 证据哈希按本轮
  源码重算并加入三个新模块，note 与 gaps 同步更新，状态仍为 `missing`。最终回执由
  `build/verification/latest.json` 指向，与最终源码快照匹配。

证据都信任固定版本的第三方编译依赖，不代表独立重建 Mathlib、远端 CI 或 Blueprint 排版通过。
审计脚本与日志留在忽略的 `build/`。本轮按 owner 要求不提交、不推送。

## 距离完整 Gauss–Green 还剩什么

**只剩单位分解拼接。** 具体地：对紧支撑 `C¹` 场 `F`，取 `tsupport F ∩ frontier U` 的有限图表柱覆盖
（每个边界点由 `exists_boundaryChart` 给出一张柱），再加上开集 `U` 与 `(closure U)ᶜ` 两块，
做从属于该覆盖的有限光滑单位分解 `{χ_i}`，把 `F = Σ_i χ_i F` 拆开；每个 `χ_i F` 或者支撑落在某张
图表柱内（用本轮的局部定理），或者支撑与 `frontier U` 不交（此时两侧都退化：内部块用
`Analysis.integral_divergence_eq_zero` 的同一技术，外部块两侧皆为零）。分解函数的导数项在求和
`Σ_i ∇χ_i = 0` 时抵消。Mathlib 提供 `SmoothPartitionOfUnity`/`ContDiffBump` 作为输入。

coarea、Sard、恢复序列此后仍各自独立开放。
