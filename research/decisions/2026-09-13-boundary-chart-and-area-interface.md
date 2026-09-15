# 2026-09-13 — Gauss–Green 前置：SmoothDomain 局部光滑图表示、区域侧别、外法向公式与图面积接口

Owner 要求完成 Gauss–Green 的下一项前置工作：`SmoothDomain` 在边界点附近的局部光滑图表示、区域侧别与
外法向公式，并把结果接通既有的余维一图面积公式；直接实施证明与验证，本轮不提交、不推送。承接
[Gauss–Green 面积公式记录](2026-09-12-gauss-green-area-formula.md)、
[接口接入记录](2026-09-12-perimeter-interface-integration.md)与
[当前状态审计](2026-09-12-status-audit-and-wip-retention.md)。上一轮未提交的模块拆分、三个接口证明、
图面积公式与散度恒等式全部保留，未重置或改写；历史记录保持原文与原计数。

## 结论先说

| 目标 | 状态 | 传递公理 |
| --- | --- | --- |
| 1. 边界点附近的 `C^∞` 图表示（含区域侧别、参数化单射性与逆参数映射） | **完成** | 标准三条 |
| 2. 图坐标下的外法向公式（含分母为正、符号确定） | **完成** | 标准三条 |
| 3. 局部图与既有面积公式的接口（`surfaceMeasure` 的局部边界片等式） | **完成** | 标准三条 |
| 向量场 Gauss–Green `integral_divergence_eq_integral_inner_outwardNormal` | **未完成**，仍是直接 `sorry` | 含 `sorryAx` |
| 标量 Gauss–Green、`gradient_mollifiedIndicator_eq` | 证明体已填，仍由 C1 归约 | 含 `sorryAx` |

本轮**没有**证明完整 Gauss–Green、子图 Fubini/FTC 恒等式、单位分解拼接、coarea、Sard 或恢复序列。
证书数仍是 24，没有新增 ledger 节点，没有 Blueprint `\lean`/`\leanok` 锚点，
`lem:relative-perimeter-smoothing` 的 infrastructure 状态仍为 `missing`。
WIP 直接 hole 总数不变，仍是 20。

## 1. 局部 `C^∞` 图表示

### 数学内容

设 `V` 有限维实内积空间，`U : SmoothDomain V`，`x₀ ∈ frontier U.carrier`。取
`ν = U.outwardNormal x₀`（`‖ν‖ = 1`），`H = (ℝ ∙ ν)ᗮ` 为切超平面，`ι = H.subtypeₗᵢ` 为自然等距嵌入。
则存在全局 `C^∞` 的 `g : H → ℝ`、参数开邻域 `Ω ∋ 0`、半高 `δ > 0`，使得在柱状邻域

```
Cyl = { x | graphProj ι (x - x₀) ∈ Ω ∧ |⟪ν, x - x₀⟫| < δ }
```

内部：

* `frontier U.carrier ∩ Cyl = Ψ '' Ω`，其中 `Ψ y = x₀ + ι y + g y • ν`
  （**集合等式**，不是"边界包含于图中"）；
* `U.carrier ∩ Cyl = { x ∈ Cyl | ⟪ν, x - x₀⟫ < g (graphProj ι (x - x₀)) }`
  （区域恰好是图下方那一侧）；
* `g 0 = 0`（中心点归一化），`∀ y ∈ Ω, |g y| < δ`（图不触及柱壁）。

参数化接口一并给出：`Ψ` 单射（`BoundaryChart.injective_map`），逆参数映射是
`tangentCoord x₀ x = graphProj ι (x - x₀)`，满足 `tangentCoord x₀ (Ψ y) = y`
（`BoundaryChart.tangentCoord_map`），`Ψ '' s ⊆ frontier U ∩ Cyl`（`image_subset_frontier`），
`Cyl` 开（`isOpen_cylinder`）。

Lean 打包为 `KLS.SmoothDomain.BoundaryChart U x₀` 结构，存在性是
`KLS.SmoothDomain.exists_boundaryChart`。通用部分是 `Analysis.GraphRepr` 与
`Analysis.exists_graphRepr`（对任意 `C^∞` 的 `φ`，`φ x₀ = 0`，`gradient φ x₀ = c • e`，`c > 0`）。

### 正则性路线：反函数定理，不是隐函数定理

Mathlib 的 `HasStrictFDerivAt.implicitFunctionOfComplemented` 只给**一点**的严格可微，
面积公式需要邻域上的 `C¹`。本轮走反函数定理：对

```
Φ x = ι (graphProj ι (x - x₀)) + φ x • e          (Analysis.flattenChart)
```

`Φ` 全局 `C^∞`，`Φ x₀ = 0`，`DΦ(x₀) = flattenCLM ι e c`，其显式逆是 `flattenCLM ι e c⁻¹`
（`Analysis.flattenEquiv`，由 `ContinuousLinearEquiv.equivOfInverse` 构造，两侧逆等式各一行）。
于是 `ContDiffAt.toOpenPartialHomeomorph` 给出局部同胚 `F`。

关键一步是把 `ContDiffAt.to_localInverse` 的**单点**结论换成邻域结论：可逆算子集合是开集
（`ContinuousLinearEquiv.isOpen`），`x ↦ fderiv ℝ Φ x` 连续，所以
`N = F.source ∩ (fderiv Φ) ⁻¹' range (↑)` 开且含 `x₀`；`T = F.target ∩ F.symm ⁻¹' N` 开
（`OpenPartialHomeomorph.isOpen_inter_preimage_symm`）且含 `0`。对 `T` 中每个点都可以用
`OpenPartialHomeomorph.contDiffAt_symm`，于是 `F.symm` 在整个 `T` 上逐点 `ContDiffAt ℝ ∞`。
取 `Ω₀ = ι ⁻¹' T`，`g₀ y = ⟪e, F.symm (ι y) - x₀⟫`，由 `Φ (F.symm (ι y)) = ι y` 取 `⟪e, ·⟫` 分量得
`φ (F.symm (ι y)) = 0`，取切向分量得 `F.symm (ι y) = x₀ + ι y + g₀ y • e`。
这就是 `Analysis.exists_local_implicit`。

### 侧别的证明

在 `⟪∇φ, e⟫ > 0` 的开集内取球 `B(x₀, r)`（同时落在给定的邻域 `N₀` 内），令 `δ = r/2`，
`Ω ⊆ ball(0, min(ρ, r/2)) ∩ {|g| < δ}`。柱内每点满足 `‖x - x₀‖² = ‖y‖² + t² < r²`（勾股，
`IsGraphSplitting.norm_add_smul_sq`），故 `Cyl ⊆ B(x₀, r)`。对固定 `y ∈ Ω`，
`h(u) = φ(x₀ + ι y + u • ν)` 在 `Icc (-δ) δ` 上导数 `= ⟪∇φ(·), ν⟫ > 0`，
`strictMonoOn_of_deriv_pos` 给出严格单调；`h (g y) = 0`，于是

```
φ x < 0  ↔  t < g y        φ x = 0  ↔  t = g y
```

两条都是 `↔`，因此 `{φ = 0} ∩ Cyl` 与 `{φ < 0} ∩ Cyl` 都是**等式**而非包含。
再用已有的 `SmoothDomain.frontier_inter_eq` 与定义式 `U ∩ W = {φ < 0} ∩ W`（取 `N₀ = W`，
所以 `Cyl ⊆ W`）把关于 `φ` 的陈述换成关于 `U` 的陈述；结论不依赖选了哪个定义函数。

### 零维

`Nontrivial V` 没有作为假设加入任何陈述。零维（更一般地 `Subsingleton V`）时每个集合都是
既开又闭的，光滑区域的边界为空，因此所有以 `x₀ ∈ frontier U.carrier` 为前提的陈述都空成立；
需要非退化的地方（`finrank_tangentSpace` 中的 `ν ≠ 0`）由 `‖ν‖ = 1` **导出**，不是额外假设。

## 2. 外法向公式

`KLS.SmoothDomain.BoundaryChart.outwardNormal_graph`：对 `y ∈ Ω`，

```
U.outwardNormal (Ψ y) = (√(1 + ‖∇g y‖²))⁻¹ • (ι (-(∇g y)) + ν)
```

除法按 Lean 中向量的标量乘法写成 `(graphJacobian (gradient g y))⁻¹ • (…)`；
`graphJacobian a = √(1 + ‖a‖²) > 0` 由 `Analysis.graphJacobian_pos`（`positivity`）给出，
即**分母恒正**，不是"非零"。

证明分两段，都放在通用层：

* `Analysis.gradient_eq_smul_of_graph`：`φ ∘ Ψ ≡ 0` 在开集 `Ω` 上，故
  `fderiv φ (Ψ y) ∘ DΨ(y) = 0`；`DΨ(y) v = ι v + ⟪∇g y, v⟫ • ν`，取 `v` 遍历 `H` 得
  `graphProj ι (∇φ(Ψ y)) = β • (-(∇g y))`，其中 `β = ⟪∇φ(Ψ y), ν⟫`；再用正交分解
  `a = ι (graphProj ι a) + ⟪ν, a⟫ • ν` 得 `∇φ(Ψ y) = β • (ι (-(∇g y)) + ν)`。
* `Analysis.norm_inv_smul_eq_graphJacobian_inv_smul`：`β > 0` 时归一化
  `‖a‖⁻¹ • a = (graphJacobian b)⁻¹ • (ι (-b) + ν)`，用到
  `‖ι(-b) + ν‖² = ‖b‖² + 1`（勾股）。

**符号是确定的，不只是"相差正负号"**：`β = ⟪∇φ(Ψ y), ν⟫ > 0` 由结构字段
`GraphRepr.inner_gradient_pos` 在整个柱内保证，而该字段来源于 `ν` 是 `∇φ(x₀)` 的正规化方向加上
连续性；同一个正性又是第 1 节侧别单调性的依据，两者用的是同一个事实，方向约定不会自相矛盾。

**梯度的解释**：`g` 是**全局** `C^∞` 函数（见下），`∇g y` 就是它在 `y` 处的 Mathlib `gradient`，
不存在"局部函数的梯度"与"延拓的梯度"两个对象。

## 3. 局部图与面积公式的接口

### 采用的路线：在表示定理内部做截断，交付全局 `C^∞` 的 `g`

既有的 `Analysis.hausdorffNormalized_image_graphMap` 要求 `ContDiff ℝ 1 g`（全局），而反函数定理
只给邻域上的光滑性。两条候选路线中本轮选**第二条**：缩小参数邻域并构造全局光滑延拓。

具体做法写在 `Analysis.exists_graphRepr` 内部，而不是留给调用方：

1. 取 `ρ > 0` 使 `closedBall (0, 2ρ) ⊆ Ω₀`（`Ω₀` 是反函数定理给出的光滑邻域）；
2. 取 `ContDiffBump (0 : H)`，`rIn = ρ`、`rOut = 2ρ`，令 `g = χ · g₀`；
   `g` 全局 `C^∞`：在 `Ω₀` 内是两个 `ContDiffAt` 的乘积，在 `closedBall(0,2ρ)` 外 `χ ≡ 0` 故 `g ≡ 0`
   在一个开集上，两类点覆盖全空间；
3. 参数集 `Ω ⊆ ball(0, min(ρ, r/2))`，在那里 `χ ≡ 1`，故 `g = g₀`。

因此交付给调用方的 `BoundaryChart.height` 本身就是全局 `C^∞`（结构字段
`contDiff_height : ContDiff ℝ ∞ height`）。**没有把局部 `ContDiffOn` 当成全局 `ContDiff` 用，
也没有把"存在全局延拓"当作额外假设**：延拓是构造出来的，并且函数与导数在所需区域一致
（`Ω` 上 `g = g₀`，`Ω` 开故梯度也一致）。面积公式本身没有被削弱或改写。

### `x₀` 平移的测度不变性

既有图映射是 `graphMap ι e g y = ι y + g y • e`，没有平移项，而边界片是
`Ψ y = x₀ + graphMap ι e g y`。新增 `Analysis.hausdorffNormalized_image_add_left`：
平移是等距，`Isometry.hausdorffMeasure_image` 消去它，`hausdorffNormalized` 只是 `μH` 的常数倍，
于是 `Analysis.hausdorffNormalized_image_graphChartMap` 把面积公式原样搬到 `Ψ` 上。

### 面向 `SmoothDomain` 的最终等式

`KLS.SmoothDomain.BoundaryChart.surfaceMeasure_image`：对**可测的参数集** `s`，

```
surfaceMeasure V (Ψ '' s) = ∫⁻ y in s, ENNReal.ofReal (√(1 + ‖∇g y‖²)) ∂volume
```

右端对切空间 `H = (ℝ ∙ ν)ᗮ` 的 `volume` 积分，Jacobian 就是 `graphJacobian (∇g y)`。
指标的换算是 `finrank_tangentSpace`：`finrank ℝ H = finrank ℝ V - 1`，配合
`surfaceMeasure V = hausdorffNormalized V (finrank ℝ V - 1)`。

`BoundaryChart.surfaceMeasure_frontier_inter_cylinder` 给出精确限定的版本：

```
surfaceMeasure V (frontier U.carrier ∩ Cyl) = ∫⁻ y in Ω, ofReal (√(1 + ‖∇g‖²)) ∂volume
```

左端是**一张图所覆盖的那一片边界**（柱内那一片），不是整个边界；两者的区别由
`frontier_inter_cylinder` 的集合等式和 `param` 的显式出现固定下来。

## 模块组织与依赖拆分

| 层 | 模块 | 内容 | hole |
| --- | --- | --- | ---: |
| 通用几何 | `Analysis/ImplicitGraph.lean`（新） | 正交分解 `IsGraphSplitting`、展平图 `flattenChart`、局部隐函数 `exists_local_implicit`、图参数化与柱、沿图的梯度公式、`GraphRepr` 与 `exists_graphRepr`、平移后的面积公式 | 0 |
| 应用层 | `KLS/Geometry/BoundaryChart.lean`（新） | 迁入的 `outwardNormal` 及其四条已证引理；切超平面 `tangentSpace`/`tangentEmbedding`/`tangentCoord`、`isGraphSplitting_tangent`、`finrank_tangentSpace`；`BoundaryChart` 与 `exists_boundaryChart`；两条 `surfaceMeasure` 等式 | 0 |
| 未完成 WIP | `KLS/WIP/AnalyticPrerequisites.lean` | 仅剩 Gauss–Green、coarea、Sard | 4 |

`outwardNormal` 原先与未完成的 Gauss–Green 同处 `AnalyticPrerequisites`，而边界图表示是
Gauss–Green 的**输入**，必须在其下方，所以做了最小依赖拆分：把 `outwardNormal` 及
`outwardNormal_eq`、`norm_outwardNormal`、`continuousOn_outwardNormal`、
`measurable_outwardNormal` 逐字迁入 `KLS/Geometry/BoundaryChart.lean`，命名、命名空间、陈述不变，
没有兼容别名、没有重复证明、没有转发声明；唯一的消费者 `AnalyticPrerequisites` 已改为 import 新模块。
`SmoothDomain` 结构本身**没有**搬动（那不是本轮所需），所以 `BoundaryChart` 为取用
`SmoothDomain` 与 `frontier_inter_eq` 而 import `KLS/WIP/RelativePerimeter.lean`；它不使用该文件的
三条未完成证明，`#print axioms` 已核实。依赖方向无环：

```
Analysis/LevelSet → Analysis/AreaFormula → Analysis/ImplicitGraph
KLS/Geometry/SurfaceMeasure → Analysis/LevelSet → KLS/WIP/RelativePerimeter → KLS/Geometry/BoundaryChart → KLS/WIP/AnalyticPrerequisites
```

`Analysis/` 下没有引入任何 `sorry`；正式聚合入口（库根）与 24 个证书都不 import 这些模块。
没有新增公理，没有隐藏 `sorry`，没有削弱结论或缩小数学范围：没有任何一条新陈述假设 `U` 有界、
边界总测度有限或 `V` 非平凡。

## 计数（本轮重新统计，不沿用旧数字）

* WIP 直接 hole 合计仍为 **20**：`RelativePerimeter` 3、`AnalyticPrerequisites` 4、
  `CheegerInfimum` 8、`Energy/WIP/Cheeger` 5。四个文件都实际重新 elaborate，退出 0，
  诊断恰好是这 3 / 4 / 8 / 5 条 `declaration uses sorry`，无其他警告或错误。
* `AnalyticPrerequisites` 迁出 5 条声明后：**9 条公开定理、0 条定义；5 条已填证明体、4 条直接
  hole；已填的 5 条中只有 2 条无传递 `sorryAx`**
  （`isLocallyFiniteMeasure_surfaceMeasure_frontier`、`integrableOn_smul_outwardNormal`）。
* `KLS/Geometry/BoundaryChart.lean`：23 条公开声明（其中 5 条是迁入的），全部无 `sorry`。
* `Analysis/ImplicitGraph.lean`：58 条公开声明，全部无 `sorry`。

### 对此前计数的勘误

上一轮记录写的"`AnalyticPrerequisites` 迁出 `divergence` 后共 12 条义务，8 条已填证明体，
其中 6 条无传递 `sorryAx`"把迁出的 `divergence`**定义**从**定理**数里减掉了。迁移前的正确数字是
**13 条公开定理 + 1 条定义（`outwardNormal`）**，其中 9 条定理已填证明体、4 条直接 hole，
6 条已填定理无传递 `sorryAx`。历史记录
[2026-09-12 Gauss–Green 面积公式](2026-09-12-gauss-green-area-formula.md) 与
`research/verification.md` 中对应段落的原文不改写；勘误由本记录与
`KLS/WIP/AnalyticPrerequisites.lean` 的模块说明承担，`research/verification.md` 另起一段记录当前状态。

## 验证

* **直接公理检查**（只允许 `propext / Classical.choice / Quot.sound`）：
  `Analysis.exists_local_implicit`、`Analysis.exists_graphRepr`、
  `Analysis.gradient_eq_smul_of_graph`、`Analysis.GraphRepr.normalized_gradient_map`、
  `Analysis.GraphRepr.zeroSet_inter_cylinder`、`Analysis.GraphRepr.sublevel_inter_cylinder`、
  `Analysis.hausdorffNormalized_image_graphChartMap`、
  `KLS.SmoothDomain.isGraphSplitting_tangent`、`KLS.SmoothDomain.finrank_tangentSpace`、
  `KLS.SmoothDomain.exists_boundaryChart`、
  `KLS.SmoothDomain.BoundaryChart.surfaceMeasure_image`、
  `KLS.SmoothDomain.BoundaryChart.surfaceMeasure_frontier_inter_cylinder`，以及迁入后的
  `outwardNormal_eq`、`norm_outwardNormal`、`continuousOn_outwardNormal`、
  `measurable_outwardNormal` —— 全部只有标准三条。
  `integral_divergence_eq_integral_inner_outwardNormal`、
  `setIntegral_gradient_eq_integral_smul_outwardNormal`、`gradient_mollifiedIndicator_eq`、
  `sard`、`ae_forall_fderiv_ne_zero`、两条 coarea 仍含 `sorryAx`（如上表）。
* **独立客户端**：`build/audit/BoundaryChartAudit.lean`（忽略目录，`lake env lean` 直接
  elaborate，不进 `lake build`、重放集合或认证闭包）。八条客户端定理用**能检验方向的具体模型**：
  半空间 `{⟪a,x⟫ < 0}`（单位 `a`）与单位球。
  1. 半空间的外法向是 `+a`（不是 `-a`）；
  2. 仅由图表示的**陈述**（不用构造过程）推出半空间的任一图表的高度函数在参数集上恒为 `0`，
     梯度也为 `0`；
  3. 图表的法向公式在该模型上算出来就是 `+a`；
  4. 从 `x₀` 沿 `-ν` 走留在区域内且严格在图下方，沿 `+ν` 走离开区域且严格在图上方
     ——这是方向约定的实质检验，约定相反两条结论会互换；
  5. 平坦边界片的 `surfaceMeasure` 恰等于参数集的 Lebesgue 测度（归一化接口，Jacobian = 1）；
  6. 平坦模型上图表存在；
  7. 单位球在边界点 `x₀` 的外法向是 `+x₀`（曲边模型上的方向检验）；
  8. 单位球上图表存在。
  八条的传递公理都只有标准三条。上两轮的 `AreaFormulaAudit.lean` 与
  `PerimeterInterfaceAudit.lean` 重新运行，结论与公理不变。
* **严格模式**：`Analysis/ImplicitGraph.lean`、`KLS/Geometry/BoundaryChart.lean` 与三个审计客户端
  在 `lake env lean -DwarningAsError=true` 下退出 0。
* **含 hole 的 WIP**：四个文件普通模式实际重新 elaborate，退出 0，诊断恰好是预期的 3 / 4 / 8 / 5 条
  `declaration uses sorry`，无其他警告或错误。**这不是严格模式通过。**
* 完成默认 `lake build`（3393 jobs），并从仓库根运行 `python3 research/verify.py`；
  `lem:relative-perimeter-smoothing` 的 infrastructure 证据哈希按本轮源码重算并加入两个新模块，
  note 与 gaps 同步更新，状态仍为 `missing`。最终回执由 `build/verification/latest.json` 指向，
  与最终源码快照匹配。

证据都信任固定版本的第三方编译依赖，不代表独立重建 Mathlib、远端 CI 或 Blueprint 排版通过。
审计脚本与日志留在忽略的 `build/`。本轮按 owner 要求不提交、不推送。

## 距离 Gauss–Green 还剩什么

1. **子图上的局部 Gauss–Green**：经 `V ≃ₗᵢ WithLp 2 (H × ℝ)` 做 Fubini，法向分量用微积分基本定理，
   切向分量需要对变上限积分 `y ↦ ∫_{-∞}^{g y} F_i` 求导（Leibniz 规则）再整体积分为零。
   它所需要的局部 `C^∞` 图表现在已经有了（`exists_boundaryChart`）。
2. **光滑单位分解**：紧支撑上的有限光滑单位分解，用于把局部恒等式粘起来并抵消分解函数的导数项；
   再与 `BoundaryChart.surfaceMeasure_image` 合成得到向量场形式。
3. 之后 coarea、Sard、恢复序列仍然各自独立开放。
