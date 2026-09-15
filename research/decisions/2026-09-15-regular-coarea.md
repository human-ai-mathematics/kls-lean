# 正则开域 C¹ 带权 coarea（L9）

2026-09-15。本轮完整证明 L9 的两个合取分量。不提交、不推送，不迁出 WIP 洞，不改历史决定。
起始 HEAD `2965b32bc79bdb24921c633df12102450eaedcc4`；起始回执
`build/verification/20260915T082341.547238Z/report.json` 为 passed，完整快照逐项一致：
430 个条目，SHA256 `d9ffd66ef3308d3469af51177aff4ca5a3adabbe2a8e20fb370fb6a36df26289`，
182 个重放模块。上轮证据绑定的 20 个 `build/audit` 文件哈希也全部一致。

## 精确结果

`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`，位于
`formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean`：

```lean
IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
MeasurableSet S → S ⊆ O → Measurable g →
AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) volume ∧
(∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
  ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V)
```

空间假设为有限维实内积空间及其 Borel 可测结构。实现省去可推导的 `CompleteSpace V`；
独立客户端 `RegularCoareaAudit.target` 保留用户的全部实例参数，并逐字复述完整目标。
它与原 `WeightedCoareaRouteStatements` 中 L9 的文本除空白外完全一致，且有实际证明。
没有增加全局 C¹/Lipschitz、有界性、有限体积、可积性、连通性、非零维或 SFinite 假设。
Mathlib `gradient` 与仓库归一化 `surfaceMeasure` 未变；既有 Lean 文件和签名未修改。

## 证明路线与同维换元的实现选择

1. `Analysis/LocalInverse.lean` 只依赖 Mathlib：`exists_contDiffOn_localInverse` 在任意指定
   开域内构造局部同胚，正向和反向在各自整个开域上 C¹。使用 `restrContDiff` 限制到双向
   C¹ 的开集，而非仅断言逆函数在中心可微。
2. `Analysis/RegularChart.lean` 保留联合参数 `(y,t)`。`exists_regularChart` 对
   `Φ(x) = P x + u(x)e` 用逆函数定理，`levelChartHeight(y,t)` 为局部逆的法向坐标；
   `levelChart_inverse` 同时证明逆像等于图点和 `u(图点) = t`，对联合开域的所有参数成立。
3. 体积换元使用**等价的逐纤维路线**，没有新增 n 维行列式恒等式：既有
   `measurePreserving_splitHomeomorph` 经 `WithLp 2 (H × ℝ)` 的线性等距同构，严格证明
   内积诱导的正交分解保体积；然后在每条垂直实纤维上用 Mathlib
   `lintegral_image_eq_lintegral_abs_deriv_mul`。该定理本身是用户建议的
   `lintegral_image_eq_lintegral_abs_det_fderiv_mul` 的一维特化。纯 Mathlib 新模块
   `Analysis/FiberIntegral.lean` 用 Tonelli 装配任意 Borel 分片上的垂直换元，并证明
   `continuous_deriv_snd`，明确给出 Jacobian 对联合参数的可测性。
4. `abs_deriv_mul_norm_gradient` 证明
   `|∂t ψ| * ‖∇u‖ = sqrt(1 + ‖∇y ψ‖²)`。链式法则给出
   `(∂t ψ) * ⟪∇u,e⟫ = 1`，水平方向给出
   `∇u = ⟪∇u,e⟫ • (ι(-∇y ψ)+e)`。使用绝对值，允许任意导数符号。
   ENNReal 版本只转换非负实数的乘积，再结合乘法结合律乘上 `g`；不除以权重，
   不用有限值减法，不消去 `⊤`。零权重、`0 * ⊤`、无限体积和无限截面均保留原有含义。
5. 对联合高度在参数小球上用 L8 模块的 `exists_contDiff_one_eqOn_ball` 取全局 C¹
   代表，在这个球内应用已证的全局带权图面积公式。这里没有假定高度在整个原开域上
   可延拓；只在更小的内部球上相等。任意 Borel 参数片的像与每个水平的图像等式均证明。
   `setLIntegral_coarea_graph_family` 得到局部 coarea。
6. 对原 `u` 再作同样的内部局部代表处理。`exists_regular_coarea_neighborhood` 将结果
   转回原函数及原梯度，并用正交补的维数公式将 `hausdorffNormalized` 包装为
   `surfaceMeasure`。第二可数性取可数开覆盖；`disjointed` 构造不交 Borel 分片；两边
   用 `lintegral_iUnion` 和 `lintegral_tsum` 拼接。
7. 可测性独立先证于 `KLS/Geometry/OpenSliceMeasurable.lean`。每个内部球上取全局 C¹
   代表，在紧闭球上获得 Lipschitz 常数，对分片应用 L5，再作可数求和。**不将 L5 的全局
   连续性加到 L9**；无正则点假设也能证明这一可测性分量。Tonelli 只用于体积测度，
   未给环境 `surfaceMeasure` 安装 SFinite 实例。

没有使用 L10、Sard、WIP、Whitney 延拓或本轮目标自身作为前提。
`ImplicitGraph.lean`、`GraphIntegral.lean` 及所有既有 Lean 文件原样保留。

## 验证与证据

* 五个新模块严格编译通过。新模块共 16 条定理和 2 个定义。
* `build/audit/RegularCoareaAudit.lean` 严格编译通过：完整 L9；无限权重；空集上无限
  权重两边均为零；零维下正则域必空及完整 L9 实例；`u = id`、`S = ℝ` 时两边实际为
  `⊤`；二维正交分解中每个实仿射直线截面均为 `⊤`；
  `jump x = if 0 < x then x else 1` 于 `(0,∞)` 的完整无限权重实例，并独立证明
  `jump` 不连续，明确排除依赖全局 C¹ 的误读。
* 全部 29 条新声明与客户端声明的公理输出只含 `propext`、`Classical.choice`、
  `Quot.sound`，无 `sorryAx`。新模块导入闭包无 WIP、CriticalSlice 或 Sard 模块。
* 用户指定的 15 个既有客户端全部严格重跑通过，包括各自的 `preserved_*` 具名参数
  检查；三个 WIP 文件逐个实际编译通过，直接洞 2/3/5，总数 10。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 是最终验收步骤。
  本轮机器证据为 `research/explorations/2026-09-15-regular-coarea.json`，它先于最终
  验证写入并被最终回执哈希绑定。最终 `build/verification/latest.json` 与最终源码
  快照完全相等的核对，另存 `build/audit/l9-final-snapshot.json`。`build/audit` 被忽略，
  因而其客户端及日志由本轮证据 JSON 单独记录哈希；最终核对再逐项检查。

## 精确未完成边界

本轮只完成 L9。L11（一般 C¹ coarea）、L12（Lipschitz coarea）、L6/L6a/L7 的 Whitney
C¹ 延拓与精确分片仍未证明。两个原有等式
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 与
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 仍是直接洞，未迁出。
尖锐 `C^(finrank)` 的 `Analysis.sard` 仍为直接洞且无下游消费者；Eilenberg 常数尖锐性、
`smoothConstant_le_minkowskiConstant`、`smoothConstant_mul_lintegral_min_superlevel_le`
及两个 Cheeger 常数相等仍未证明。证书仍 24，perimeter infrastructure 仍 missing，
没有扩展 Blueprint leanok 或认证范围。
