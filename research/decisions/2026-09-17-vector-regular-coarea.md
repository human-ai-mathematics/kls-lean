# 余维 m 的加权切片可测性，与余维 m 正则 coarea 公式

2026-09-17。本轮**证明新定理**：请求的**余维 m 加权切片可测性**，
以及它立刻装配出的 **余维 m 正则情形 coarea 公式**——标量 `L9` 的类比。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T170802.272750Z/report.json`：10 个门、211 个本地模块内核重放、
554 条目，快照
`90d7047331fbb80fe9b65b48b4eeaee61329c47dd97dcb372a0089ea6ccf8ad4`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 走的不是标量那条路，必须说清

标量情形的切片可测性（`KLS/Geometry/OpenSliceMeasurable.lean`）对**任意** Borel `S ⊆ O`
成立，**不需要正则点假设**，它经由 `KLS/Geometry/SurfaceSlicing.lean` 的 **Eilenberg 切片不等式**。
**余维 m 的 Eilenberg 不等式本仓库没有**，Mathlib 也不提供。

所以本轮**改走图**：在一张水平族的图上，切片积分就是参数–水平乘积上**某一个可测函数的 Tonelli 截面**，
可测性因此是直接的，**完全不用任何切片不等式**。
代价是：本轮的切片可测性**只在微分满射处成立**。
这对正则情形足够，但**不覆盖临界部分**——见「没有做的事」。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/VectorRegularCoarea.lean`
（211 行，本地 import 闭包 21 个模块，**无 WIP**）。

* **`measurable_setLIntegral_inter_levelSet_levelGraphFamily`**：
  一张图上的**加权切片可测性**。用上一轮的切片描述与加权面积公式把
  `t ↦ ∫⁻ over (Ψ''A) ∩ {u = t}, g` 写成 `t ↦ ∫⁻ y, (A.indicator F) (y, t)`，
  `F` 在 `H × W` 上可测，于是 `Measurable.lintegral_prod_left'` 直接给出可测性。
* **`exists_vector_coarea_neighborhood_measurable`**：邻域形式，等式与可测性一并给出。
* **`coarea_of_contDiffOn_of_coareaJacobian_ne_zero`**：**余维 m 正则情形的 coarea 公式**。
  在微分处处满射的开集 `O` 上，对**任意** Borel `S ⊆ O` 与**任意**可测 `ℝ≥0∞` 权重：
  水平函数**可测**，且
  `∫⁻_S coareaJacobian(Du)·g dx = ∫⁻_t ∫⁻_{S ∩ {u = t}} g dℋ^{n-m} dt`，
  纤维测度是余维的归一化 Hausdorff 测度 `hausdorffNormalized V (finrank V − finrank W)`。
  装配方式与标量 `L9` 相同：可数覆盖、`disjointed` 不交化、逐片用邻域形式、`lintegral_tsum` 交换。

  注意结论给的是 **`Measurable`**，比标量 `L9` 的 `AEMeasurable` **更强**；
  这是走图路线的副产品。

假设只有：`u` 在开集 `O` 上 C¹，且 `O` 上处处 `coareaJacobian (fderiv ℝ u x) ≠ 0`（即微分满射）。
**无有限性、有界性、可积性、正则值、SFinite**，`O` 外无正则性。

## m = 1 逐字退回已证的标量 L9

审计客户端的 `scalar_L9` **逐字重写**仓库已证的
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` 的语句——梯度范数、`surfaceMeasure V`、
`AEMeasurable`——并**从余维 m 的定理把它兑现**。桥梁三条都已证：
`coareaJacobian_fderiv`（密度退回 `‖gradient u x‖ₑ`）、
`finrank ℝ V − finrank ℝ ℝ = finrank ℝ V − 1` 使纤维测度就是 `surfaceMeasure V`、
以及 `coareaJacobian_ne_zero_of_fderiv_ne_zero`（实值非零微分即满射）。

## 本轮没有做的事

* **没有证明一般的余维 m coarea 公式**（标量 `L11`–`L13` 的类比）。
  它需要处理**临界集**，而这需要余维 m 的 Sard 或临界切片论证，两者都没有。
* **没有证明不带正则性假设的切片可测性**。
  标量情形靠 Eilenberg 切片不等式做到这一点；**余维 m 的 Eilenberg 不等式没有证**。
  没有它就无法把临界部分纳入。
* 没有碰临界部分、尖锐有限正则 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍是 `B1` 与已证伪的 `A0`。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 余维 m 纲领现状

已证：coarea Jacobian 与正则集刻画、线性面积公式与仿射纤维、A1、B1/B2 图面积公式、
纤维 Jacobian 恒等式、保测分裂、带参数隐函数图化、纤维方向 m 维换元、
加权图面积公式、局部 coarea 等式，以及本轮的**正则情形 coarea 公式**。

仍开放：余维 m 的 Eilenberg 切片不等式；不带正则性的切片可测性；
余维 m 的 Sard／临界切片；因而一般的余维 m coarea 公式。
Federer 面积公式 `A0`（已证伪其路线语句的写法）与 `A2`–`A5` 也仍开放。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorRegularCoareaAudit.lean` 的 **11 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；含空集、全空间（无有限性）、恒为 `∞` 的权重、
  零维靶空间（此时每点都正则）、以及 m = 1 逐字退回标量 `L9`
  （最后一条报告是仓库已证的标量 `L9` 本身，供对照）。
* 重跑全部 **38 个审计客户端**（`research/audits` 31 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-regular-coarea.json`，最终核对另存
  `build/audit/vector-regular-coarea/final-snapshot.json`。
