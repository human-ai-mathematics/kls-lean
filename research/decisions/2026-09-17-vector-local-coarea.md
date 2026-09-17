# 加权的余维 m 图面积公式，与一张图上的局部 coarea 等式

2026-09-17。本轮**证明新定理**：请求的**加权余维 m 图面积公式**，
以及它与前两轮件拼起来的直接结果——**一张图上的局部 coarea 等式**，
进而**每个正则点的邻域上的 coarea 等式**。
**这不是余维 m 的正则 coarea 公式**，缺口在最后写明。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T165144.989890Z/report.json`：10 个门、209 个本地模块内核重放、
549 条目，快照
`b2c11a93ec5bfe245ad6791cd300eeebae4e1e1d74fb979909db61c7f11505f6`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

### 一、加权的余维 m 图面积公式

新模块 `formalization/FunctionalInequalities/Analysis/VectorGraphIntegral.lean`
（92 行，本地 import 闭包 11 个模块，**无 WIP**），
`OpenGraphIntegral.lean` / `GraphIntegral.lean` 的余维 m 类比。

* **`map_vectorGraphMap_withDensity`**：把 `B2`（集合测度的等式）升级为**测度的等式**——
  图参数化把 Jacobian 加权的 Lebesgue 测度前推为限制在图上的归一化曲面测度。
  用到的两条性质仓库都已证：图映射**按构造单射**，其像可测。
* **`setLIntegral_image_vectorGraphMap`**：**加权的余维 m 图面积公式**。
  任意可测 `ℝ≥0∞` 权重在一片 C¹ 图上的曲面积分，等于该权重对图面积密度的 Lebesgue 积分。
  `B2` 是 `f = 1` 的情形，审计里逐字取回。
  **无可积性、无有限性、无有界性**；参数集只需可测。

### 二、一张图上的局部 coarea 等式

新模块 `formalization/FunctionalInequalities/Analysis/VectorLocalCoarea.lean`
（158 行，本地 import 闭包 20 个模块，**无 WIP**）。三件输入各出自一轮：

* 环境一侧 `setLIntegral_coareaJacobian_levelGraphFamily`（上一轮）；
* 纤维一侧 `setLIntegral_image_vectorGraphMap`（本轮第一部分）；
* 切片描述 `slice_eq_image_vectorGraphMap`（图化那一轮）。

水平变量上的 Tonelli 把三者接起来：

* **`setLIntegral_coarea_levelGraphFamily`**：标量 `setLIntegral_coarea_graph_family` 的余维 m 类比。
* **`exists_vector_coarea_neighborhood`**：**每个微分满射的点都有一个开邻域，
  在它的任意 Borel 子集上、对任意可测 `ℝ≥0∞` 权重，coarea 等式成立**，
  曲面测度取维数 `finrank V - finrank W`（即 `n - m`）。
  邻域与权重无关。这是标量 `KLS.exists_regular_coarea_neighborhood` 的余维 m 类比。

假设只有：`u` 在开集 `O` 上 C¹，且在该点微分满射。`O` 外无正则性要求；
无有限性、有界性、可积性、正则值、SFinite。

## m = 1 退回已证结果

* `codimension_one_graphArea`：从余维 m 的加权公式取回仓库已证的
  `Analysis.setLIntegral_image_graphMap`。
* `codimension_one_coarea_density`：局部 coarea 等式里的环境密度在 `m = 1` 时就是
  `‖gradient u x‖ₑ`（经已证的 `coareaJacobian_fderiv`），即标量 `L9` 的被积函数。

## 本轮没有做的事

**这不是余维 m 的正则 coarea 公式。** 还差两件：

1. **余维 m 的加权切片可测性**：`t ↦ ∫⁻ over S ∩ {u = t}` 的 `AEMeasurable`，
   标量对应物是 `KLS/Geometry/OpenSliceMeasurable.lean`。
   没有它就不能在拼接时把求和与外层积分交换（`lintegral_tsum` 需要可测性）。
2. **可数覆盖 + 不交拼接**：把上面的邻域形式装配成整个正则开集上的等式，
   标量对应物是 `KLS/Geometry/RegularCoarea.lean` 里的装配段。

此外：没有碰临界部分、尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞；
没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
**没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍是 `B1` 与已证伪的 `A0`。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 验证

* 两个新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorLocalCoareaAudit.lean` 的 **15 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；含 `B2` 的取回、全空间、恒为 `∞` 的权重、
  零维参数空间、零维靶空间（此时每点都正则）、以及 m = 1 的两条退回。
* 重跑全部 **37 个审计客户端**（`research/audits` 30 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-local-coarea.json`，最终核对另存
  `build/audit/vector-local-coarea/final-snapshot.json`。
