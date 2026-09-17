# 余维 m 的紧切片可测性，与不带正则性的加权切片可测性

2026-09-17。本轮**证明新定理**：请求的**余维 m 紧切片可测性**，
并把上一轮的 Eilenberg 不等式接上去，得到**不带任何正则性假设的加权切片可测性**
（Borel 集形式与开 C¹ 域形式）。
**这不是 coarea 公式**——去掉的是**可测性**那一半的正则性假设，不是 coarea **等式**的。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T180259.203752Z/report.json`：10 个门、213 个本地模块内核重放、
562 条目，快照
`cfc6a0899b7ac59cf4524e972a36aa6a71d8ec4f4449b100d7ce0fd6122ffab1`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 只有一半需要重做

`Analysis/HausdorffContent.lean` 里有两件事：尺度化**开**覆盖代价的尺度极限是 `μH[d]`，
以及固定尺度上紧集切片的开覆盖代价对**实**水平上半连续。
**前者只关乎环境空间，与靶空间无关，本轮原样复用**；只有后者提到靶空间，本轮对度量靶空间重做。
论证一字未改：含有某一切片的开集也含有邻近的一切片，
因为落在开集外的紧余部使映射与该水平保持正距离——
实值情形那个距离是 `|u x − t|`，余维 m 是 `dist (u x) t`，其余完全相同。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/VectorSliceMeasurable.lean`
（294 行，本地 import 闭包 13 个模块，**无 WIP**）。

* **`isOpen_setOf_slice_subset_vector`、`upperSemicontinuous_openCoverCost_slice_vector`**：
  上面那步，对任意度量靶空间。
* **`measurable_hausdorffMeasure_inter_levelSet_vector`**：**余维 m 的紧切片可测性**——
  `S` 紧、`u` 连续取值于度量空间时，`t ↦ μH[d] (S ∩ {u = t})` 是 Borel 可测的。
  不要求 `u` Lipschitz，不要求 `S` 在任何维数下测度有限，`d = 0` 允许。
* **`measurable_hausdorffNormalized_inter_levelSet_vector`**：归一化约定下的同一结论。
* **`aemeasurable_hausdorffNormalized_inter_levelSet_vector`**：Borel 集形式。
  照 `KLS/Geometry/SurfaceSlicing.lean` 的结构：内正则性把 Borel 集用紧集穷竭到只差一个
  Lebesgue 零测余部，紧片用上半连续处理，余部用上一轮的 **Eilenberg 零测切片**处理。
  两个原料都必需，单独任何一个都不够。
* **`aemeasurable_setLIntegral_inter_levelSet_vector`**：加权形式，经单调简单函数。
  权重任意可测 `ℝ≥0∞`，可无界、可恒为 `∞`。
* **`aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector`**：
  局部化到**只在开集上 C¹** 的映射与其任意可测子集，
  标量对应物是 `KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`。

**全部不需要微分满射。** 与 `Analysis/VectorRegularCoarea.lean` 的图路线不同，
这些陈述**覆盖定义域的临界部分**——审计里用常值映射（法方向为正维时微分处处不满射）做了见证。

假设只有：`u` 在集合上 Lipschitz（或在开集上 C¹）、集合可测、纤维维数与余维相加等于环境维数。

## m = 1 退回已证的标量结果，并如实记下一处差别

* `scalar_compact_slices`：逐字取回 `Analysis.measurable_hausdorffMeasure_inter_levelSet`。
* `scalar_open_slices`：逐字取回 `KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`，
  **但多要一个 `1 ≤ finrank V`**。这是**如实记下的差别**：
  余维 m 的陈述带假设 `k + finrank W = finrank V`，
  所以零维环境空间（标量陈述也覆盖，靠自然减法与子单点分支）落在其射程之外。

## 本轮没有做的事

* **没有证明任何 coarea 公式。** 去掉的是**可测性**那一半的正则性假设；
  coarea **等式**仍然只在微分满射处成立。
* 临界部分的 coarea 等式需要余维 m 的 **Sard 或临界切片**论证，**没有证**。
* 没有修改 `Analysis/HausdorffContent.lean`、`Analysis/HausdorffSlicing.lean`、
  `KLS/Geometry/SurfaceSlicing.lean` 或 `KLS/Geometry/OpenSliceMeasurable.lean`——
  余维 m 版本是并列的新模块。
* 没有碰尖锐有限正则 Sard、两条 Cheeger 比较、Energy 的五个洞；
  没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍是 `B1` 与已证伪的 `A0`。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 剩余工作

1. **余维 m 的 Sard 或临界切片**：临界集上的 coarea 贡献为零，
   标量对应物在仓库里是 `Analysis/Sard.lean` 一线与临界切片零测；
2. 把它与本轮的可测性、上一轮的正则等式合并，得到**一般的余维 m coarea 公式**
   （标量 `L11`–`L13` 的类比）。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorSliceMeasurableAudit.lean` 的 **18 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；含常值映射（临界情形）、恒为 `∞` 的权重、
  零维靶空间，以及 m = 1 的两条退回
  （最后两条报告是仓库已证的两个标量陈述本身，供对照）。
* 重跑全部 **40 个审计客户端**（`research/audits` 33 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-slice-measurable.json`，最终核对另存
  `build/audit/vector-slice-measurable/final-snapshot.json`。
