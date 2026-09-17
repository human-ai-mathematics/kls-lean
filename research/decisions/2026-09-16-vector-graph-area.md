# B1 收口：余维 m 的 C¹ 图面积公式

2026-09-16。本轮**证明新定理**，完成义务 **B1** 的第五阶段，
**余维 m 的 C¹ 图面积公式在原始与归一化两种约定下都已证明**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T144943.423764Z/report.json`：10 个门、205 个本地模块内核重放、
533 条目。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮未触碰。

## 精确成果

`Analysis/VectorGraphArea.lean`（本地 import 闭包 10 个模块，**无 WIP**）：

* **`hausdorffMeasure_image_vectorGraphMap`**：
  `μH[k] (graph '' s) = ∫⁻ y in s, ofReal (normDet (graphMapLinear ι κ (Dγ y))) ∂μH[k]`。
* **`hausdorffNormalized_image_vectorGraphMap`**：归一化版本，右端对 **Lebesgue 测度**积分。
  这是余维 m coarea 纲领实际要消费的形式。

`s` 只需可测：**不要求有限测度、有界或单射**——图映射按构造就是单射。

## 一处与余维一不同的真障碍

余维一的证明用到「Jacobian `√(1+‖a‖²)` 对斜率**全局 1-Lipschitz**」，从而导数接近就推出
Jacobian 接近。**余维 m 的 `√det(1+AᵀA)` 不是一致 Lipschitz 的**：在二维参数空间上取
`A = t·id`，它像 `1+t²` 那样增长，导数随 `t` 无界。

所以上一轮的分片不够用。本轮改为让分片**直接控制 Jacobian**
（`exists_approximating_partition_with_jacobian`），由 Jacobian 的连续性（上一轮 A1 的结论
经 `continuous_graphMapLinear_normDet`）提供。此后完全照余维一的结构走，
极限引理 `tendsto_aux`、`tendsto_aux'` 与图无关，**原样复用未重证**。

## 路线语句 B1 的一处错误，必须记下

上一轮路线探查写的 **B1 语句是错的**：它把左边的**原始** `μH[k]` 与右边的 **Lebesgue**
测度配在一起。两者差一个归一化常数——`Analysis.hausdorffMeasure_finrank_eq_smul_volume`
给出 `μH[k] = (2^k/ω_k) • volume`，而 `2^k = ω_k` 只在 `k ≤ 1` 成立（`ω_0=1`、`ω_1=2`）。
**所以该语句在 `k ≥ 2` 时按字面是假的**，本轮证的不是它。

正确的两种配对都已证明并审计：
* `corrected_B1`：原始配原始（`μH` 与 `μH`）；
* `route_B2`：归一化配 Lebesgue——**路线里的 B2 写对了**，逐字兑现。

按不改写历史证据的惯例，`research/audits/AreaFormulaRouteStatements.lean` **保持原字节**，
更正记在本决定与 `research/audits/VectorGraphAreaAudit.lean` 中。

## 这是什么，不是什么

这是**图**的面积公式。**不是** Federer 面积公式 `A0`（任意单射 C¹ 参数化），
后者与 `A2`–`A5` 仍然开放。路线当初推荐图版本，正是因为图映射按构造单射且有显式左逆。

## 本轮没有做的事

* 没有证明 `A0`、`A2`–`A5`；没有证明任何 coarea 公式。
* 没有迁洞；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 纲领现状与下一步

余维 m coarea 纲领已完成：coarea Jacobian、线性面积公式与仿射纤维、任意余维图 Jacobian、
A1、以及 **B1/B2 图面积公式**。下一步是余维 m coarea 的**正则情形**（标量 L9 的类比）：
在 `coareaJacobian ≠ 0` 的开集上用带参数隐函数定理把纤维表示成图族，再用本轮的 B2。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/VectorGraphAreaAudit.lean` 的 10 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`；含全空间（无有限性）与零维参数空间。
* 重跑全部 33 个审计客户端（`research/audits` 26 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-vector-graph-area.json`，最终核对另存
  `build/audit/vector-graph-area/final-snapshot.json`。
