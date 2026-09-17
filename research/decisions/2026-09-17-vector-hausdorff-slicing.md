# 余维 m 的 Eilenberg 切片不等式

2026-09-17。本轮**证明新定理**：请求的**余维 m Eilenberg 切片不等式**，
以及它的零测切片推论（原始与归一化两种约定）。
**这不是切片可测性，也不是一般的余维 m coarea 公式**——缺口在最后写明。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T172603.078138Z/report.json`：10 个门、212 个本地模块内核重放、
558 条目，快照
`d4d668e06556962f439a2f52fb79f6a0b5cb092481447265e9bd7696ad8cc731`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/VectorHausdorffSlicing.lean`
（357 行，本地 import 闭包 **2** 个模块——它自己与 `KLS/Geometry/SurfaceMeasure.lean`，
**无 WIP**；其余依赖只有 Mathlib）。
它是 `Analysis/HausdorffSlicing.lean` 的余维 m 类比。

* **`exists_measurable_majorant_vector`**：**余维 m 的 Eilenberg 切片不等式**，可测优函形式。
  对在 `S` 上 K-Lipschitz、取值在 m 维内积空间 `W` 的 `u`，
  切片函数 `t ↦ μH[d] (S ∩ {u = t})` 被某个**可测**的 `F` 控制，且
  `∫⁻ F ≤ volume (closedBall 0 1) · K^m · μH[d+m] S`。
  优函的可测性是结论的一部分，而不是对切片函数的假设——切片函数在此阶段并不知道可测。
* **`exists_levelBall`**：证明里余维唯一进入的地方。
  实值情形每个覆盖片的像落在长度 `2K·diam` 的**区间**里；
  余维 m 落在半径 `K·diam` 的**球**里，其体积是 `volume(closedBall 0 1)·(K·diam)^m`，
  这就是 `m` 次幂的来源。
* **`ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`**：零测切片——
  `μH[d+m]`-零测集在几乎每个水平上有 `μH[d]`-零测切片。
* **`hausdorffNormalized_eq_zero_iff`、`ae_hausdorffNormalized_inter_levelSet_eq_zero_vector`**：
  归一化约定下的同一结论，即 coarea 层实际消费的形式。

**论证是覆盖论证，不是 Rademacher**：几乎处处可微对单个水平集什么也不说。
每个尺度用 `μH[d+m]` 的下确界公式取近最优覆盖，用 Lipschitz 性把每片的像装进球，
把含 `t` 的那些片的贡献求和得到该尺度的可测优函，
`Measure.hausdorffMeasure_le_liminf_tsum` 给逐点界，Fatou 收尾。

退化数据都由分支处理而非排除：`K = 0` 且 `m ≥ 1` 时 `u` 在 `S` 上是常数、界为 `0`；
`K^m ≠ 0` 且覆盖代价无穷时界为 `∞`；**零维靶空间也在语句之内**，
此时 `K^m = 1`、每个球都是全空间，不等式退化成 `μH[d] S · volume univ ≤ volume univ · μH[d] S`。
`S` 不要求可测、有界或非空，`u` 不要求整体 Lipschitz、可微或可测，`d = 0` 允许，
零直径与空覆盖片无害。

## m = 1 逐字退回已证的标量界，**常数也一样**

实轴上 `volume (closedBall 0 1) = 2` 且 `K^1 = K`，
所以余维 m 的常数 `volume(closedBall 0 1)·K^m` **恰好是**标量的 `2K`。
审计客户端的 `codimension_one_majorant` 逐字重写
`Analysis.exists_measurable_majorant` 的语句并从余维 m 的定理兑现它。

## 本轮没有做的事

**这不是切片可测性。** 从 Eilenberg 不等式到「无正则性假设的加权切片可测性」的链条
**没有走完**：还需要余维 m 的**紧切片可测性**，即
`Analysis.measurable_hausdorffMeasure_inter_levelSet` 的类比，
而后者是对**实值**函数叙述的，本轮**没有**推广它。

因此：
* coarea 层的余维 m 切片可测性**仍然带着正则性假设**（上一轮经图路线得到的那个）；
* **临界集仍未处理**；
* **一般的余维 m coarea 公式仍然开放**。

此外：没有碰尖锐有限正则 Sard、两条 Cheeger 比较、Energy 的五个洞；
没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论；
没有修改 `Analysis/HausdorffSlicing.lean`——它保持原样，余维 m 版本是**并列的新模块**。
**没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍是 `B1` 与已证伪的 `A0`。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 剩余工作

1. **余维 m 的紧切片可测性**：把 `Analysis/HausdorffContent.lean` 的尺度化开覆盖代价
   与其对水平的上半连续性推广到向量值 `u`（`isOpen_setOf_slice_subset` 是关键，
   它是纯拓扑陈述，应当可以逐字推广）；
2. 用它与本轮的零测切片，照 `KLS/Geometry/SurfaceSlicing.lean` 做
   紧穷竭 + 单调简单函数，得到**不带正则性假设**的加权切片可测性；
3. 再照 `KLS/Geometry/OpenSliceMeasurable.lean` 局部化到开 C¹ 域；
4. 之后才谈得上临界集与一般的余维 m coarea 公式（还需要余维 m 的 Sard 或临界切片）。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorHausdorffSlicingAudit.lean` 的 **15 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；含 `K = 0`、`d = 0`、零维靶空间、
  零测切片，以及 m = 1 连常数一起退回标量界
  （最后一条报告是仓库已证的标量 Eilenberg 界本身，供对照）。
* 重跑全部 **39 个审计客户端**（`research/audits` 32 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-hausdorff-slicing.json`，最终核对另存
  `build/audit/vector-hausdorff-slicing/final-snapshot.json`。
