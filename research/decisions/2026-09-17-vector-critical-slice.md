# 余维 m 的临界切片：导数为零的那一部分

2026-09-17。本轮**证明新定理**：余维 m 情形下**导数为零**那部分临界集的切片零测性，
以及由它把正则情形的 coarea 公式延拓到全空间的结果
（假设「微分不满射处导数即为零」）。
**这不是完整的临界集**（`m ≥ 2` 时严格更小），**也不是任何 Sard 定理**；
差距不是断言而是**给出反例**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260917T034956.058840Z/report.json`：10 个门、214 个本地模块内核重放、
566 条目，快照
`e87a9add07bbc20692efd7891719dcf6b8cdf6d1bf027fe3f36fd05b7f90b019`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/VectorCriticalSlice.lean`
（275 行，本地 import 闭包 28 个模块，**无 WIP**）。

* **`exists_lipschitzOnWith_zeroDeriv_cover`**：Mathlib 的逼近分片把
  `{x | fderiv ℝ u x = 0}` 覆盖成可数个两两不交的可测片，`u` 在每片上 `ε`-Lipschitz。
  逼近用的线性映射是导数的取值，在该集合上为零，所以线性部分脱落，逼近变成真正的 Lipschitz 估计。
  **这一步正是对仅仅秩亏的导数失效的地方。**
* **`ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`**（及归一化版本）：
  `m ≥ 1` 时，**几乎每个水平与 `{Du = 0}` 的交是 `ℋ^{n−m}` 零测的**。
  论证与标量一字不差，只是换用上两轮的余维 m Eilenberg 界，常数变成
  `volume (closedBall 0 1) · ε^m`，而 `ε^m → 0` 正因为 `m ≥ 1`。
  `0 < finrank W` 是真假设：靶空间为零维时每个导数都为零、该集合是全空间。
* **`coarea_of_contDiff_of_critical_eq_zeroDeriv`**：
  在**「微分不满射处导数即为零」**的假设下，把已证的正则情形 coarea 公式延拓到全空间——
  可测性来自上一轮**不带正则性**的切片可测性，临界部分的贡献两侧都为零。

## m = 1 逐字退回已证的标量 L10 与 L11

`m = 1` 时「不满射」与「为零」对实值微分是同一件事，所以上面的假设**自动成立**。审计里：
* `scalar_L10` 逐字取回 `KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero`；
* `scalar_L11` 逐字取回 `KLS.coarea_of_contDiff`。

两者都多要一个 `1 ≤ finrank V`——与前两轮同样的**如实记下的差别**：
余维 m 的陈述带假设「纤维维数 + 余维 = 环境维数」。

## 差距是给出的，不是断言的

`m ≥ 2` 时 coarea 的临界集是 `{x | fderiv ℝ u x 不满射}`，**严格大于**导数为零的集合。
审计的 `rank_deficient_witness` 给出反例：平面上秩一的线性映射
（沿第一坐标轴的正交投影），其导数**处处非零**且**处处不满射**——
于是导数为零的集合是空集，而 coarea 的临界集是全空间，
`coarea_of_contDiff_of_critical_eq_zeroDeriv` 的假设在每一点都不成立。

**本轮对秩亏部分什么也没证。** 那部分需要沿存活方向的迭代切片，
与本轮用的「小 Lipschitz 常数」技巧是两回事——后者严格依赖导数为零。

## 本轮没有做的事

* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言，
  仅仅 C¹ 的映射其临界值集合完全可以有正测度。
* **没有证明一般的余维 m coarea 公式**：秩亏部分未覆盖。
* 没有修改 `KLS/Geometry/CriticalSlice.lean` 或 `KLS/Geometry/SmoothCoarea.lean`——
  余维 m 版本是并列的新模块。
* 没有碰尖锐有限正则 Sard、两条 Cheeger 比较、Energy 的五个洞；
  没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍是 `B1` 与已证伪的 `A0`。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 剩余工作

**秩亏部分**是余维 m coarea 仅存的结构性缺口。可能的路线：
按秩分层 `{rank Du ≤ r}`，在每层上用逼近分片把 `u` 的像挤进一个 `r` 维仿射子空间附近，
再沿存活的 `m − r` 个方向用 Eilenberg 界——但需要同时沿 `r` 个「好」方向切片，
即迭代切片；这正是 Federer coarea 公式退化部分的难点，
仓库与 Mathlib 目前都没有相应工具。若要立项，建议先做一轮路线探查。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorCriticalSliceAudit.lean` 的 **17 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；含常值映射（整体临界）、零维靶空间下导数恒零、
  秩亏反例，以及 m = 1 逐字退回 `L10` 与 `L11`
  （最后两条报告是仓库已证的标量 `L10`、`L11` 本身，供对照）。
* 重跑全部 **41 个审计客户端**（`research/audits` 34 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-critical-slice.json`，最终核对另存
  `build/audit/vector-critical-slice/final-snapshot.json`。
