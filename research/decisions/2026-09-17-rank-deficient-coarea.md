# R8、R0、R9 证出：秩亏临界集与余维 m coarea 公式

2026-09-17。本轮**证明新定理**：秩亏路线的 **`R8`**（局部补整体）、**`R0`**（目标本身）
与 **`R9`**（无临界集假设的余维 m coarea 公式）。
连同 `R1`–`R7`，十三条编号里已兑现 **十条**。

**余维 m coarea 纲领的秩亏缺口就此关闭：`C¹` 映射的一般余维 m coarea 公式已证。**

**这不是任何 Sard 定理**：对临界**值**集合的测度什么也没断言。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；起点 passed 回执
`build/verification/20260917T074617.481735Z/report.json`：10 个门、221 个本地模块内核重放、
599 条目，快照
`3ae6039e5db626e1937bb51bcf07cefc99e07e399abb199b8136007b30fbf279`。
起点工作区 drift 为空。本轮并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/RankDeficientCoarea.lean`
（204 行，本地 import 闭包 35 个模块、无 WIP）。

* **`ae_hausdorffMeasure_inter_levelSet_eq_zero_of_local`（`R8`）**：
  局部零测切片补成整体。`V` 第二可数，邻域族有可数子覆盖，几乎处处量词经得住可数交。
  **不用 `u` 的正则性，也不用 `A` 可测。**
* **`ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero`**：由 `R7` + `R8` 得每一层的整体零测性。
* **`ae_hausdorffMeasure_critical_inter_levelSet_eq_zero`（`R0`，路线的目标）**：
  `C¹` 映射的**整个**临界集 `{x | fderiv ℝ u x 不满射}` 在几乎每个水平上 `ℋ^k` 零测。
  由各层结论对 `r < m` 求有限并（`R1` 的分解式）得到。
  **不需要余维为正**：零维靶空间时每个线性映射都满射，临界集为空，命题空洞成立而非为假。
* **`coarea_of_contDiff`（`R9`）**：余维 m coarea 公式，**对临界集没有任何假设**。
  `VectorCriticalSlice.lean` 此前是在「微分不满射处导数即为零」下证的——`m ≥ 2` 时那是真限制，
  它自己的审计用平面上的秩一投影给出了反例；`R0` 把这个假设整个去掉。
  无有限性、有界性、可积性或正则值假设，`S` 任意 Borel、`g` 任意可测 `ℝ≥0∞` 权，
  也不需要余维为正。

## 路线是怎么走通的（一段话）

`R1` 把临界集按微分的**确切秩**分成有限个可测层。
层上：`R2` 说微分沿正则分量 `P ∘ u` 的纤维方向死掉，`R3` 用邻域一致的右逆界把它定量化，
`R4` 把两者合成纤维方向上正比于 `ε` 的 Lipschitz 常数。
`R7` 对 `u` **本身**跑逼近分片，并在**纤维内部**用 Eilenberg 界——
那里 `k + (m − r) = n − r` 恰好是对的指数——再沿纤维参数对**已证的**正则 coarea 公式积分；
这给出该层在其每个点附近的零测性。
`R8` 用第二可数把这些邻域补起来，对 `r < m` 求有限并得 `R0`，
临界部分在 coarea 等式两侧同时消失，得 `R9`。

**错误指数是在纤维里修好的**：同一个 Eilenberg 界用在环境空间会被逼到指数 `k + r`；
硬压回 `k` 则右端是正 Lebesgue 测度集合的 `μH[n−r] = ∞`（这正是路线诊断 `N2`）。

## 明确没证什么

* **没有证明任何 Sard 定理。** `R0` 说的是临界集**在一个水平之内**的测度；
  对临界**值**集合的测度什么也没断言，仅仅 `C¹` 的映射其临界值集合完全可以有正测度。
  尖锐有限正则 Sard 仍是直接洞，未触碰。
* **`R10`**（同维退化情形，便宜的旁证）仍未证；
  **`N1`、`N2`** 是障碍的诊断语句、不是步骤，也仍未证。
* 映射假设是 `C¹`，**不是** Lipschitz；纤维测度是余维的**归一化** Hausdorff 测度，
  沿用仓库既有约定。
* 没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* 没有修改 `FunctionalInequalities.lean`，也没有修改任何既有 `.lean`。
* **没有提交、没有推送**，真实 Git index 未改动。

## 关于 `RankDeficientRouteStatements.lean`

该文件**保持原字节**。它头部的状态说明（由合作者在 `e7c4403` 里加入）现在已过时——
上面写着 `R0`、`R4`–`R10` 仍开，而实际上 `R4`–`R9` 与 `R0` 都已证。
本轮**没有去改它**：它是已提交的历史路线快照，且合作者此前已对它行使过编辑；
按仓库约定，「义务已兑现」由审计客户端**逐字复制并证明**其命题来记录，
`research/audits/RankDeficientCoareaAudit.lean` 的 `route_R8`、`route_R0`、`route_R9` 即是。
如需刷新该文件的状态说明，留给文件的当前维护者。

## m = 1 退回已证的标量情形

审计的 `scalar_L10` 与 `scalar_L11` 从余维 m 版本取回
`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` 与 `KLS.coarea_of_contDiff`，
两者都多要一个 `1 ≤ finrank V`——与前几轮同样的**如实记下的差别**。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/RankDeficientCoareaAudit.lean` 的 **14 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`，其中 `route_R8`、`route_R0`、`route_R9`
  是 `RankDeficientRouteStatements.lean` 的命题**逐字复制并证明**。
* 重跑全部 **49 个既有审计客户端**加新客户端共 **50 个**，全部严格通过，0 失败；
  公理报告 648 条，其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-rank-deficient-coarea.json`，
  最终核对另存 `build/audit/rank-deficient-coarea/final-snapshot.json`。
