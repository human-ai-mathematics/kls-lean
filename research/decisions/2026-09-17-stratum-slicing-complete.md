# R7 证出：逐层局部切片

2026-09-17。本轮**证明新定理**：秩亏路线的 **`R7`**——逐层局部切片。
连同 `R1`–`R6`，十三条编号里已兑现 **七条**。
**`R0` 仍然开着**：它还需要 `R8`（把 `R7` 从一个邻域补到整层）与对 `r < m` 的有限并。
本轮**没有在新情形下证明任何 coarea 公式、没有证明关于完整临界集的切片定理、没有证明任何 Sard 定理**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；起点 passed 回执
`build/verification/20260917T072259.478204Z/report.json`：10 个门、221 个本地模块内核重放、
597 条目，快照
`05569e6d2c0537b968c5a57d17df14c5e3aee6a49541e5713afcabc3608be01f`。
起点工作区 drift 为空。本轮并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

在 `formalization/FunctionalInequalities/Analysis/StratumSlicing.lean`（489 行，
本地 import 闭包 34 个模块、无 WIP）上继续，新增：

* **`lintegral_hausdorffMeasure_stratum_le`（`R7b`，逐尺度估计）**：
  对每个 `ε ≠ 0`，
  `∫⁻_W μH[k](Σ_r ∩ U ∩ u⁻¹(t)) dt ≤ Cst · (c ε)^{m−r} · ∫⁻_{Σ_r ∩ U} coareaJacobian(D(P∘u))`，
  **`Cst` 与 `ε` 无关**。
  证明就是上一轮写下的路线：对 `u` **本身**跑一次 Mathlib 的逼近分片（一套分片同时供两个分量）；
  每片上由局部包得到 `Q ∘ u` 沿纤维的 `c ε`-Lipschitz；
  在**纤维内部**用 `VectorHausdorffSlicing.lean` 的 Eilenberg 界，
  取指数 `k`、靶维 `m − r`，此时 `k + (m − r) = n − r` 恰好；
  沿纤维参数积分时用**已证的**正则 coarea 公式（权 `1`）把纤维测度换成 coareaJacobian 的普通积分；
  最后用 `lintegral_split_target` 读成靶空间上的积分。
* **`exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero`（`R7`）**：
  `ε → 0`。右端因子有限（邻域闭包紧、被积函数连续有界），
  指数 `m − r` 为正恰因 `r < m`，故靶空间上的积分为零，被积函数几乎处处为零。
* 配套的 `hausdorffMeasure_eq_inv_mul_normalized`（原始与归一化 Hausdorff 测度的互换）
  与 `finrank_tangentRange_eq_of_mem`。

## 错误指数是在哪里被修好的

一步法在环境空间里用 Eilenberg 界会被逼到指数 `k + r`；硬压回 `k` 则右端是
正 Lebesgue 测度集合的 `μH[n−r]`，即 `∞`（这正是 `N2`）。
**在纤维内部**同一个界用在指数 `k` 上，右端换成纤维自身有限的 `ℋ^{n−r}` 测度——量纲就对上了。
这也是 `R5`（纤维有限性）与 `R6`（靶空间分解）两条义务的用武之地：
本轮实际用到的是同样的两台引擎（已证的正则 coarea 公式、保测换元加 Tonelli），
以积分形式而不是零测集形式出现。

## 本轮改了两个既有 `.lean`——如实记下

两处都在本会话自己的、尚未提交的文件里，且都**只增不减**：

* `Analysis/StratumSlicing.lean`：新增上面三条定理，并**重写模块文档串**——
  它此前写着「`R7` 未证」，现在已不成立，必须改。原有的
  `exists_stratum_local_data` 与 `lintegral_split_target` **语句一字未动**。
* `research/audits/StratumSlicingRouteStatements.lean`：在文件头加一段状态说明
  （`R7b`、`R7c` 现已证，`R0` 仍开），**两条 `#check` 命题一字未动**。
  这与合作者此前对 `RankDeficientRouteStatements.lean` 的做法一致。

`research/audits/RankDeficientRouteStatements.lean` 与 `AreaFormulaRouteStatements.lean`
**未被本轮改动**。

## 本轮没有做的事

* **没有证明 `R0`**。`R7` 是关于**一个秩层、一个邻域**的陈述；
  要到 `R0` 还差 `R8`（第二可数 ⟹ 可数子覆盖，把局部补成整层）
  与对 `r < m` 各层的有限并（`R1` 的分解式已备好）。
* 没有证明 `R8`、`R9`、`R10`、`N1`、`N2`。
* **没有在新情形下证明任何 coarea 公式**；已证公式的适用范围没有扩大一分。
* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言。
* 没有修改 `FunctionalInequalities.lean`；没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；
  没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一步

**`R8`**（局部补整体，估计 90 行、低到中风险），然后 `R0` 就是
`R1` 的有限并加 `R8`；再往后是 `R9`（无二分假设的余维 m coarea 公式）。

## 验证

* 模块与两个客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/StratumSlicingAudit.lean` 的 **16 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`，其中 `route_R7` 是
  `RankDeficientRouteStatements.lean` 的 `R7` 命题**逐字复制并证明**。
* 重跑全部 **49 个审计客户端**，全部严格通过，0 失败；公理报告 634 条，
  其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-stratum-slicing-complete.json`，
  最终核对另存 `build/audit/stratum-slicing-complete/final-snapshot.json`。
