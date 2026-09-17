# 逐层局部切片 R7：局部包与靶空间分解已证，**R7 本身未证**

2026-09-17。本轮的目标是 `R7`。**`R7` 没有证出来**，`R0` 也依然开着。
本轮证出的是 `R7` 的两个部件：**局部包**（把已证的 `R2`、`R3`、`R4` 装配成一个带**统一常数**的邻域）
与**靶空间分解的积分形式**（换元 + Tonelli）。剩下的缺口**精确写成 `R7b`、`R7c`**，
只含 `#check`，一条未证。
本轮**没有证明任何 coarea 公式、任何关于临界集的切片定理、任何 Sard 定理**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；起点 passed 回执
`build/verification/20260917T065323.126590Z/report.json`：10 个门、220 个本地模块内核重放、
592 条目，快照
`b9df57d18dfff53fae863419fc7ad261a19b37889026c1d14a1cc8c57969f03a`。
起点工作区 drift 为空。本轮并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 本轮修改了一个既有 `.lean`——如实记下

`formalization/FunctionalInequalities/Analysis/TangentialLipschitz.lean`（上一 `R4` 轮的模块，
尚未提交）被改为**先给出显式常数**的形式
`lipschitzOnWith_of_ker_bound`，原来的存在形式 `exists_lipschitzOnWith_of_ker_bound`
（即路线的 `R4` 语句）**原样保留**并由显式形式直接导出。
这是**严格加强**，没有削弱任何已证结论，也没有改动 `R4` 的路线语句。

原因是硬性的：装配需要**同一个常数**在逼近分片的所有片上成立，
而存在形式的常数依赖于每片的线性模型 `fderiv ℝ u y`，取不出统一界。
这也是上一轮把 `R3` 的**邻域一致版**列为硬需求的理由在此兑现的地方。

## 证了什么

新模块 `formalization/FunctionalInequalities/Analysis/StratumSlicing.lean`
（209 行，本地 import 闭包 25 个模块、无 WIP）。

* **`exists_stratum_local_data`（局部包）**：设 `x₀` 在秩 `r` 层上，
  `K = range (Du x₀)`，`P`、`Q` 分别是到 `K`、`Kᗮ` 的正交投影。则存在
  `x₀` 的开邻域 `U`（闭包紧）与**一个**常数 `c`，使得
  * 在 `closure U` 上 `P ∘ u` 处处正则（`coareaJacobian ≠ 0`）；
  * 对层上落在 `U` 里的**每一个** `y`、**每一个** `ε`、**每一个**被 `fderiv ℝ u y`
    以 `ε` 逼近的集合 `S`、**每一条**纤维 `s`，
    `Q ∘ u` 在 `S ∩ {P ∘ u = s}` 上是 `c ε`-Lipschitz 的。

  **`c` 对 `y` 的一致性是全部难点**：逼近分片在每片上给出不同的线性模型，
  而 `R4` 的常数通过 `‖fderiv ℝ u y‖` 与右逆界依赖于该模型。
  统一常数由 `R2`（核引理）、`R3` 的**邻域一致版**、以及 `‖fderiv ℝ u‖` 在点附近的界给出。

* **`lintegral_split_target`（靶空间分解的积分形式）**：
  靶空间上的积分等于沿正交分解的累次积分。这是 `R6` 对零测集所做的事的**积分版本**，
  也是逐尺度估计最终要被积分到的形状。用 Mathlib 的
  `LinearIsometryEquiv.measurePreserving`、`WithLp.volume_preserving_toLp` 与 Tonelli，
  只要求被积函数几乎处处可测。

* 配套的 `fderiv_clm_comp`（连续线性后复合的链式法则）、`surjective_proj_comp`
  （基点处正则分量确实是淹没）、`finrank_tangentRange_eq`（层上维数相等）。

## 没证什么——`R7` 本身

**`R7` 未证。** 缺的是两步，精确写在只含 `#check` 的
`research/audits/StratumSlicingRouteStatements.lean` 里，**一条未证**：

* **`R7b`（逐尺度估计）**：在固定尺度 `ε` 上，层片在整个靶空间上的纤维测度总量
  被 `ε^{m−r}` 乘以正则分量 coareaJacobian 的积分控制，常数与 `ε` 无关。
  要走的路是：对 `u` **本身**做一次逼近分片（一套分片同时供两个分量使用）；
  在每片上用局部包得到纤维方向的 `c ε`-Lipschitz；在**纤维内部**用
  `Analysis/VectorHausdorffSlicing.lean` 的 Eilenberg 界，取指数 `k`、靶维数 `m − r`，
  此时 `k + (m − r) = n − r` 恰好；再沿纤维参数积分，用**已证的**正则 coarea 公式
  把纤维测度换成 coareaJacobian 的普通积分；最后用 `lintegral_split_target` 读成靶空间上的积分。
* **`R7c`（`ε → 0`）**：这种形状的界在每个尺度上成立、右端有限、指数为正（即 `r < m`），
  就逼出积分为零，进而几乎处处为零。这是仓库里已经用过两次的模式
  （`VectorHausdorffSlicing.lean` 与 `VectorCriticalSlice.lean`）。

在这两条做完之前，**`R7` 开着，`R0` 开着，一般余维 m coarea 公式开着**。

## 本轮还没做的事

* **没有证明 `R0`**；`R8`–`R10`、`N1`、`N2` 也都未证。
* **没有证明任何 coarea 公式**；已证公式的适用范围没有扩大一分。
* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言。
* 除上面记下的 `TangentialLipschitz.lean` 加强外，没有修改任何其他既有 `.lean`
  （`FunctionalInequalities.lean`、`RankDeficientRouteStatements.lean`、
  `AreaFormulaRouteStatements.lean` 均未动）；没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；
  没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 验证

* 新模块与两个新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/StratumSlicingAudit.lean` 的 **11 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`。
  `research/audits/StratumSlicingRouteStatements.lean` 只含 **2 条 `#check`**，无声明。
* 重跑全部 **47 个既有审计客户端**加两个新客户端共 **49 个**，全部严格通过，0 失败；
  公理报告 629 条，其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-stratum-slicing.json`，
  最终核对另存 `build/audit/stratum-slicing/final-snapshot.json`。
