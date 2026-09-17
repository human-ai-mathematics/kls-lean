# N1 证出：小 Lipschitz 方法实际给出的指数

2026-09-17（同日，在 `2026-09-17-equidimensional-sard.md` 那一轮之后）。
本轮**证明新定理**：秩亏路线的诊断项 **`N1`**。
连同 `R0`–`R10`，十三条编号里已兑现 **十二条**；
剩下的 `N2` 已在上一轮**证明为假**，其修正版已证。

**`N1` 是诊断，不是纲领的进展。** 它证出的恰恰是「这条路走不通」的那个陈述：
指数是 `k + r` 而不是 `k`。见下「为什么证出 N1 不是进展」。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；
上一轮收尾 passed 回执 `build/verification/20260917T084846.473181Z/report.json`：
10 个门、223 个本地模块内核重放、608 条目，快照
`bbc6729f41d7c11b2ef7b9a3c919b5f40ad495a2edf549280f42183dfcd6125b`，drift 为空。
本轮期间并发会话（王浩丞那条线）**未改动工作区，也未提交**。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard（直接洞 `Analysis.sard`）、Energy 的五个洞、无量纲 KLS
也都未触碰。**本轮与 Sard 无关**：`N1` 只谈某个映射的纤维的 Hausdorff 测度，
对临界值集合一字未提。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/ExponentObstruction.lean`
（179 行，本地 import 闭包 2 个模块、无 WIP，无 `sorry`、无 `axiom`）。

* **`hausdorffMeasure_truncated_add_le`**：`μH[((n − m : ℕ) : ℝ) + m] S ≤ μH[n] S`。
  `ℕ` 的截断减法满足 `(n − m) + m ≥ n`（无论 `m ≤ n` 与否），Hausdorff 测度对指数递减。
  这一条使整个证明**不需要** `finrank ℝ W₂ ≤ finrank ℝ V`——
  正是 `N2` 栽在截断减法上的那一点，`N1` 挺住了。
* **`exists_measurable_majorant_of_lipschitz_pieces`**（单个尺度）：
  给定 `S` 的可数可测分片、每片上 `Q ∘ u` 为 `ε`-Lipschitz，
  对每片用已证的余维 `m₂` Eilenberg 优函数 `exists_measurable_majorant_vector`，
  把优函数求和。得到一个**可测**优函数 `G ≥ τ ↦ μH[n − m₂](S ∩ {Q∘u = τ})`，
  且 `∫⁻ G ≤ C · ε^{m₂} · μH[n] S`。
  切片函数本身不可测（`u` 没有任何正则性假设），所以必须走优函数。
  分片的**可测性与不交性**在这里唯一一次被用到：可数可加性把
  `∑ᵢ μH[n−m₂+m₂](S ∩ Tᵢ)` 合成 `μH[n−m₂+m₂](S)`。
* **`ae_hausdorffMeasure_inter_levelSet_eq_zero_of_lipschitz_pieces`（`N1`）**：
  对 `ε_j = (j+1)⁻¹` 取优函数 `G_j`，取逐点下确界 `H = ⨅ⱼ Gⱼ`（可测、仍是优函数），
  则 `∫⁻ H ≤ C · ε_j^{m₂} · μH[n] S` 对每个 `j` 成立；
  `m₂ > 0` 且 `μH[n] S < ∞` 使右端趋于 `0`，故 `∫⁻ H = 0`，
  `H` 可测故几乎处处为零，切片被它控制，于是几乎每个 `τ` 上切片零测。

审计 `research/audits/ExponentObstructionAudit.lean`（244 行，闭包 5 个模块、无 WIP）
现有 **11 条标准三公理报告**，其中 `route_N1` 是路线命题的**逐字复制并证明**
（脚本核对，去空白后与路线文件逐字相同）。

## 为什么证出 `N1` 不是进展

路线记录早就把 `N1` 定性为**障碍的陈述**，本轮只是把它兑现成定理，不改变这个定性。

* **指数是 `k + r`，不是 `k`。** 路线里 `W₂` 是秩 `r` 的像的正交补，`dim W₂ = m − r`，
  于是 `N1` 给出的指数 `n − dim W₂ = k + r`。
  审计的 `N1_exponent_is_k_add_r` 把这条算术单列出来，免得被误读。
* **弱在没用的方向上。** `r ≥ 1` 时，`μH[k+r]` 零测**推不出** `μH[k]` 的任何信息：
  在指数 `k = n − r` 上，任何正 Lebesgue 测度集合的 Hausdorff 测度都是 `∞`
  （`N1_null_at_higher_exponent_says_nothing_at_k`，即上一轮证出的修正版 `N2` 的特例）。
* **`R0` 不依赖它。** `R0` 已由分层路线独立证出，办法是改在**纤维内部**切片
  （`Analysis/StratumSlicing.lean`），那里 `k + (m − r) = n − r` 才是对的指数。
  `Analysis/ExponentObstruction.lean` 没有任何下游消费者。

## 侧条件是必需的

`0 < finrank ℝ W₂` 不是装饰。审计的 `N1_needs_positive_codimension`
否定的是**删掉这条假设之后**的 `N1`（`Type` 实例；路线的 `Type*` 版蕴含它），
反例为 `V = W = ℝ`、`W₂` 零维、`Q = 0`、`u = id`、`S = [0,1]`：
分片假设平凡成立（`Q ∘ u` 是常值），而唯一的纤维就是整个 `S`，`μH[1] S = 1 ≠ 0`。
零维时 Eilenberg 常数 `ε^{dim W₂} = 1`，没有东西趋于零。

`S` 可测这一条也是真用到的，见上。

## 明确没证什么

* **没有证明任何 Sard 定理**，与 `Analysis.sard` 这个直接洞无关，其状态未变。
* **`N2` 仍未证，且已知为假**；已证的是它的修正版（上一轮）。
* 不迁洞、不新增证书、不扩大 Blueprint `leanok` 范围、不新增兼容 alias、
  不削弱已证结论、不增加不必要的假设。无量纲 KLS 仍开。
* 未修改任何既有 `.lean` 文件（本轮只新增一个模块，并扩写**本轮自己**上一步新建的
  `ExponentObstructionAudit.lean`）；路线语句文件 `RankDeficientRouteStatements.lean`
  仍**字节不变**。

## 验证

* 新模块与审计客户端均以 `-DwarningAsError=true` 通过。
* 重跑 **52 个**审计客户端（`research/audits` 45 个、`build/audit` 7 个），
  全部严格通过，**0 失败**。
* 全库公理报告 **672 条**（上一轮 665 + 本轮 7），其中 **12 条 `sorryAx` 未变**，
  仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；
  证据 JSON 为 `research/explorations/2026-09-17-exponent-obstruction-n1.json`，
  本地日志在 `build/audit/exponent-obstruction-n1/`，
  最终核对另存 `build/audit/exponent-obstruction-n1/final-snapshot.json`。
* **没有提交、没有推送**，真实 Git index 未改动。

---

## 附记（2026-09-17，同日稍后补记，正文未改写）

同日的文件管理一轮把上文提到的两处位置/名字做了调整，**数学内容与类型一字未改**：

* 修正版 `N2` 从审计客户端挪进模块，现为
  `Analysis.hausdorffMeasure_finrank_sub_eq_top`（`Analysis/ExponentObstruction.lean`），
  原名 `ExponentObstructionAudit.hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos`。
  模块因此新增 `import Analysis.LevelSet`，本地 import 闭包由 2 变 **4**，仍无 WIP。
  审计只留路线记账项 `N2_repair_is_free_on_the_route` 与反例 `route_N2_is_false`。
* `ExponentObstructionAudit` 原先把零维空间声明了**两次**（`Pt₀` 与 `Pt`），已并为一个 `Pt`；
  客户端重排为 `N1` 全部在前、`N2` 全部在后。

上文其余记载不变：`N1` 仍是已证的诊断项，指数仍是 `k + r` 而非 `k`，
证出它仍**不是纲领的进展**；`N2` 仍未证且已知为假；`Analysis.sard` 仍是直接洞。
