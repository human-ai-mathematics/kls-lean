# R10 证出：同维退化情形；并发现 N2 按字面为假

2026-09-17。本轮**证明新定理**：秩亏路线的 **`R10`**（同维退化情形，`n = m`），
即几乎没有水平是临界值。十三条编号里已兑现 **十一条**。

本轮还发现并在 Lean 里**证明**：路线诊断 **`N2` 按其字面陈述为假**（零维空间上的反例），
并证明了补上 `0 < finrank ℝ V` 之后的修正版。`N1` **仍未证**。

**`R10` 不是任何一般的 Sard 定理，也不是通往 `R0` 的一步。** 见下「明确没证什么」。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；起点 passed 回执
`build/verification/20260917T080255.188361Z/report.json`：10 个门、222 个本地模块内核重放、
603 条目，快照
`bce9cda59abe8b2674cb72ce76c02b4e21d7adf9abcb97361a542a6f21a2e530`。
起点工作区 drift 为空，未提交成果 27 项，全部保留。
本轮期间并发会话（王浩丞那条线）**未改动工作区，也未提交**：收尾时
`HEAD = origin/main` 仍为 `e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`。

## 边界

对数凹 Cheeger–Buser 线——等周常数几种定义的对齐直到与 Poincaré 常数的双向比较，
含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞——归合作者**王浩丞**，本轮未触碰。
尖锐有限正则 Sard（直接洞 `Analysis.sard`）、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/EquidimensionalSard.lean`
（123 行，本地 import 闭包 18 个模块、无 WIP，无 `sorry`、无 `axiom`）。

* **`ContinuousLinearMap.det_eq_zero_of_not_surjective`**：有限维空间的自同态不满射则行列式为零。
  Mathlib 只有反向（`LinearMap.range_lt_top_of_det_eq_zero`）；这一向要经过单射，
  而单射与满射等价只在有限维成立。
* **`measure_image_critical_eq_zero`**：`finrank ℝ V = finrank ℝ W` 时，`C¹` 映射 `u` 的
  临界集的**像**是 Lebesgue 零测集。证法是把 Mathlib 的自映射引理
  `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` 沿本仓库的
  `isometryEquivOfFinrankEq` 搬运：**前**合成逆等距而不是后合成，
  于是像本来就落在 `W` 里，零测集本身不需要再搬一次。
* **`ae_critical_inter_levelSet_eq_empty`（`R10`）**：同维时几乎每个水平**完全避开**临界集。
  纤维维数 `k = 0`，`μH[0]` 零测就是空集，所以 `R0` 的结论在此退化为「切片为空」。

## `R10` 与一般 Sard 的分界（必须读的一节）

`R10` 确实是秩亏纲领十三条里**唯一**一条关于临界**值**的陈述，因此最容易被误读。分界如下。

* **Sard 定理**说的是 `ℝⁿ → ℝᵐ` 的临界值集合零测。这里证的只有 `n = m` 一种情形，
  而且那一情形之所以成立，纯粹是因为奇异线性映射压缩体积——Mathlib 已经有自映射版本。
  `n > m` 时仅 `C¹` 的映射其临界值集合完全可以有正测度（Whitney），下面没有一句话与之相反。
* **直接洞 `FunctionalInequalities.Analysis.sard`**（`KLS/WIP/AnalyticPrerequisites.lean`）
  说的是：实值 `u`、**任意**维数 `n` 的定义域、`C^n` 正则性。
  本轮与它的**全部**重叠是 `finrank ℝ V = 1`（`r10_reaches_only_dimension_one` 记下这一点），
  而那一情形 `Analysis.sard_of_finrank_le_one` 早已无条件证出，用的还是同一条 Mathlib 引理。
  审计里的 `sard_dimension_one_recovered` 把这个重叠**做出来**而不是断言出来。
  `n ≥ 2` 本轮一个字也没说。**`Analysis.sard` 的直接洞状态完全未变。**
* **不是纲领的进展。** 路线探查轮已经写明 `R10` 不在通往 `R0` 的路上；`R0` 现已由分层路线
  独立证出，那条路线从不特化到 `n = m`。`R10` 是事后的旁证/一致性检查。
  `Analysis/EquidimensionalSard.lean` **不 import 秩亏路线的任何部分**，
  所以这个检查是真正独立的：审计里的 `equidimensional_R0_of_R10` 与
  `equidimensional_R10_of_R0` 在 `n = m` 时互推——非空集合的 `μH[0]` 至少是 `1`，
  所以两条陈述在该情形下等价——两条独立证明给出同一结论。

## `N2` 按字面为假

`N2` 的路线陈述是

  `volume S ≠ 0 → 0 < r → μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤`，

其中 `finrank ℝ V - r` 是**截断**自然数减法。取 `finrank ℝ V = 0`：空间是一个点，
唯一非零测集就是这个点，截断指数是 `0` 而不是负数，而单点集的 `μH[0]` 是 `1`，不是 `⊤`。

* `ExponentObstructionAudit.N2_counterexample` 把三件事分开列出：`finrank ℝ Pt = 0`、
  `volume univ ≠ 0`、`μH[((0 - 1 : ℕ) : ℝ)] univ = 1`。
* `route_N2_is_false` 由此导出矛盾。它否定的是路线命题的 `Type` 实例；
  路线里的 `Type*` 版本蕴含该实例，所以否定这一个就否定了它。

**修正是补上维数的正性，并且已证。**
`hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos` 就是加了 `0 < finrank ℝ V` 的 `N2`。
这个假设由反例可知是**必需的**，不是把结论偷偷削弱；它在路线实际引用 `N2` 的地方还是**免费**的：
那里 `r` 是秩，满足 `1 ≤ r < finrank ℝ W ≤ finrank ℝ V`，维数本来就是正的，
`N2_repair_is_free_on_the_route` 记下这条蕴含。所以 `N2` 在路线记录里的**诊断作用不受影响**。

路线语句文件 `research/audits/RankDeficientRouteStatements.lean` 保持**字节不变**，
其中的 `N2` 仍然是一条未兑现的——并且按本轮记录为假的——义务。

## 明确没证什么

* **没有证明任何一般的 Sard 定理。** 见上一节。尖锐有限正则 Sard 仍是直接洞，未触碰。
* **`N1` 未证。** 它是「小 Lipschitz 方法实际给出什么」的诊断，需要 Eilenberg 优函数机器，
  本轮没有做；不是步骤，`R0` 不依赖它。
* **`N2` 未证，且已证其为假**；证出的是修正版，并已如实与 `N2` 区分开命名。
* 不迁洞、不新增证书、不扩大 Blueprint `leanok` 范围、不新增兼容 alias、
  不削弱已证结论、不增加不必要的假设。无量纲 KLS 仍开。

## 边界情形

审计逐条覆盖：`zero_dimensional`（两个空间都平凡：任何线性映射都满射，临界集为空）、
`constant_map` 及其配套的 `constant_map_critical_everywhere`（导数恒零，
正维数靶空间下**处处**临界，结论仍成立是因为整个像只有一个点——这个边界情形不空洞）、
`regular_map`（`n = m` 且微分处处可逆，临界集为空，结论对**每个**水平成立而不止几乎每个）。

## 验证

* 新模块与两个新审计客户端均以 `-DwarningAsError=true` 通过，
  **无 `sorry`、无 `axiom`、无占位、无削弱**。
* `EquidimensionalSardAudit.lean`（208 行，闭包 37 个模块、无 WIP）：
  **13 条标准三公理报告**，其中 `route_R10` 是路线命题的**逐字复制并证明**
  （已用脚本核对与路线文件在去空白后逐字相同）。
* `ExponentObstructionAudit.lean`（119 行，闭包 3 个模块、无 WIP）：
  **4 条标准三公理报告**。其中 `route_N2_is_false` 的命题与路线 `N2` 在去空白后逐字相同，
  只把 `Type*` 换成 `Type`（否则无法在 Lean 里否定一条全域量化的宇宙多态命题）。
* 重跑 **52 个**审计客户端（`research/audits` 45 个、`build/audit` 7 个），
  全部以 `-DwarningAsError=true` 严格通过，**0 失败**。
* 全库公理报告 **665 条**（上一轮 648 + 本轮 17），其中 **12 条 `sorryAx` 未变**，
  仍全部落在四个**故意**报告未决 WIP 结果的客户端里
  （`LevelSetMeasurableAudit`、`IsoperimetryCoareaAudit`、`LipschitzCoareaMigrationAudit`、
  `build/audit/SuperlevelSardScope`）。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 未修改任何既有 `.lean` 文件；聚合 import 未动。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；
  证据 JSON 为 `research/explorations/2026-09-17-equidimensional-sard.json`，
  本地日志在 `build/audit/equidimensional-sard/`，
  最终核对另存 `build/audit/equidimensional-sard/final-snapshot.json`。
* **没有提交、没有推送**，真实 Git index 未改动。

---

## 附记（2026-09-17，同日稍后补记，正文未改写）

上文「明确没证什么」里记的「**`N1` 未证**」在写下时属实，此后已不再成立：
同日后续一轮证出了 `N1`，见 `research/decisions/2026-09-17-exponent-obstruction-n1.md`
与 `research/explorations/2026-09-17-exponent-obstruction-n1.json`。
本附记不改动上文任何其他记载：`R10` 与一般 Sard 的分界未变，
`N2` 仍未证且已知为假（修正版已证），`Analysis.sard` 仍是直接洞，
直接洞仍 8（1/2/5），证书仍 24。
证出 `N1` **不是纲领的进展**——它兑现的正是障碍本身的陈述，指数是 `k + r` 而非 `k`。

## 附记之二（2026-09-17，同日文件管理轮，正文未改写）

上文点名的两个声明改了名字，**类型与证明未变**：

* `ContinuousLinearMap.det_eq_zero_of_not_surjective` → `Analysis.det_eq_zero_of_not_surjective`。
  原先在 `Analysis` 里嵌套 `ContinuousLinearMap` 命名空间，点记法并不会解析到它
  （点记法只认 root 的 `ContinuousLinearMap`），等于白白把命名空间重复进短名，
  撞 `research/naming.md` 第一条。
* 上文「修正版」`hausdorffMeasure_finrank_sub_eq_top_of_finrank_pos` 已挪进模块，
  现为 `Analysis.hausdorffMeasure_finrank_sub_eq_top`。

`R10` 与一般 Sard 的分界、`N2` 为假、直接洞 8（1/2/5）与证书 24 均不受影响。
