# 秩分层与核引理：秩亏路线的 R1 与 R2

2026-09-17。本轮**证明新定理**：秩亏路线义务清单上的 **`R1`（秩分层可测 + 临界集的有限分解）**
与 **`R2`（核引理）**，按上一轮建议的主攻顺序头两项。
**只证了这两条**；`R0`、`R3`–`R10`、`N1`、`N2` 仍未证，
**余维 m coarea 的秩亏部分仍然开着**。本轮**没有证明任何 coarea 公式、任何切片定理、任何 Sard 定理**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260917T044025.829812Z/report.json`：10 个门、215 个本地模块内核重放、
573 条目，快照
`f500b26955fdb2cd97ba613222e82b08a54fd44d66f8c2a88fdd974084a79058`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 更正上一轮记录的一处事实错误

上一轮（`2026-09-17-rank-deficient-route.md`）给出的「本轮什么也没证」的理由是：
新增库模块必须进 `formalization/FunctionalInequalities.lean` 的聚合 import 才会被默认构建覆盖，
而那要修改既有 `.lean`。**这条理由是错的。**
`research/verify.py` 的 `replay_sources` 从**源码树**计算构建与内核重放范围，
其 `build_replay_inputs` 的注释原文就是
"Build the exact replay scope, **including modules outside default import closures**"，
并以 `lake build +Module…` 逐个构建。现有的 `Analysis/Vector*.lean` 十余个模块同样不在聚合 import 里，
一样被 215 个模块的重放门覆盖。
所以新增 `Analysis/` 模块**不需要**改聚合 import。本轮据此新增模块，**未修改 `FunctionalInequalities.lean`**。

上一轮的决定记录、探查 JSON 与回执**不改写**；更正以本记录为准，
并在 `HANDOFF.md`、`research/verification.md` 的本轮新节中写明。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/RankStratification.lean`
（**仅依赖 Mathlib**，本地 import 闭包 **1 个模块**、无 WIP）。

### `R2` 核引理（纯线性代数）

* **`ker_comp_eq_ker_of_finrank_range_eq`**：若 `P.comp L` 满射，且
  `finrank W₁ = finrank (range L)`，则 `ker (P ∘ L) = ker L`。
  证明：`range (P ∘ L) = P '' (range L)`，故 `P` 在 `range L` 上的限制满射；
  两边维数相同，有限维下满射即单射；于是 `P (L z) = 0 ⟹ L z = 0`。
* **`apply_eq_zero_of_comp_apply_eq_zero`**：路线直接消费的形式，
  `∀ z, P (L z) = 0 → L z = 0`——**在层上，微分沿正则部分的纤维方向为零**。

**维数假设是必需的，而且是给出反例而不是断言。** 审计的 `rank_hypothesis_necessary`
只删掉维数假设：平面上取 `L = id`、`P =` 第一坐标泛函，`P ∘ L` 满射到 `ℝ`，
但 `rank L = 2 ≠ 1 = finrank ℝ`，第二个基向量落在 `ker (P ∘ L)` 而不在 `ker L`。
所以 `R2` **不是**关于复合满射性的陈述，它恰恰断言 `P` 不压塌 `range L` 的任何部分。

`R2` **不用**内积、不用测度、不用完备性；只要 `V` 与 `W₁` 有限维，`W` 可以是任意赋范空间。

### `R1` 秩分层

* **`setOf_rank_eq`**：`{f | rank f = r} = {f | r ≤ rank f} \ {f | r+1 ≤ rank f}`，
  有限维下秩是整数。
* **`measurableSet_rank_fderiv_eq`**：`C¹` 映射的秩分层可测。
  Mathlib 的 `isOpen_setOfPred_nat_le_rank` 给秩的下半连续性，
  沿连续的导数拉回两个开集作差。**算子空间上不需要任何可测结构**，
  靶空间也**不需要有限维**（审计的 `stratum_measurable_without_target_finrank`）。
* **`setOf_not_surjective_fderiv_eq_iUnion`**：
  `{x | Du x 不满射} = ⋃_{r < m} {x | rank (Du x) = r}`，有限并。
  **不用 `u` 的任何正则性**，是逐点的线性代数。

## m = 1 退回已证的标量情形

审计的 `codimension_one_collapse`：`finrank W = 1` 时
`{x | Du x 不满射} = {x | Du x = 0}`——分层只剩一层，余维一里本轮什么也没加。
`codimension_one_critical_slices` 由此**导出**（不是断言）仍未证的 `R0` 在 `m = 1` 的情形，
用的是已证的 `ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`。
**这没有关掉秩亏问题的任何部分**：`m = 1` 时秩亏部分是空集，开着的是 `m ≥ 2`。

## 边界情形

* **零维靶空间**：每个映射都满射，临界集为空，`⋃_{r<0}` 也为空
  （`zero_dimensional_target`）。这正是 `R0` 不需要「余维为正」假设的原因。
* **零维定义域**：所有秩为零（`zero_dimensional_domain`）。
* **分层指标超过靶空间维数**：该层为空（`stratum_empty_of_le`）。
* **`R2` 的退化实例**：零维投影靶空间下复合满射、结论空洞成立（`zero_map_zero_target`）。
* 无任何有限性、内积、完备性或测度假设进入 `R2`。

## 本轮没有做的事

* **没有证明 `R0`**：秩亏部分（`m ≥ 2` 的中间秩）一点没动。
* **没有证明 `R3`–`R10`、`N1`、`N2`**。按上一轮的顺序，下一步是 `R3`（近似右逆，逐点与邻域一致），
  然后是**不归点 `R4`**（纤维上的小 Lipschitz 估计）。
* **没有证明任何 coarea 公式**，也没有改进已证的余维 m coarea 的适用范围。
* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言。
* 没有修改任何既有 `.lean`（包括 `FunctionalInequalities.lean` 与
  `research/audits/RankDeficientRouteStatements.lean`，后者继续**保持原字节**）；
  没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句文件

`research/audits/RankDeficientRouteStatements.lean` **保持原字节**：它是路线的历史记录。
`R1` 的两条命题与 `R2` 的命题由新客户端
`research/audits/RankStratificationAudit.lean` **逐字复制并证明**
（`route_R1_measurable`、`route_R1_decomposition`、`route_R2`），
这是本仓库对「路线义务已兑现」的既有约定。
本轮也重跑了 `AreaFormulaRouteStatements.lean`，**未发现新的错误**，它同样保持原字节。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/RankStratificationAudit.lean` 的 **20 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`：8 条是新模块的全部声明，
  3 条是逐字兑现的路线命题，其余是核形式、维数假设必需性的反例、四个边界情形、
  靶空间不需有限维的加强版，以及 `m = 1` 的两条。
* 重跑全部 **42 个既有审计客户端**加新客户端共 **43 个**，全部严格通过，0 失败；
  公理报告 578 条，其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里，与上一轮一致。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-rank-stratification.json`，
  最终核对另存 `build/audit/rank-stratification/final-snapshot.json`。
