# Klartag 前端识别的文献 Poincaré 子句：实现轮

2026-09-19，当日第十三轮，紧接[路线轮](2026-09-19-klartag-literature-poincare-route.md)。
`Q1`、`Q2`、`Q0` **全部证出**，`Q3` 由既有定义直接给出。
`thm:klartag-density-frontend-identification` 三条结论现在都是本地 Lean 证明，节点已标 `\leanok`。
直接洞仍 **0**，证书仍 **26**（本子句属既有节点，未新增证书）。不提交、不推送。

起点 `HEAD = 2a882c8`（领先 `origin/main` 一个提交）。

## 结果

新模块 `formalization/FunctionalInequalities/Poincare/LocalSlope/Gradient.lean`，三条公开声明：

| 义务 | 声明 | 说明 |
| --- | --- | --- |
| `Q1` | `Poincare.LocalSlope.holds_iff_memLp_gradient` | `ν ≪ m` 时，斜率形式与梯度形式的有效常数等价 |
| `Q2` | `Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient` | 任意绝对连续内蕴律，下确界相等 |
| `Q0` | `Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave` | **目标**：对数凹律的文献 Poincaré 子句 |

按路线预期，**没有新增任何定义**：梯度形式的有效性就地写出，最优常数仍是
`Poincare.LocalSlope.Intrinsic.constant`。分析部分全部复用 `Energy/LocalSlope/Gradient.lean`
的四条已证声明，本轮只做了有效性谓词与其下确界上的搬运。

## `Q3` 的结论：由定义给出，不需要引理

路线要求如实记录 `Q3`（仿射原点无关性）究竟是哪一种。**结论是前者**：
`Probability.intrinsicMeasure` 本来就不带原点选择，所以 Blueprint 那句话由既有定义直接给出，
本轮没有为它写任何引理。

比预期多给出一点：`Q0` 的**陈述里也没有参考测度**。Haar 测度是在证明内部造的——
direction 子模是有限维赋范空间，因而弱局部紧，`PositiveCompacts` 实例可推出，
`Measure.addHaarMeasure K₀` 配 `Measure.isAddHaarMeasure_addHaarMeasure` 即可。
所以该常数既不依赖原点也不依赖参考测度。这是仓库里第一处**自己构造** Haar 测度的地方——
既有写法（`constant_eq_localSlope`、`ThmSmoothLipschitzConstantEquivalence`）一律把 `m` 作显式参数。

## 与路线的偏差

路线估 55–70 行，实际模块 114 行（含 22 行模块文档与三条 docstring），证明本体约 30 行。
路线点名的「唯一实质风险」（`Q1` 的 `iff` 两边检验类须逐字对上）**没有发生**：
`admissible_iff_memLp_gradient` 的三元组与梯度形式的三个前提逐字一致，两个方向各三行。

唯一的实现摩擦是 `unusedSectionVars`：`Q2`、`Q0` 不用 `[CompleteSpace E]`，按仓库惯例加
`omit [CompleteSpace E] in`，且必须放在 **docstring 之前**（放在 docstring 与 `theorem` 之间会报
`unexpected token 'omit'`）。

## 记账

* Blueprint `thm:klartag-density-frontend-identification`：加 `\lean{}` 两个名字
  （`Solutions.LemRelativePerimeterCheegerInfimum.intrinsic` 与本轮的 `Q0`）、定理与证明各加 `\leanok`，
  并改写结尾散文——原文写的是「`C_P^lit` 子句未认证，故本节点不带 leanok」，现已不成立。
  同时**明确写下**：这不会让 `thm:logconcave-cheeger-poincare-comparison` 变成已认证。
* 聚合根 `FunctionalInequalities.lean` 加入新模块的 import，使 `lake exe checkdecls` 可达。
* `research/tasks.json`：该节点 note 重写、`infrastructure.status` 由 `unchecked` 改 `available`
  （三条证据带 sha256，`gaps: []`）；另刷新 `lem:relative-perimeter-smoothing` 里
  `45-shared-analytic-bridges.tex` 的 evidence 哈希（本轮改了该文件）。
* 审计客户端 `research/audits/KlartagLiteraturePoincareAudit.lean`：`Q1`/`Q2`/`Q0` 逐字重述并消解，
  另两个边界情形（零维 direction、单个有效常数的搬运）。

## 调度效果

`atlas.py ready` 中 `thm:logconcave-cheeger-poincare-comparison` 由 **`blocked`** 变为
**`inspect_infrastructure`**——「依赖未认证」这条理由消失。它**仍不会**标 `\leanok`：
Buser 半在 `n ≥ 2` 仍是 imported mathematics。`thm:klartag-density-frontend-identification`
变为 `verify_recorded`。

## 验证

`lake build` 通过（3515 jobs）。新模块与审计客户端均以 `lake env lean -DwarningAsError=true`
通过，**0 错误 0 警告**。审计 **8 条 `#print axioms` 报告，全部只有
`propext, Classical.choice, Quot.sound`，0 条 `sorryAx`**；日志
`build/audit/klartag-literature-poincare-proofs/scope-audit.log`。
`check_ledger.py` 26 节点 0 错误；`check_blueprint.py` 88 标签 0 错误；
`atlas.py check` 75 节点 26 证书无环；`research/tests` 104 项通过。
`lake exe checkdecls` 对由 `.tex` 重新生成的 **326** 个 `\lean{}` 名字全部通过（含本轮新增 2 个）。
直接洞 0，无 WIP 模块。回执于本轮末重跑 `research/verify.py` 绑定。
