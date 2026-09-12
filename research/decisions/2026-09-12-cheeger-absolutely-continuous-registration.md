# 2026-09-12 — `cor:absolutely-continuous-relaxation-two-cheeger`：注册为第二十四个证书

承接[陈述记录](2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md)、
[证明记录](2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md)与
[元数据记录](2026-09-12-smooth-gradient-relaxation-two-cheeger-metadata.md)，按
[本轮提示词](2026-09-12-cheeger-absolutely-continuous-scope-prompt.md)执行。
未 `git commit`、未 `git push`。

## 决定

把 `Energy/WIP/Cheeger.lean` 中**已经无 `sorry`** 的绝对连续/对数凹范围拆出来转正，立为新的 Blueprint 节点
`cor:absolutely-continuous-relaxation-two-cheeger` 并注册为第二十四个证书。
**无条件节点 `thm:smooth-gradient-relaxation-two-cheeger` 的陈述未改、未加 `\lean{}`/`\leanok`，仍未认证。**

## 模块拆分

原 584 行的单一 WIP 模块拆成三个：

| 文件 | 内容 | 状态 |
|---|---|---|
| `Energy/LocalSlope/Relaxation.lean` | `AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`、`LocalSlope.{preEnergy,relaxation}` 及其无 `sorry` 引理、无条件比较 `relaxation_le_asymptoticLipschitz` | 已注册，无 `sorry` |
| `Energy/Cheeger.lean` | `Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`、`SmoothGradient.Test.*`、`localSlope_relaxation_le`、两条 `_of_absolutelyContinuous`、`Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`、`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | 已注册，无 `sorry` |
| `Energy/WIP/Cheeger.lean` | **只剩**五条奇异情形的开放义务（两条真义务 + 三条三行推论） | 未注册 |

「无 `sorry` 部分对依赖封闭」不是靠人工断言，而是**由编译强制**：两个注册模块里删掉了那五条声明，
如果任何保留下来的声明（传递地）用到它们，`lake env lean` 会以 unknown identifier 失败。实际一次通过。

所有声明的类型均未改动，只搬了位置并按新模块补了模块 docstring。

## 新增与修改

- 证书 `solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean`：
  `certificate μ m hac` 打包 (1) `SmoothGradient.relaxation (intrinsicMeasure μ) = LocalSlope.relaxation (intrinsicMeasure μ)`；
  (2) 对每个 `f : L²(μ)`，`SmoothGradient.Intrinsic.energy μ f = 2 * Cheeger.Intrinsic.energy μ f`。
  五个 `example`：对数凹律自动满足前提、约定 `2·Ch = LocalSlope.relaxation`、无条件不等式
  `LocalSlope.relaxation ≤ SmoothGradient.relaxation`、一点空间上 Cheeger 能量为零、Euclidean 族的定型应用。
  三条公理守卫，均为 `propext / Classical.choice / Quot.sound`。
- Blueprint `30-open-canonical-bridges.tex`：无条件定理后新增推论块（`\uses{def:selected-canonical-frontend,
  lem:logconcave-intrinsic-absolute-continuity}`、六个 `\lean{}` 名字、陈述与证明块各一个 `\leanok`），
  并改写其前的说明段，指明开放义务的全部内容就是 WIP 模块，绝对连续范围已单列并认证。
- `formalization/lakefile.toml` 的 `Solutions` 根；`formalization/FunctionalInequalities.lean` 新增两条导入与一段文档。
- `research/a-series/ledger.yaml`：新增第 24 个节点（`proved / lean`），`meta.scope` 追加。
- `research/check_blueprint.py` 的 `CERTIFICATES` 新增映射。
- `research/tasks.json`：**未改**。被 ledger 记录的节点不需要 task 条目（`atlas.py` 只对
  `not recorded and not in records` 报错），本轮也没有任何既有证据哈希过期。
- `formalization/blueprint/route-composition.yaml`：**未改**。该节点属于第 30 章的开放桥接，不是任何路线的
  `all_of` 成员；无条件节点同样不在 sidecar 中。`atlas.py check` 通过，无需条目。
- 指南：`HANDOFF.md`（新节、二十四计数、证书表新行）、`README.md`、`research/verification.md`（计数与新节）、
  `formalization/README.md`、`formalization/FunctionalInequalities/Energy/README.md`（两行）、
  `formalization/blueprint/README.md`、`solutions/README.md`（计数与新节）、
  `research/naming.md`（两行，按陈述记录「未做」一节列出的三组名字）。

### 顺带修正的两处过时表述

- `formalization/blueprint/README.md` 原写「The remaining marked node is
  `thm:smooth-gradient-relaxation-two-cheeger`」——该标记已于 2026-09-12 移除，现在没有任何节点带 `\notready`，已改写。
- `formalization/README.md` 原写条件纤维那段「does not provide ... an identification with Cheeger energy `2 · Ch`」
  ——在绝对连续范围内现在提供了，已改写并指明奇异情形仍开放。

## 检查

- `python3 research/check_ledger.py`：24 节点，0 错误。`python3 research/check_blueprint.py`：88 标签，0 错误。
- `python3 research/atlas.py check`：75 数学节点，24 证书，无环。
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`：103 项全部通过。
- `lake build`（默认目标）成功；`lake env lean -DwarningAsError=true` 对两个新注册模块与证书均无输出。
- `blueprint/lean_decls` 因本机未装 plastex 仍是旧清单，故新增的六个 `\lean{}` 名字改用 `lake env lean` 的
  `#check` 逐个验证（见下）。CI 会重新生成清单并做真正比对。
- `python3 research/verify.py` 的收据在本记录与全部指南编辑之后生成。

## 证据边界

本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI、commit 或 push。
本次注册**不推进** `thm:smooth-gradient-relaxation-two-cheeger`：奇异测度下两种松弛的比较与
光滑梯度松弛的识别仍无文献出处、无证明，五条义务原样留在 WIP 模块。
也不推进任何 Poincaré 常数、Cheeger–Buser 比较或 `def:isoperimetric-cheeger-scale` 的等周数。
