# 2026-09-12 — `cor:conditional-fiber-twelve-bound`：注册为第二十三个证书

## 决定

同日证明落地（见[证明记录](2026-09-11-conditional-fiber-twelve-bound-proofs.md)）后，把该节点注册为 Lean 证书。
`KLS/LogConcave/ConditionalFiber.lean` 的六条定理类型与[陈述记录](2026-09-11-conditional-fiber-twelve-bound-statement.md)
一致，注册过程中未再改动。未 `git commit`、未 `git push`（用户指令）。

**陈述变更（owner 决定）**：Blueprint 推论原写 `D_{μ,ρ}(f) ≤ 12∫|∇f|²`、`CPLit(μ) ≤ 12C`，
现改为 `4` 与 `4C`——这正是 `thm:one-dimensional-logconcave-poincare` 提供的常数，也是 Lean 实际证到的强度。
文献常见的 `12` 作为直接弱化保留在正文一句话与 Lean 的 `_of_four` 版本里。
`q:conditional-fiber-frame` 后那段的 `CPLit ≤ 12C` 同步改为 `4C`。

## 新增与修改

- 证书 `solutions/CorConditionalFiberTwelveBound.lean`：
  `Solutions.CorConditionalFiberTwelveBound.certificate μ ρ hμ hρ m hac` 打包 Blueprint 证明的四步：
  (1) `∀ᵐ b ∂baseLaw μ ρ, KLS.LogConcave ⟨kernel μ ρ b, _⟩`；(2) `FiberBound μ ρ 4`；
  (3) 每个 `Energy.LocalSlope.Admissible μ f` 满足 `energy μ ρ f ≤ 4 * Energy.LocalSlope.energy μ f ∧ ≠ ⊤`；
  (4) 每个 `C : NNReal`，`domain μ ρ` 上的形式差界推出 `Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * C`。
  六个 `example`：梯度形式 `4 ∫⁻ ofReal ‖∇f‖ ^ 2`、文献常数 `12` 的弱化版本、有限能量测试落在 `domain μ ρ`、
  推论作为参数化比较引理的实例、`EuclideanSpace ℝ (Fin (n+1))` 上以 `volume` 为 Haar 参考、
  `Fin 0` 上球面概率律不存在。三条公理守卫（证书与两条库定理），均为 `propext / Classical.choice / Quot.sound`。
- `formalization/lakefile.toml`：`Solutions` 根新增 `solutions.CorConditionalFiberTwelveBound`。
- `formalization/FunctionalInequalities.lean`：新增五条导入（`KLS.ConditionalFiber.SliceKernel`、
  `KLS.LogConcave.Line.OfDensity`、`KLS.LogConcave.ConditionalFiber`、`Probability.Line.BrunnMinkowski`、
  `Probability.HaarLine`），模块文档补一段说明推论与其三块分析输入。
- `research/a-series/ledger.yaml`：新增节点 `cor:conditional-fiber-twelve-bound`（`kind: lemma`，`proved / lean`），
  `meta.scope` 追加对数凹条件纤维与常数 4；共二十三个节点。
- `research/check_blueprint.py`：`CERTIFICATES` 新增映射。
- `formalization/blueprint/route-composition.yaml`：该节点 claim `open → proved`，Lean 证据
  （`kls-lean`、ledger 节点、证书声明）。
- `research/tasks.json`：该节点 `missing → available`，`gaps` 清空，证据改为十五个仓库文件（含四个新模块与证书）
  与十六个所用 Mathlib 文件的哈希；`note` 改写为完整证明路线。
  另外刷新三处因本次编辑而过期的哈希：`lem:conditional-fiber-energy-comparison` 的 `EnergyComparison.lean`
  （只去掉了一个 `private`，评估不变）、`prop:weighted-spectator-obstruction` 的 `50-kls-routes.tex`
  （该评估针对 Eldan 随机局部化对象缺失，与本次编辑的条件纤维段落无关）。
- Blueprint `50-kls-routes.tex`：章首 `leanok` 说明加入本推论；推论块常数改 `4`（`12` 作为弱化保留一句），
  加 `\lean{ae_conditionalFiber_logConcave, conditionalFiber_fiberBound_four,
  conditionalFiber_energy_le_four_mul, conditionalFiber_literatureConstant_le_four_mul, certificate}`
  与 `\leanok`，尾部补 Lean 读法；证明块加 `\leanok` 与本地 Lean 路线段（Borell 密度、切片核、Haar 直线拆分、
  一维 Prékopa–Leindler、坏基点的狄拉克律）；`q:conditional-fiber-frame` 后的 `12C` 改 `4C`；
  "Pinned provenance" 段改写为推论已有 Lean 证书、以常数 `4` 陈述，upstream 的 factor-four 仅为历史出处。
  `00-orientation-and-status.tex`：条件纤维路线一句改为三个节点均已认证、`12` 是 `4` 的弱化、
  剩余闸门是 `q:conditional-fiber-frame`。
- 当前指南：`HANDOFF.md`（新节、二十三计数、证书表新行、比较引理节末尾改写）、`README.md`、
  `research/verification.md`（计数与新节）、`formalization/README.md`（两处）、
  `formalization/FunctionalInequalities/KLS/README.md`（两行）、
  `formalization/FunctionalInequalities/KLS/LogConcave/README.md`（一行）、
  `formalization/blueprint/README.md`、`solutions/README.md`（计数与新节）、`research/naming.md`（五行）。
  statement golden、`STATEMENT_CHECKS`、`FoundationAxiomAudit` 未动。

## 检查

- `python3 research/check_ledger.py`：23 节点，0 错误。`python3 research/check_blueprint.py`：87 标签，0 错误。
- `python3 research/atlas.py check`：74 数学节点，23 证书，无环。
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`：103 项全部通过。
  （与上一轮不同，本轮不再有 lake/git 环境导致的失败：本机 elan 与全部 Lean 工具链已从 x86_64 换成原生 arm64，
  根因是 x86_64 的 lake 调 `/usr/bin/git` 时 CLT 的 `libxcrun.dylib` 缺 x86_64 切片；仓库内容与系统 git 配置未改。）
- `lake build`（默认目标）成功，3390 jobs；`solutions.CorConditionalFiberTwelveBound` 已构建。
- `python3 formalization/blueprint/build.py checkdecls` 运行成功，但本机未安装 plastex，
  `blueprint/lean_decls` 仍是 2026-09-08 的旧清单，**未覆盖本次新增的五个 `\lean{}` 名字**。
  作为替代，已用 `lake env lean` 对这五个全限定名逐一 `#check`，全部解析成功、0 错误。
  CI 会重新生成 `lean_decls` 并做真正的比对。
- `python3 research/verify.py` 的收据在本记录与全部指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。

## 证据边界

本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI、commit 或 push。
本次注册不推进 `q:conditional-fiber-frame`：推论给出的是纤维输入 `κ = 4`，不是框架界，
因此仍没有 `μ` 的 Poincaré 不等式，也没有 KLS 结论。`conj:kls` 与四条路线的状态不变。

## 补充（同日）：常数改动的下游残留清理

注册轮之后复查全仓库仍写 `12` 的位置，区分三类：Bobkov 的一维 `12·Var`（保留）、只追加的决定记录（不改）、
以及本推论的输出常数（应为 `4`）。第三类发现两处已经说错，均在 `HANDOFF.md`，已修：

- 一维锐常数那节末尾原写"The fiber corollary `cor:conditional-fiber-twelve-bound` still records
  `12C` and can be sharpened to `4C`"，改为已于本日加强为 `4C` 并完成认证。
- 路线状态清单里原写"the fiber corollary still records `12C` and can be sharpened to `4C`"，
  改为该推论也已 Lean 认证（`Solutions.CorConditionalFiberTwelveBound.certificate`）、以 `4C` 陈述，
  文献 `12C` 是其弱化。

复查后确认无其它残留：`formalization/blueprint/route-composition.yaml` 的 adapters 不编码数值常数；
`45-shared-analytic-bridges.tex` 的 `Var ≥ 1/(12c²)` 是 Bobkov 方差下界，与路线常数无关；
`FunctionalInequalities.lean`、`Line/SharpPoincare.lean`、`solutions/ThmOneDimensionalLogConcavePoincare.lean`
中的 `12` 均指 Bobkov 的独立一维证明。

**标签与标识未改名**：`cor:conditional-fiber-twelve-bound`（Blueprint 标签、ledger 节点 ID、`tasks.json` 键、
route sidecar 节点）与 `Solutions.CorConditionalFiberTwelveBound` 仍带 "twelve"。按 `research/naming.md`
"证书入口、ledger 节点 ID 和来源标签保留稳定身份"，常数变化不触发改名；数值以陈述正文与本记录为准。
