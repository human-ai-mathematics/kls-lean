# 补齐正则 coarea 轮的审计证据绑定

2026-09-15。本轮**不证明任何定理**，不改动任何 `.lean` 库源码，不提交、不推送，
不改写历史决定。只做两件收尾：把正则 coarea 轮（L9）的审计客户端放进受版本控制的路径，
并把该轮产物接入 `research/tasks.json` 的 infrastructure evidence。

起始 HEAD 为 `e7768408766af27e08ba0fe9ded61d602efc4056`；起始 passed 回执为
`build/verification/20260915T112258.149854Z/report.json`，其快照与起始工作区完全一致：
447 个文件，SHA256 `fa8697347cab6da1cf30275c0883866c548803c3758ffc3c355894afd42331cd`。

## 修的是什么

`2026-09-15-ci-audit-source-paths.md` 把九个被 `tasks.json` 引用的审计客户端从被忽略的
`build/audit/` 复制到 `research/audits/`，理由是干净 checkout 里读不到 `build/`。
**但 L9 自己的客户端 `RegularCoareaAudit.lean` 漏掉了**：它仍只存在于被忽略的 `build/audit/`，
于是干净 checkout 无法复现 L9 的公理审计。它当时没有被 `tasks.json` 引用，所以 CI 不会失败，
但证据不可复现。

同时，L9 轮没有像之前各轮那样把本轮产物加入 `tasks.json` 的 evidence，
所以那五个新模块与该轮决定记录在 `tasks.json` 这条链上没有哈希绑定
（它们在 `research/explorations/2026-09-15-regular-coarea.json` 里已绑定 73 个文件）。

## 本轮所做

1. `build/audit/RegularCoareaAudit.lean` **逐字节**复制到 `research/audits/RegularCoareaAudit.lean`
   （`cmp` 通过），并从新路径以 `-DwarningAsError=true` 重跑：29 条 `#print axioms`，
   全为 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
   `research/explorations/2026-09-15-regular-coarea.json` 仍绑定原来的本地路径，
   字节未变故两处哈希一致。
2. `research/audits/README.md` 补记这一条的来龙去脉。
3. `research/tasks.json` 的 `lem:relative-perimeter-smoothing` infrastructure evidence
   新增 7 条：`Analysis/LocalInverse.lean`、`Analysis/RegularChart.lean`、
   `Analysis/FiberIntegral.lean`、`KLS/Geometry/OpenSliceMeasurable.lean`、
   `KLS/Geometry/RegularCoarea.lean`、`research/decisions/2026-09-15-regular-coarea.md`、
   `research/audits/RegularCoareaAudit.lean`。只增不改，其余条目原样保留。

## 刻意没有做的事

* **没有改写任何逐轮证据 JSON。** `research/explorations/2026-09-15-regular-coarea.json` 中
  `research/tasks.json` 一条哈希与当前文件不符，这**不是缺陷**：每份逐轮 JSON 只绑定该轮结束
  时的状态，而每一轮都会改动 `tasks.json`，所以全部十份带该条目的 JSON（含更早各轮）都处于
  同样状态。改写它们等于篡改历史记录。
* **没有证明任何新定理**，没有改动任何 `.lean` 库源码，没有动 WIP，
  没有扩大证书或 Blueprint `leanok` 范围，直接洞仍为 **2/3/5，总数 10**，证书仍 **24**，
  perimeter infrastructure 仍 **missing**。
* **没有提交、没有推送。**
* 加权 coarea 的**全局 Lipschitz 等式**（`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  及其 `C¹` 特化）仍是直接洞；L11、L12、L6/L6a/L7 的 Whitney 延拓、尖锐 `C^(finrank)` 的
  `Analysis.sard`、Eilenberg 常数的尖锐性、`smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等，全部仍未证明。

## 并发改动

本轮进行中，仓库外部又落入一个与本轮无关的文档提交
`737abc3 docs: consolidate proof corrections and improvements`（新增
`research/proof-corrections-and-improvements.md`、改动 `README.md`），HEAD 因此从起始的
`e776840` 变为 `737abc3`。本轮既没有制造也没有改写该提交；最终回执绑定的是**含该提交在内**的
最终工作区状态，所以回执的 `head` 与上文的起始 HEAD 不同。本轮自身的四处改动
（新增 `research/audits/RegularCoareaAudit.lean` 与本记录，改动 `research/audits/README.md`
与 `research/tasks.json`）**保持未提交、未推送**。

## 验证

* 从新路径运行 L9 客户端：`-DwarningAsError=true` 通过，29 条公理报告全标准，无 `sorryAx`。
* 其余 16 个审计客户端（`research/audits/` 9 条 + `build/audit/` 7 条）重跑全部严格通过；
  `LevelSetMeasurableAudit`、`SuperlevelSardScope` 中的 `sorryAx` 是刻意报告仍开的洞。
* 三个 WIP 文件逐个实际编译，直接洞 **2/3/5，总数 10**。
* `python3 research/atlas.py check` 与默认 `lake build` 通过。
* 根目录 `python3 research/verify.py` 通过，最终回执为 `build/verification/latest.json`，
  与最终全部源码快照完全一致；核对另存 `build/audit/evidence-completion-final-snapshot.json`。
