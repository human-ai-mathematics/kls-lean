# 迁出原始 T2 入口：最后一个 coarea 洞闭合

2026-09-16。本轮把直接洞 `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
从 `KLS/WIP/AnalyticPrerequisites.lean` **迁出**到无洞模块
`KLS/Geometry/LipschitzCoarea.lean`，`pp.all` 签名**逐字节不变**，并由上一轮证明的 L12
（`KLS.coarea_of_lipschitz`）在 `S = Set.univ` 时给出证明。直接洞由 **9（2/2/5）降到
8（1/2/5）**。**不证明任何新定理**，不提交、不推送，不改写历史决定。

起始 HEAD 与 `origin/main` 均为 `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`；起始 passed 回执为
`build/verification/20260916T072336.749178Z/report.json`：10 个门、198 个本地模块内核重放、
492 条目，快照 `87051db917d503cf61aa3d227baa3e102ce22627679b47372ca65ab8e15e487e`。
起始工作区含前几轮尚未提交的改动，本轮在其之上继续，全部保留。

## 迁出的内容与签名核对

新位置是 `KLS/Geometry/LipschitzCoarea.lean` 的末尾，紧接它消费的 L12：

```lean
theorem FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (KLS.coarea_of_lipschitz (S := univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa only [setLIntegral_univ, univ_inter] using h
```

**签名逐字节不变，两项机器核对，不是肉眼比较也不是 defeq 声称**：

* 迁出前在导入 WIP 的环境里以 `set_option pp.all true` 打印该常数类型，存为
  `build/audit/t2-migration/signature-before.raw`；迁出后在导入新模块的环境里同样打印，存为
  `signature-after.raw`。两文件 `cmp` 通过，SHA256 同为
  `9e2121c254f66ed331b0f8fbb6b7ca7955f277f3f66705d7ed21a6ff490786a9`。
* `#check @` 会把全称层级重命名为 `u_1`，因此另有一次元程序探针直接读取环境中的
  `ConstantInfo`：`binders-before.raw` 与 `binders-after.raw` 显示两边存储的
  `levelParams` 都是 `[u]`，十二个 binder 的名字与 `BinderInfo` 完全一致，
  类型哈希同为 `2073454840`。唯一差异是匿名实例 binder 内部的模块卫生标签
  （`inst._@.<模块名>...`），它按构造就是所在模块名，且是不可访问名，不属于公开接口；
  把该标签归一化后两份报告逐字节相同（`binders-*.normalized`）。

因此保留了：同一 universe 参数 `u`；同样**六个**实例参数及其顺序，其中 `CompleteSpace V`
正是语句里 `gradient` 实际解析到的实例（`@gradient.{0,u_1} … inst_2 u x`），并非无用参数；
同样的隐式绑定 `u`、`K`、`g` 与同样的假设名 `hu`、`hg`；同样的 `LipschitzWith` 假设；
同样的 `KLS.surfaceMeasure` 归一化和不加限制的 `ℝ≥0∞` 权重范围。
**没有**增加 C¹、正维、有限体积、可积性或 SFinite 假设，**没有**新增兼容 alias，
**没有**重复证明 coarea。文档注释原样保留。

声明保留 `FunctionalInequalities.Analysis` 命名空间（公共名不能变），文件放在
`KLS/Geometry/` 与它消费的 coarea 层并列；`KLS/Geometry/LevelSetMeasurable.lean` 与
`KLS/Geometry/IsoperimetryCoarea.lean` 是同样的安排。新位置在 `L12` 之后另开
`namespace FunctionalInequalities.Analysis` 与独立 section，不复用 L12 的 section 变量。

## 对 WIP 文件的改动

`KLS/WIP/AnalyticPrerequisites.lean` 只删除了这一条声明，并相应更新了文件头对该义务的描述；
删除后 `section Coarea` 内只剩标题注释与一行不再被任何声明使用的 `variable`，一并移除
（纯脚手架，不含任何声明，不改变任何签名）。
**`Analysis.sard` 与 `Analysis.ae_forall_fderiv_ne_zero` 的语句、证明与位置全部不变**，
迁出前的原文存为 `build/audit/t2-migration/AnalyticPrerequisites.before.lean`，
迁出前的 `LipschitzCoarea.lean` 存为同目录的 `LipschitzCoarea.before.lean`。

## 消费者与 import

Lean 侧只有两个审计客户端引用这个名字，库里没有任何模块消费它。两者都加了一行
`import FunctionalInequalities.KLS.Geometry.LipschitzCoarea`，**客户端语句一字未改**：

* `research/audits/LevelSetMeasurableAudit.lean`
* `research/audits/IsoperimetryCoareaAudit.lean`

新模块的本地 import 闭包共 29 个模块，其中**没有任何 WIP 模块**，没有引入反向依赖。

## 洞数变化与仍然开着的洞

* `KLS/WIP/AnalyticPrerequisites.lean`：**2 → 1** 个直接洞，剩下的正是尖锐 `C^(finrank)`
  `Analysis.sard`。
* `KLS/WIP/CheegerInfimum.lean`：2（不变），即两条 Cheeger 比较。
  `Energy/WIP/Cheeger.lean`：5（不变）。
* 总计 **9 → 8**。证书仍 **24**，perimeter infrastructure 仍 **missing**。

T1（`Analysis.aemeasurable_lintegral_levelSet`）、T2（本轮）、T3
（`KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`）三个原始目标
现已全部正式接通到无洞模块，三次迁出的 `pp.all` 签名都是机器核对的逐字节不变。

## 审计

新客户端 `research/audits/LipschitzCoareaMigrationAudit.lean` **同时导入**新模块与**两个**
WIP 文件，所以下列 16 条报告出自同一个环境，迁出的名字在其中只解析到一条声明。
十二条只依赖 `propext`、`Classical.choice`、`Quot.sound`：

* `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（迁出的原声明）；
* `KLS.coarea_of_lipschitz`（L12，证明来源）；
* `Analysis.aemeasurable_lintegral_levelSet` 与
  `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（前两轮迁出的邻居）；
* 八个客户端：逐字复述并以**具名参数**兑现的 `client_migrated_t2`（改名 binder 或调换假设
  在此不会通过 elaboration）、按原路线命题文本书写并只经迁出入口兑现的 `original_T2`、
  `client_L12`、把两半合成原始两段结论的 `client_both_halves`、在 0 处确实不可微的范数函数
  `norm_not_contDiff`、恒 ∞ 权重 `infinite_weight`、零维 `zero_dimension`，以及上一轮 C¹
  特化的 `client_contDiff_specialization`。

四条仍含 `sorryAx`，都是本轮未触碰的开放洞：`Analysis.sard`、
`Analysis.ae_forall_fderiv_ne_zero`、`Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`、
`Isoperimetry.smoothConstant_le_minkowskiConstant`。

两个既有消费者的报告按预期变化，不是回归也不是全体清零：

* `LevelSetMeasurableAudit`：两条 coarea 报告
  （`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 与 `client_coarea_statement`）
  摆脱 `sorryAx`；`Analysis.sard` 与 `Analysis.ae_forall_fderiv_ne_zero` 仍保留 `sorryAx`。
* `IsoperimetryCoareaAudit`：两条 Lipschitz coarea 报告
  （同一个名字与 `client_lipschitz_coarea_statement`）摆脱 `sorryAx`；
  `Analysis.sard`、两条 Cheeger 比较与 `minkowskiConstant_eq_smoothConstant` 仍保留 `sorryAx`。

## 本轮没有做的事

* **没有证明任何新定理**；本轮只有一次迁出与接线。
* 没有扩展到 Cheeger 或尖锐 Sard，没有证明尖锐 `Analysis.sard`、两条 Cheeger 比较、
  两个 Cheeger 常数相等、Energy 的五个洞或维数无关 KLS。
* 没有扩大证书或 Blueprint `leanok` 范围；没有把 coarea 完成误标为 KLS 完成。
* **没有提交、没有推送**，真实 Git index 未改动。

## 验证

* `KLS/Geometry/LipschitzCoarea.lean` 以 `-DwarningAsError=true` 单独编译通过，无 `sorry`。
* 新客户端以 `-DwarningAsError=true` 编译通过，16 条 `#print axioms` 给出上节的边界。
* 签名 `cmp` 通过，binder/universe 探针归一化后逐字节相同。
* 重跑全部 24 个审计客户端（`research/audits` 17 个，已有 `build/audit` 7 个），
  全部严格编译通过。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **1/2/5，总数 8**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全一致；证据 JSON 为
  `research/explorations/2026-09-16-t2-coarea-migration.json`，最终核对另存
  `build/audit/t2-migration/final-snapshot.json`，避免给回执自身制造循环哈希。
