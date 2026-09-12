# 2026-09-12 — 外法向与边界积分接口：statement 补充及 sorry 提示词

Owner 要求：补入缺失接口，本轮只写 statement，证明体均为 `by sorry`，再生成证明提示词。
本轮在 `KLS/WIP/AnalyticPrerequisites.lean` 新增以下四条公开义务；原有类型、定义体和证明体均保留。
没有新增 C1/C2 的额外假设，没有注册 WIP，也没有完成 Gauss–Green。

| 名称（命名空间 `FunctionalInequalities.KLS.SmoothDomain`） | 结论与边界 |
| --- | --- |
| `continuousOn_outwardNormal` | 法向量在 `frontier U.carrier` 上连续；不声称全空间连续；不要求有限维 |
| `measurable_outwardNormal` | 边界外取零的法向量全空间 Borel 可测；不要求有限维 |
| `isLocallyFiniteMeasure_surfaceMeasure_frontier` | **归一化** `surfaceMeasure V` 限制到光滑区域的闭边界后局部有限；不声称环境表面测度局部有限 |
| `integrableOn_smul_outwardNormal` | `η` 连续且紧支撑时，`η • outwardNormal` 关于归一化边界测度可积；局部有限性是前置结论，不另作调用者假设 |

局部定义函数和已证明的 `outwardNormal_eq` 足以逐点建立边界连续性，继而由闭集分片得到可测性；
无需为此构造可数子覆盖。两条可测/连续接口本身不能代替可积性。C2 从 C1 导出的难度应表述为：
完成边界正则性和可积性接口后，才进入较短的向量积分组装。

当前四个 WIP 文件的直接 `sorry` 数为 `5 + 9 + 9 + 5 = 28`（依次为 RelativePerimeter、
CheegerInfimum、AnalyticPrerequisites、Energy/WIP/Cheeger）。AnalyticPrerequisites 共 21 条义务，
12 个原有证明体已填，9 个直接 hole；原有 12 个证明体中仍只有 10 个传递依赖不含 `sorryAx`。
本次数量增加来自显式分解前置义务，不代表已有证明退化。此前的审计记录保留为其时快照。

本轮陈述检查：目标模块 `lake build` 通过（3,088 jobs），该模块恰有 9 条预期 `sorry` 警告；
独立 API 客户端在 `-DwarningAsError=true` 下通过，四个新声明的公理审计均按预期包含
`sorryAx`，不作为已证明结果。`research/tasks.json` 仅刷新受影响输入的摘要与未完成说明，
基础设施状态仍为 `missing`。

下面代码块可直接交给证明会话。本提示词只针对新增四条，取代旧 17 条提示词在此子任务上的范围；
现有 C1/C2、Sard、coarea 及其他文件的 `sorry` 留待另一个任务。

```text
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS
Lake 根目录：formalization/
目标文件：formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
先核对 git status、formalization/lean-toolchain 和 lake-manifest.json，不使用历史版本号代替当前环境。
先读 HANDOFF.md、research/naming.md、目标模块的说明，以及
research/decisions/2026-09-12-outward-normal-interfaces-sorry-prompt.md。

任务：只填写以下四个新增定理的 sorry，命名空间均为
FunctionalInequalities.KLS.SmoothDomain：
1. continuousOn_outwardNormal
2. measurable_outwardNormal
3. isLocallyFiniteMeasure_surfaceMeasure_frontier
4. integrableOn_smul_outwardNormal

范围与规则：
- 保持四条定理及所有既有声明的类型不变，保持所有 def 定义体和既有证明体不变。
  不加强 SmoothDomain，不添加有界区域、正维、可测法向、边界有限测度等调用者假设。
- 只编辑目标 Lean 文件；允许必要 import 和 private 辅助引理。新增公开 API 需另行说明必要性。
  可以追加一份 proofs 决定记录，列完成情况、验证命令、公理和剩余障碍。
- 不填写 C1/C2、coarea、Sard 或 RelativePerimeter/CheegerInfimum 的旧 sorry。
  不重排模块、不反向导入 AnalyticPrerequisites 到 RelativePerimeter，以免产生循环。
- 不新增 axiom、opaque 假证明、unsafe、关闭检查的选项或隐蔽 sorry；不能把新增定理的 hole
  转移给新辅助引理后声称完成。若 statement 有问题，保留 sorry 并说明反例，不擅改类型。
- 不登记 ledger、tasks 的完成状态，不修改证书入口、聚合 import、Blueprint lean/leanok。
  不提交或推送。可保留未解决的目标，但必须如实报告。

路线 1：边界连续性（不需要可数覆盖）
对任意 x ∈ frontier U.carrier，用 U.exists_defining 取 W、φ、hW、hxW、hφ、hφ'、hU。
在 W ∩ frontier 上，U.outwardNormal_eq 给出 ν(y) = ‖gradient φ y‖⁻¹ • gradient φ y。
- 梯度连续性：gradient φ 是 (InnerProductSpace.toDual ℝ V).symm 与 fderiv ℝ φ 的复合；
  hφ.continuous_fderiv 给连续性。注意 toDual 的命名空间。
- 在 x，hφ' x hxW 给 fderiv 非零，通过 toDual_gradient 和 map_zero 得 gradient 非零。
- 用 ContinuousAt.norm、inv₀、smul 得归一化梯度在 x 连续。
- 由 hW.mem_nhds hxW、self_mem_nhdsWithin 得相对邻域上的 eventuallyEq，
  用 ContinuousWithinAt.congr_of_eventuallyEq_of_mem 转移。
不证明 ν 在全空间连续；零延拓一般在边界处不连续。

路线 2：全空间可测性
使用第 1 条、continuous_const.continuousOn、isClosed_frontier.measurableSet，调用
ContinuousOn.measurable_piecewise。按 x 是否在 frontier 分情况，展开 outwardNormal 的零分支，
把 piecewise 函数与 outwardNormal 对齐。无须为局部定义函数构造可测选择。

路线 3：归一化边界测度局部有限性（这是独立于可测性的几何组装）
本文件已证明 Analysis.exists_hausdorffMeasure_levelSet_lt_top。
对边界点，用 U.exists_defining 和 U.frontier_inter_eq 将一个邻域内的边界包含在正则零水平集，
再由上述点态结果得到某个邻域内 raw Hausdorff measure 有限。
对非边界点，用 frontier 闭性取与边界不交的邻域，限制测度为零。
这样对全空间每个点构造有限测度邻域，建立 IsLocallyFiniteMeasure。
- 目标测度始终是 (surfaceMeasure V).restrict (frontier U.carrier)。
- surfaceMeasure 的维数是自然数 n - 1；点态输入是实数 (n : ℝ) - 1。
  正维时处理 Nat.cast_sub；n = 0 时空间是单点、frontier 为空，限制测度为零。
  不通过添加 Nontrivial V 或 0 < n 排除零维。
- 展开 surfaceMeasure/hausdorffNormalized，将 raw 测度乘上有限 ENNReal.ofReal 系数。
  测度缩放保持所需的局部有限性；限制和缩放的交换要明确处理。
- 不需要先证明整个无界 frontier 的总测度有限，这通常不成立。
- RelativePerimeter 中已有 isLocallyFiniteMeasure_hausdorff_frontier，但它仍有 sorry。
  不能把它当作无条件认证输入来完成本条；最终 #print axioms 必须无 sorryAx。
  使用本文件已证的点态 level-set 引理即可保持当前单向 import，并避免旧 hole 污染。

路线 4：边界积分可积性
设 μ := (surfaceMeasure V).restrict (frontier U.carrier)。由第 3 条安装局部有限实例，
得到 IsFiniteMeasureOnCompacts μ。hη.integrable_of_hasCompactSupport hηc 给 η ∈ L¹(μ)。
- 第 2 条与 hη.measurable.smul 给 η • ν 的可测性；有限维空间满足强可测性所需的拓扑条件，
  用 aestronglyMeasurable。
- 边界上 norm_outwardNormal = 1，边界外 outwardNormal = 0，故全空间都有
  ‖η(x) • ν(x)‖ ≤ ‖η(x)‖。用 Integrable.mono 支配，再折回 IntegrableOn。
- 如果先做任意紧集上有限测度 μ 的 private 版本，仍需实例化到上述边界测度，
  不能只证明条件版本而遗漏当前公开结论。

后续 C2 的关系（本任务不填 C2）：
取 F(x) = η(x) • e，秩一算子的迹给 div F = ⟪gradient η, e⟫，用 C1。
体积侧梯度连续且紧支撑，边界侧由第 4 条可积，才能用 integral_inner 与 ext_inner_right
提升为向量等式。不要把完成本次四个前置接口报告为完成 C1 或 C2。

验证与报告：
在 formalization/ 下运行：
  lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites
  lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
普通模式应无 error；只允许仍保留的 declaration uses 'sorry' 警告。
全部四条完成时，本模块直接 sorry 应从 9 降至原有 5；其他文件计数不变。
逐条在独立客户端 #check / #print 其完整类型，并 #print axioms；完成项只允许
propext / Classical.choice / Quot.sound，标准公理列表可以是其子集。
不要仅凭证明体里没有 sorry 就标为完成，必须检查传递依赖。

仍有旧 sorry 时，直接对整个 WIP 文件运行 -DwarningAsError=true 预期会失败；
记录其错误是否仅为保留的 sorry，不要求通过关闭警告制造绿色结果。
可对导入已构建 WIP 的独立无 sorry 客户端运行 -DwarningAsError=true，检查新 API 的真实调用，
但客户端编译成功本身不能代替上述公理检查。

最后 git diff --check，并检查 diff 只含四个目标的证明填充、必要辅助项/import 和新增报告。
报告逐条列：名称 | 是否填完 | 是否无 sorryAx | 关键 API | 剩余障碍。
```
