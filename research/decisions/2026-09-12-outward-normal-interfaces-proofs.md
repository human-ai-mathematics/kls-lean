# 2026-09-12 — 外法向与边界积分接口：填 sorry（4/4 完成）

承接同日的[接口陈述与 sorry 提示词](2026-09-12-outward-normal-interfaces-sorry-prompt.md)。本轮只改动
`formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` 一个文件：新增的四条边界正则性
义务全部证完，四条的类型逐字未动，其余 17 条陈述、两个 `def` 的定义体和既有证明体未动。
未补 C1/C2、coarea、Sard，未改 `RelativePerimeter.lean` / `CheegerInfimum.lean`，未登记 ledger/tasks，
未改证书入口、聚合 import 或 Blueprint，未提交、未推送。

## 一览

| 义务（命名空间 `FunctionalInequalities.KLS.SmoothDomain`） | 填完 | 无 `sorryAx` | 关键 API | 剩余障碍 |
|---|---|---|---|---|
| `continuousOn_outwardNormal` | 是 | 是 | `outwardNormal_eq`、`ContDiff.continuous_fderiv`、`InnerProductSpace.toDual` 的连续等价、`ContinuousAt.inv₀`、`ContinuousWithinAt.congr_of_eventuallyEq` | — |
| `measurable_outwardNormal` | 是 | 是 | `ContinuousOn.measurable_piecewise`、`isClosed_frontier.measurableSet`、`Set.piecewise_eq_of_mem/notMem` | — |
| `isLocallyFiniteMeasure_surfaceMeasure_frontier` | 是 | 是 | `Analysis.exists_hausdorffMeasure_levelSet_lt_top`、`SmoothDomain.frontier_inter_eq`、`Measure.restrict_apply'`、`Nat.cast_sub`、`Module.finrank_zero_iff` | — |
| `integrableOn_smul_outwardNormal` | 是 | 是 | `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`、`Continuous.integrable_of_hasCompactSupport`、`Integrable.mono`、`norm_outwardNormal` | — |

四条的 `#print axioms` 都只有 `propext / Classical.choice / Quot.sound`。

## 路线

### 1. `continuousOn_outwardNormal`

逐点证 `ContinuousWithinAt`。在 `x ∈ frontier` 处取 `U.exists_defining` 给的 `(W, φ)`，
`outwardNormal_eq` 把 `frontier ∩ W` 上的法向写成归一化梯度 `h y = ‖∇φ y‖⁻¹ • ∇φ y`。
`∇φ = (InnerProductSpace.toDual ℝ V).symm ∘ fderiv ℝ φ` 连续（`hφ.continuous_fderiv`），
`hφ' x hxW` 经 `toDual_gradient` + `map_zero` 给 `∇φ x ≠ 0`，于是 `h` 在 `x` 处 `ContinuousAt`。
`frontier ∩ W` 是 `𝓝[frontier] x` 的成员（`self_mem_nhdsWithin` 与 `hW.mem_nhds hxW` 取交），
用 `ContinuousWithinAt.congr_of_eventuallyEq` 搬运。不需要可数子覆盖，也没有断言全空间连续。

### 2. `measurable_outwardNormal`

`outwardNormal = (frontier U.carrier).piecewise outwardNormal 0`（对 `x ∈ frontier` 与否分情况，
非边界分支展开 `outwardNormal` 的 `dif_neg`），再用第 1 条、`continuousOn_const` 与
`isClosed_frontier.measurableSet` 调 `ContinuousOn.measurable_piecewise`。
`Set.piecewise` 的可判定性实例由声明前的 `open Classical in` 提供，和 `outwardNormal` 的定义一致。

### 3. `isLocallyFiniteMeasure_surfaceMeasure_frontier`

逐点构造有限测度邻域。

* `x ∉ frontier`：取 `(frontier U.carrier)ᶜ`（`isClosed_frontier.isOpen_compl`），
  `Measure.restrict_apply'` 后集合是 `∅`，测度为零。
* `x ∈ frontier`：边界非空排除零维——若 `finrank = 0`，`Module.finrank_zero_iff` 给 `Subsingleton V`，
  于是 `carrier` 只能是 `∅` 或 `univ`，两种情况的 `frontier` 都是 `∅`，与 `hx` 矛盾。故 `1 ≤ n`，
  `Nat.cast_sub` 把 `surfaceMeasure` 的自然数指数 `((n - 1 : ℕ) : ℝ)` 对齐到点态引理的 `(n : ℝ) - 1`。
  取 `U.exists_defining` 的 `(W, φ)`，`Analysis.exists_hausdorffMeasure_levelSet_lt_top` 给出
  `N ∈ 𝓝 x` 与 `μH[(n:ℝ)-1] (N ∩ {φ = φ x}) < ⊤`；邻域取 `N ∩ W`，
  `frontier_inter_eq` 给 `φ x = 0` 和 `N ∩ W ∩ frontier ⊆ N ∩ {φ = φ x}`。
  展开 `surfaceMeasure`/`hausdorffNormalized` 后是有限 `ENNReal.ofReal` 系数乘上有限 raw 测度，
  `ENNReal.mul_lt_top` 收尾。

零维不是被假设排除的，而是被证明在该分支下不出现；无界 frontier 的总测度没有被断言有限。
本条**没有**调用 `RelativePerimeter.isLocallyFiniteMeasure_hausdorff_frontier`（它仍是 `sorry`），
所以导入方向不变，公理审计也干净。

### 4. `integrableOn_smul_outwardNormal`

设 `μ := (surfaceMeasure V).restrict (frontier U.carrier)`。第 3 条作为局部实例引入后，
`isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure` 自动给 `IsFiniteMeasureOnCompacts μ`，
于是 `hη.integrable_of_hasCompactSupport hηc : Integrable η μ`。
可测性来自第 2 条与 `hη.measurable.smul`（`V` 有限维故 `SecondCountableTopology`，
`Measurable.aestronglyMeasurable` 可用）。支配是逐点的：边界上 `norm_outwardNormal` 给 `‖ν‖ = 1`，
边界外 `outwardNormal` 为零，故全空间 `‖η x • ν x‖ ≤ ‖η x‖`，`Integrable.mono` 收尾。
`IntegrableOn` 按定义就是 `Integrable _ μ`，无需额外折回。

## 签名与 linter

四条的 `#check` 输出与填 `sorry` 之前逐字相同（对比记录于本轮验证）。
`isLocallyFiniteMeasure_surfaceMeasure_frontier` 的 `[CompleteSpace V]` 在证明体里用不到——
`FiniteDimensional ℝ V` 已经给每一步提供完备性——但它是陈述轮固定下来的签名的一部分，
`sorry` 时 `unusedSectionVars` 不检查，填完才暴露。按本仓已有先例
（`KLS/WIP/CheegerInfimum.lean:676`、`KLS/LogConcave/ConditionalFiber.lean:92`）在该声明前局部
`set_option linter.unusedSectionVars false in` 并加注释，不改签名、不在文件头关闭 linter。

## 新增声明与 import

没有新增任何声明（private 或公开），没有新增 import。四条证明只用既有 API。

## 计数

目标模块直接 `sorry` 由 9 降到 5（加权 coarea 及其可测性、Sard、两条 Gauss–Green）。
21 条义务中 16 条有证明体，其中 14 条只依赖标准公理；`Analysis.ae_forall_fderiv_ne_zero`（依赖 `sard`）
与 `KLS.SmoothDomain.gradient_mollifiedIndicator_eq`（依赖 C2）仍经输入带 `sorryAx`。
其余 WIP 文件计数不变：`RelativePerimeter` 5、`CheegerInfimum` 9、`Energy/WIP/Cheeger` 5；
四文件合计由 28 降到 24。模块文档的计数与措辞已同步。

## 验证

在 `formalization/` 下：

* `lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites` — 3,088 jobs 成功，
  目标模块恰 5 条 `declaration uses 'sorry'` 警告，无 error，无 linter 警告。
* `lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` — 同上 5 条警告。
* `lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` —
  按预期失败，且 5 条 error **全部**是保留的 `sorry`，没有其他 error 或被升格的警告。
* 独立无 `sorry` 客户端（不入库，临时文件）对四条各写一个真实调用：
  `ContinuousWithinAt`、`Measurable (‖ν ·‖ₑ)`、紧集上 `surfaceMeasure (K ∩ frontier) < ⊤`、
  以及 `integral_inner` 把边界向量积分与内积交换（正是 C2 需要的那一步）；
  该客户端在 `-DwarningAsError=true` 下通过，四条客户端结论的 `#print axioms` 也只有标准三条。
* 四条目标定理逐条 `#check` / `#print axioms`：类型与本轮之前一致，公理为
  `[propext, Classical.choice, Quot.sound]`。
* `git diff --check` 干净；diff 只含目标模块的四处证明填充、一处 linter 注释与 `set_option`、
  模块文档计数更新，以及本记录。

## 与 C1/C2 的关系

本轮**没有**完成 C1 或 C2。四条接口只是把边界侧的正则性和可积性准备好：
取 `F(x) = η(x) • e` 后 `div F = ⟪∇η, e⟫`，体积侧梯度连续且紧支撑、边界侧由第 4 条可积，
才能用 `integral_inner` 与 `ext_inner_right` 把 C1 的标量等式提升为 C2 的向量等式。
C1 本身（Gauss–Green 的标量形式）仍是开的，coarea 与 Sard 也仍是开的。
