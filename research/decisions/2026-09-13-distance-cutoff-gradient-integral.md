# 距离截断的梯度积分估计

日期：2026-09-13。承接 [距离截断路线与状态勘误](2026-09-13-cutoff-route-audit-correction.md)，
该勘误取代 [单向 Cheeger 比较记录](2026-09-13-cheeger-infimum-one-sided.md) 中对应的状态与路线描述。
起始 HEAD 仍为 `2965b32`；上一份 passed 回执 `build/verification/latest.json` 的 381 个文件条目与
开始时的工作区快照逐字匹配（`snapshot.sha256` 相同）。保留此前未提交与未跟踪成果，
本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

`KLS.Isoperimetry.lintegral_enorm_gradient_distanceCutoff_le` 已证明，声明文本与原目标逐字一致：

```
theorem lintegral_enorm_gradient_distanceCutoff_le (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) (B : Set V) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r
```

迁移前后七条声明（`distanceCutoff`、`distanceCutoff_mem_Icc`、`lipschitzWith_distanceCutoff`、
`distanceCutoff_eq_one_of_mem_closure`、`distanceCutoff_eq_zero_of_notMem_thickening`、
`tendsto_distanceCutoff_indicator`、本目标）的 `pp.all` 签名逐字节相同，`diff` 为空——包括本目标
本身，它此前是 `sorry`，section 变量因而全部保留，填体后接口一个没改。

全部数学范围与接口保留：任意有限维实内积空间含零维；`B` 任意，**不**要求非空、可测、闭、有界或
边界零测；`m`、Haar 实例与 `hac` 原样保留在签名里，尽管证明不使用它们；`distanceCutoff` 的定义
与右端的 `ν (closure B)` 不变，没有退回较弱的 `ν B` 上界，也没有改成闭增厚。证明不引入 coarea、
Sard 或任何带 `sorryAx` 的依赖。

本轮把直接洞从 **13** 降到 **12**：AnalyticPrerequisites **3**、CheegerInfimum **4**、
Energy/WIP/Cheeger **5**。正式证书仍为 **24**。这只是反方向链条上的一个梯度估计：
`smoothConstant_le_minkowskiConstant` 仍是直接洞，`minkowskiConstant_eq_smoothConstant` 虽有
`le_antisymm` 证明体但通过反方向继承 `sorryAx`，两个 Cheeger 常数相等**未证**，整条比较链**未**完成。

## 实际证明

1. **空集单独一支。** Mathlib 的约定是 `Metric.infDist x ∅ = 0`，所以
   `distanceCutoff ∅ r x = max 0 (1 - 0 / r) = 1`——是常数 **1**，不是 `0`。
   `gradient_fun_const` 给出梯度为零，左端积分为 `0`；`Metric.thickening r ∅ = ∅` 与
   `closure ∅ = ∅` 使右端为 `(0 - 0) / ofReal r = 0`。因此**没有**为绕过这一情形给声明加
   `B.Nonempty`。
2. **环带。** 非空 `B` 时取 `A = Metric.thickening r B \ closure B`。它可测的理由是
   增厚开、闭包闭（`Metric.isOpen_thickening.measurableSet.diff isClosed_closure.measurableSet`），
   **与 `B` 是否可测无关**。由已有的 `distanceCutoff_eq_one_of_mem_closure` 与
   `distanceCutoff_eq_zero_of_notMem_thickening`（两者都要求 `B` 非空），
   `closure B = {d = 0}`、`thickening r B = {d < r}`。
3. **环带外的梯度逐点为零。** 这是本路线的核心，且是**逐点**结论，不是几乎处处结论：
   由 `distanceCutoff_mem_Icc` 值域为 `[0,1]`，截断在 `closure B` 上取到**全局最大值 1**，
   在增厚之外取到**全局最小值 0**。于是 `Filter.Eventually.of_forall` 直接给出
   `IsLocalMax` / `IsLocalMin`，`IsLocalMax.fderiv_eq_zero` 与 `IsLocalMin.fderiv_eq_zero`
   给出 `fderiv = 0`，再由 `gradient` 的定义（`(toDual).symm` 作用在 `fderiv` 上，`map_zero`）
   得 `gradient = 0`。**两个 API 都不需要额外的 `DifferentiableAt` 假设**，因为 Mathlib 在不可微点
   把 `fderiv` 和 `gradient` 定义为零。两个端点水平集 `{d = 0}` 与 `{d = r}` 因此被自然覆盖，
   没有被误当作某个开集的内部：`{d = r}` 上的点仍然是全局最小点。
   分类写成 `by_cases x ∈ thickening r B`：在增厚内而不在 `A` 中的点必在 `closure B` 中。
4. **环带内的逐点上界。** `lipschitzWith_distanceCutoff`（已有，常数 `Real.toNNReal r⁻¹`）配
   `norm_fderiv_le_of_lipschitz`（同样无需可微性）给 `‖fderiv‖ ≤ r⁻¹`，
   `LinearIsometryEquiv.norm_map` 把它换成 `‖gradient‖ ≤ r⁻¹`，
   `Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)` 处理 `ℝ≥0` 到 `ℝ` 的强制转换，
   `ofReal_norm` 把实范数换成 `enorm`，`ENNReal.ofReal_le_ofReal` 收尾。合起来得到
   `‖gradient w_r x‖ₑ ≤ A.indicator (fun _ ↦ ENNReal.ofReal r⁻¹) x`，对**每个** `x` 成立。
5. **积分与收尾。** `lintegral_mono` 用第 3、4 步的逐点界，
   `lintegral_indicator_const hAmeas` 得 `ENNReal.ofReal r⁻¹ * ν A`；
   `measure_sdiff (Metric.closure_subset_thickening hr B) isClosed_closure.nullMeasurableSet
   (measure_ne_top _ _)` 得 `ν A = ν (thickening r B) - ν (closure B)`（有限性来自概率测度）；
   最后 `ENNReal.ofReal_inv_of_pos hr` 与 `ENNReal.div_eq_inv_mul` 把 `ofReal r⁻¹ * X` 换成原声明的
   `X / ENNReal.ofReal r`。

路线因此不使用 Rademacher、Lebesgue 密度定理、任何“水平集上梯度几乎处处为零”的一般引理，也不使用
`hac`。`hac` 与 `m` 未被使用是这条更强路线的结果，不是弱化：结论、右端与全部假设都没有变。
按要求**没有**删除未用假设，也**没有**制造虚假用途；只对这一条声明局部叠加
`set_option linter.unusedSectionVars false in` 与 `set_option linter.unusedVariables false in`，
并在注释中写明原因，没有全文件关闭警告。此处“不可微点梯度为零”是 Mathlib 的定义约定，
仅服务于这一估计，**不**构成任何关于一般奇异律比较的结果。

## 分层与迁移

* 新模块 `formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean` 无洞，
  **本地导入闭包为 0 个模块**：只依赖 Mathlib，和 `Geometry/MinkowskiContent.lean` 同级。
* 按实际依赖迁移完整的距离截断基础：`distanceCutoff` 定义、`distanceCutoff_mem_Icc`、
  `lipschitzWith_distanceCutoff`、`distanceCutoff_eq_one_of_mem_closure`、
  `distanceCutoff_eq_zero_of_notMem_thickening`，以及已有的 `L¹(ν)` 收敛
  `tendsto_distanceCutoff_indicator`。前四条是本目标的直接依赖；`tendsto_distanceCutoff_indicator`
  一并下移，因为它无洞、无 `sorryAx`，而且它的全部依赖恰好就是上面那四条——把它单独留在 WIP 会
  把同一个 `distanceCutoff` API 拆到两个模块。证明原样移动，全名与 `pp.all` 签名逐字不变，
  没有兼容别名、转发证明、空壳模块或重复实现。
* **没有**机械搬运整个 WIP 文件：`exists_smooth_approximation_lipschitz` 留在原处。它已证明
  （不要重复实现），但属于光滑替身接口而不是截断基础，且会把
  `Energy.Euclidean.LipschitzApproximation` 这条无关的导入带进新的几何模块；它的消费者是仍未完成的
  反方向比较。同理，Sard／coarea 的两条 KLS 侧义务、
  `smoothConstant_mul_lintegral_min_superlevel_le`、`smoothConstant_le_minkowskiConstant`、
  `minkowskiConstant_eq_smoothConstant` 与仿射支撑传输段都留在 `KLS/WIP/CheegerInfimum.lean`，
  该文件加一行导入新模块。
* `Geometry/MinkowskiConstant.lean`、`Geometry/CheegerInfimum.lean` 与
  `Geometry/PerimeterRecovery.lean` 一字未改：没有把恢复序列或任何无关几何依赖塞进基础层。

## 验证

* 七条声明（定义、四条截断引理、`L¹` 收敛、本目标）的传递公理均为
  `propext / Classical.choice / Quot.sound`，无 `sorryAx`。
* 新模块与 `Geometry/{CheegerInfimum,MinkowskiConstant,MinkowskiContent}` 都以
  `lake env lean -DwarningAsError=true` 编译通过（`build/audit/distance-cutoff-strict-*.log`）。
* 迁移前后的 `#check`（`set_option pp.all true`）输出逐字节 `diff` 为空，确认 section 变量没有变化，
  接口没有被无意改动。
* 新的独立客户端 `build/audit/DistanceCutoffAudit.lean` 严格编译通过，含 7 个客户端与 14 条公理
  报告，全部只用标准三条公理：显式带“`B` 不可测”“`B` 无界”假设的一般情形；
  **空集截断恒为 1**（并由定理得左端为零）；全空间（增厚与闭包都是全空间，两端为零）；
  零维；`closure B` 上**每一点**梯度为零（含内端点水平集 `{d = 0}`）；
  `{d = r}` 这一**外端点水平集上每一点**梯度为零；以及迁移后的 `L¹(ν)` 收敛仍可用。
* 既有客户端 `CheegerInfimumAudit`、`MinkowskiConstantAudit`、`MinkowskiCoareaAudit`、
  `RecoveryAudit`、`DilationAudit`、`GaussGreenAudit` 与路线核验文件 `CutoffRouteReview`
  重跑，严格模式通过，14 + 17 + 18 + 14 + 17 + 22 条公理报告仍只用标准三条公理。
* 三个 WIP 文件实际普通模式重编译，诊断为 **3/4/5** 个直接洞，没有其他诊断
  （`build/audit/distance-cutoff-wip-*.log`）；仍不是严格模式通过。
* 默认 `lake build` 通过，随后从根目录 `python3 research/verify.py`；最终源码回执为
  `build/verification/latest.json`。`research/tasks.json` 中 `lem:relative-perimeter-smoothing`
  的证据加入新模块条目，gaps 改写为下一步的实际缺口，status 仍为 `missing`。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 反方向剩余依赖的分类

`smoothConstant_le_minkowskiConstant` 之前还有五件事，必须分开记，不能合并成“组装”：

1. **加权 coarea 公式**：`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
   （`WIP/AnalyticPrerequisites`，**直接洞**）——Lipschitz `u` 的
   `∫ g ‖∇u‖ dvolume = ∫_ℝ (∫_{u=t} g dℋ^{n-1}) dt`。
2. **水平集积分的可测性**：`Analysis.aemeasurable_lintegral_levelSet`
   （`WIP/AnalyticPrerequisites`，**直接洞**）——`t ↦ ∫⁻_{u=t} g dℋ^{n-1}` 对 Lebesgue 测度
   `AEMeasurable`。它是第 1 条右端有意义的前提，是独立的一块。
3. **Sard**：`Analysis.sard`（`WIP/AnalyticPrerequisites`，**直接洞**）——`C^n` 实值函数的临界值
   Lebesgue 零测，`C^n` 是目标维数为一时的锐正则性。
   `Analysis.ae_forall_fderiv_ne_zero` 是**已填体**，但通过 `sard` 继承 `sorryAx`。
4. **从 Sard 到光滑超水平集的封装**：`SmoothDomain.ae_exists_superlevel`
   （`WIP/CheegerInfimum`，**仍是直接洞，不是已填体**）。
5. **最终组装**：`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
   （`C¹` 特化，直接洞）、`smoothConstant_mul_lintegral_min_superlevel_le`（直接洞）与
   `smoothConstant_le_minkowskiConstant`（直接洞）。

其中第 1、2、3 条是真正的大块分析基础设施，Mathlib 没有现成结论。第 5 条的第一项只是把第 1 条
特化到 `C¹`，做完也只会把一个直接洞换成一个继承 `sorryAx` 的填体，对真实缺口没有帮助。

### 选定的最小后续目标：`SmoothDomain.ae_exists_superlevel`

边界最清楚、又确实推进结构的是第 4 条。当前声明（在 `KLS/WIP/CheegerInfimum.lean`，本轮未改动）：

```
theorem ae_exists_superlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x}
```

**它现在是直接洞，不是已填体。** 做完之后它会变成填体，并通过 `Analysis.sard` 继承 `sorryAx`——
所以它消去的是“Sard 到光滑区域的封装”这一处结构缺口，**不**消去 Sard 本身，也不会让任何下游结论
摆脱 `sorryAx`。直接洞会从 12 降到 11（3／3／5）。

依赖与路线（`SmoothDomain` 的字段见 `KLS/Geometry/SmoothDomain.lean`）：

* 取 `carrier = {x | t < u x}`，`isOpen` 由 `isOpen_lt continuous_const hu.continuous`。
* `exists_defining`：对 `x ∈ frontier carrier`，已证明的 `SmoothDomain.frontier_superlevel_subset`
  （`WIP/CheegerInfimum`，无洞）给 `u x = t`。
* 正则性：`Analysis.ae_forall_fderiv_ne_zero` 需要 `ContDiff ℝ (Module.finrank ℝ V) u`，
  由 `hu.of_le` 从 `ContDiff ℝ ∞ u` 降阶；注意侧条件是
  `(Module.finrank ℝ V : WithTop ℕ∞) ≤ ∞`，**`∞` 不是该类型的 `⊤`（`ω` 才是）**，
  与上一轮 `ContDiff.of_le` 的坑相同。由它得 `fderiv ℝ u x ≠ 0`。
* 取 `W = {y | fderiv ℝ u y ≠ 0}`，它是开集：`hu.continuous_fderiv` 给出 `y ↦ fderiv ℝ u y` 连续，
  `W` 是 `{0}ᶜ` 的原像。`x ∈ W` 由上一条。
* 取 `φ = fun y ↦ t - u y`，`ContDiff ℝ ∞ φ` 由 `contDiff_const.sub hu`；
  `fderiv_const_sub` 给 `fderiv ℝ φ y = -fderiv ℝ u y`，`neg_ne_zero` 给 `W` 上非零；
  `carrier ∩ W = {y ∈ W | φ y < 0}` 因为 `t - u y < 0 ↔ t < u y`，是纯粹的集合改写。
* 最后 `ae_forall_fderiv_ne_zero` 的 `∀ᵐ t` 与上述构造用 `filter_upwards` 合起来。

完成后 `WIP/CheegerInfimum` 只剩 coarea 的 `C¹` 特化与两条组装；真正阻塞反方向的仍然是第 1、2、3
条。在它们完成之前，`smoothConstant_le_minkowskiConstant`、`minkowskiConstant_eq_smoothConstant`、
`constant_eq_smoothConstant_intrinsic` 与 `inverseScale_eq_inv_smoothConstant_intrinsic`
都继续传递依赖 `sorryAx`，不能表述为反方向比较、Cheeger 常数相等或整条链已证。
