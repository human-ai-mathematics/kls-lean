# 正则超水平集的光滑域构造与 Sard 接口封装

日期：2026-09-14。承接 [距离截断的梯度积分估计](2026-09-13-distance-cutoff-gradient-integral.md)。
起始 HEAD 仍为 `2965b32`；开始时 `build/verification/latest.json`（passed）的 383 个文件条目与
工作区快照逐字匹配（`snapshot.sha256` 相同，`head` 相同）。保留此前未提交与未跟踪成果，
本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

本轮把 `KLS.SmoothDomain.ae_exists_superlevel` 从**直接洞**变成**填体**，声明文本逐字不变：

```
theorem ae_exists_superlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x}
```

这是**正则值到光滑域的几何构造，加 Sard 接口封装**，**不是证明 Sard**。必须分开记：

* 新增的 `KLS.SmoothDomain.ofSuperlevel`（含 `ofSuperlevel_carrier`）在无洞几何模块
  `KLS/Geometry/SmoothDomain.lean` 中，`#print axioms` 只有
  `propext / Classical.choice / Quot.sound`，**无 `sorryAx`**。
* `ae_exists_superlevel` 虽已填体，但通过 `Analysis.ae_forall_fderiv_ne_zero` 继承
  `Analysis.sard` 的 `sorryAx`，**不得列入无 `sorryAx` 清单**。它关掉的只是“Sard 到光滑区域”
  这一处结构封装缺口，`Analysis.sard` 本身仍是直接洞，下游没有任何结论因此摆脱 `sorryAx`。

数学范围保持原声明：任意有限维实内积空间，**含零维**；任意全空间 `C∞` 实函数；
**严格**超水平集 `{x | t < u x}`。没有增加正维数、紧支撑、有界性、超水平集非空、
水平集整体正则或边界紧致等任何假设。

## 无洞的几何构造

`SmoothDomain.ofSuperlevel` 取的是结构真正需要的**最弱自然条件**：只要求
`∀ x ∈ frontier {x | t < u x}, fderiv ℝ u x ≠ 0`，**不**要求整条水平集 `{x | u x = t}` 正则，
更不要求全空间非零。字段逐条核对：

* `carrier := {x | t < u x}`，`isOpen := isOpen_lt continuous_const hu.continuous`。
* `exists_defining`：在边界点 `x` 取 `W = {y | fderiv ℝ u y ≠ 0}`，它是 `{0}ᶜ` 在连续映射
  `y ↦ fderiv ℝ u y` 下的原像（`hu.continuous_fderiv`），故为开集；`x ∈ W` 正是假设。
* 定义函数按结构的**负子水平**约定取 `φ = fun y ↦ t - u y`，`contDiff_const.sub hu` 给光滑性；
  `fderiv_const_sub` 给 `fderiv ℝ φ y = -fderiv ℝ u y`（Mathlib 的这条无可微性假设），
  `neg_ne_zero` 给 `W` 上非零。
* `carrier ∩ W = {y ∈ W | φ y < 0}` 是纯集合改写：`t - u y < 0 ↔ t < u y`（`sub_neg`）。

**边界与水平集没有混同。** 构造只在 `frontier {t < u}` 的点上要正则性；空边界、空载体、
全载体与零维都由构造自然覆盖，没有为它们添加假设或分支：这三种情形下边界为空，
`exists_defining` 的前提为假，构造照常给出光滑域。

构造放在 `KLS/Geometry/SmoothDomain.lean`（结构与其余构造器 `empty`、`univ`、`homothety`
的所在模块），只用到该模块已有的 `NormedAddCommGroup` + `NormedSpace ℝ` 上下文：
不需要完备性、测度结构或有限维，也没有引入任何流形框架。该模块不导入
`WIP/AnalyticPrerequisites`，也不依赖任何带 `sorryAx` 的声明。

## WIP 层的封装

`KLS/WIP/CheegerInfimum.lean` 保留 `ae_exists_superlevel`，证明是两行：

```
filter_upwards [Analysis.ae_forall_fderiv_ne_zero (hu.of_le ENat.LEInfty.out)] with t ht
exact ⟨ofSuperlevel hu fun x hx ↦ ht x (frontier_superlevel_subset hu.continuous t hx), rfl⟩
```

* 降阶的侧条件是 `(Module.finrank ℝ V : WithTop ℕ∞) ≤ ∞`。**`le_top` 不适用**（该类型的 `⊤` 是
  `ω` 而不是 `∞`），`by simp` 也不成立（实测 “`simp` made no progress”）；成立的是
  `ENat.LEInfty.out`。这以实际编译结果为准，记录下来以免下一轮重蹈。
* 正则值条件没有外泄成新的外部假设：`ht` 只在证明体内部使用，签名不变。
* 没有引入新公理、新类型类假设或“已认证”黑箱；`Analysis.sard` 原样不动。

该文件新增一行 `import FunctionalInequalities.KLS.WIP.AnalyticPrerequisites`——此前没有任何模块
导入它，`Analysis.ae_forall_fderiv_ne_zero` 因而不在作用域内。这是 WIP → WIP 的边，
无洞基础层不受影响。

## 迁移与排序

* **没有**模块迁移。`frontier_superlevel_subset` 仍留在 `KLS/WIP/CheegerInfimum.lean`：
  它的唯一消费者就是同文件的 `ae_exists_superlevel`，而无洞构造采用边界形式的假设后
  **不需要**它，所以按实际消费者最小化处理，不下移、不复制、不留兼容别名。
* 唯一的改动是**同文件内的顺序**：`frontier_superlevel_subset` 移到 `ae_exists_superlevel`
  之前（此前在其后，导致 `Unknown identifier`）。`omit ... in` 前缀随声明一起移动，
  作用域不变。
* `ae_exists_superlevel` 填体后 `unusedSectionVars` 会报 `CompleteSpace`、`MeasurableSpace`、
  `BorelSpace`、`SecondCountableTopology` 未用（`sorry` 体不受该 linter 检查，所以此前没有警告）。
  **没有**用 `omit` 收窄签名——那会改接口；只对这一条声明叠加
  `set_option linter.unusedSectionVars false in` 并在注释里写明原因，没有全文件关闭。

## 验证

* `ofSuperlevel`、`ofSuperlevel_carrier` 与 `frontier_superlevel_subset` 的 `#print axioms`
  只含标准三条公理。
* `ae_exists_superlevel` 与其客户端的 `#print axioms` 含 `sorryAx`，与
  `Analysis.ae_forall_fderiv_ne_zero`、`Analysis.sard` 一致；证据见
  `build/audit/superlevel-sard-scope.log`。
* `Geometry/SmoothDomain.lean` 与新的独立客户端 `build/audit/SuperlevelDomainAudit.lean`
  以 `lake env lean -DwarningAsError=true` 通过（`build/audit/superlevel-domain-audit-strict.log`），
  客户端 8 条公理报告全部只含标准三条公理，覆盖：只要求边界正则的一般情形；
  定义函数的**符号方向**（`{t < u}` 而非 `{u < t}`，域在 `W` 内恰为 `{φ < 0}`）；
  **整条水平集临界**而边界为空的情形（常值函数、`t = 0`，`fderiv` 处处为零，载体为空）；
  全载体（同样处处临界）；零维；以及带显式“载体无界”“边界无界”假设的非零线性泛函半空间。
* 迁移前后 `set_option pp.all true` 的 `#check` 输出对 `ae_exists_superlevel` 与
  `frontier_superlevel_subset` 逐字节 `diff` 为空
  （`build/audit/superlevel-signature-{before,after}.log`），section 变量与接口未变。
* `KLS/WIP/CheegerInfimum.lean` 实际普通模式重编译，诊断恰为 **3 个直接洞**，无其他诊断
  （`build/audit/superlevel-wip-cheegerinfimum.log`）。直接洞总数由 **12** 降到 **11**：
  AnalyticPrerequisites **3**、CheegerInfimum **3**、Energy/WIP/Cheeger **5**。
  **这不代表 Sard 或其任何传递依赖已经消除。**
* 受影响的既有客户端重跑：`BoundaryChartAudit`、`CheegerInfimumAudit`、`CutoffRouteReview`、
  `DilationAudit`、`DistanceCutoffAudit`、`GaussGreenAudit`、`MinkowskiCoareaAudit`、
  `MinkowskiConstantAudit`、`MollifiedBoundaryScope`、`PerimeterInterfaceAudit`、`RecoveryAudit`、
  `SubgraphDivergenceAudit` 全部严格模式通过，公理报告不含 `sorryAx`。
  `build/audit/AreaFormulaAudit.lean` 仍然编译失败，原因是它引用的 `Analysis.divergence`
  在更早一轮迁到 `Analysis/Divergence.lean` 而该客户端没有导入它——这是**此前就存在**的陈旧
  审计脚本，与本轮改动无关（本轮只新增声明，不可能造成 `Unknown identifier`），
  本轮不改写它。
* 默认 `lake build` 通过，随后从根目录 `python3 research/verify.py`；最终源码回执为
  `build/verification/latest.json`。
* 正式证书仍为 **24**，周长基础设施仍为 `missing`。本轮**不**登记 Sard 已证、
  两个 Cheeger 常数相等或整条比较链已证。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 反方向剩余依赖：实际声明与分类

1. **加权 coarea**：`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
   （`WIP/AnalyticPrerequisites`，**直接洞**）
   ```
   theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet {u : V → ℝ} {K : ℝ≥0}
       (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
       ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
         ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ)
   ```
   Mathlib **没有**任何 coarea 公式（`grep -rl coarea Mathlib/` 为空）。这是独立的大块分析基础设施。
2. **水平集积分的可测性**：`Analysis.aemeasurable_lintegral_levelSet`
   （`WIP/AnalyticPrerequisites`，**独立的直接洞**）——`t ↦ ∫⁻_{u=t} g dℋ^{n-1}` 对 Lebesgue
   测度 `AEMeasurable`。它是第 1 条右端有意义的前提，通常与 coarea 的构造一起得到，
   单独证明**不是封装工作**。
3. **Sard**：`Analysis.sard`（`WIP/AnalyticPrerequisites`，**直接洞**）
   ```
   theorem sard {u : V → ℝ} (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
       (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0
   ```
   Mathlib 只有两类相关结论，**都不蕴含**本条：`Mathlib/MeasureTheory/Function/Jacobian.lean`
   的 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` 是**同维**（`E → E`）的 Sard 引理；
   `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` 的
   `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` 只给补集稠密，不给零测，且条件是
   定义域维数小于目标维数。目标维数为一的 Morse–Sard（`C^n` 锐正则性）需要按维数归纳、
   Taylor 余项在小立方体上的估计与覆盖论证，Mathlib 无现成基础。
4. **最终组装**：`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（第 1 条的
   `C¹` 特化，直接洞——做完只会把直接洞换成继承 `sorryAx` 的填体）、
   `smoothConstant_mul_lintegral_min_superlevel_le` 与 `smoothConstant_le_minkowskiConstant`
   （均为直接洞，都要先有第 1、2 条）。

其中第 1、2、3 条是真正的独立分析难点；第 4 条在它们之前只能做成封装。

### 选定的下一个目标：Sard 的低维基础情形

建议的下一个边界明确目标是新增**无洞**引理
`Analysis.sard_of_finrank_le_one`（暂定名，放在 `Analysis/` 层）：当 `Module.finrank ℝ V ≤ 1` 时
`volume (u '' {x | fderiv ℝ u x = 0}) = 0`。

* **可复用基础（已确认存在于 Mathlib）**：`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
  给同维可微映射在“微分不可逆”集合上的像零测；`LinearIsometryEquiv.measurePreserving`
  （`Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`）给等距同构的测度保持。
* **需要新增的数学**：把 `u : V → ℝ` 沿 `V ≃ₗᵢ[ℝ] ℝ`（维数一）转成 `ℝ → ℝ`，
  并证明一维时 `(fderiv ℝ u x).det = 0 ↔ fderiv ℝ u x = 0`；零维情形单独一支
  （像至多一点，故零测）。
* **它不是什么**：这是一般 Morse–Sard 按维数归纳的**基础情形**，**不**给出任意 `n` 的 Sard，
  因此**不会**填 `Analysis.sard`，也不会让 `ae_exists_superlevel` 或任何下游结论摆脱 `sorryAx`。
  在真正证出一般情形之前，`smoothConstant_le_minkowskiConstant`、
  `minkowskiConstant_eq_smoothConstant`、`constant_eq_smoothConstant_intrinsic` 与
  `inverseScale_eq_inv_smoothConstant_intrinsic` 继续传递依赖 `sorryAx`，
  不能表述为反方向比较、Cheeger 常数相等或整条链已证。
