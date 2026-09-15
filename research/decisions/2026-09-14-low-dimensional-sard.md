# Sard 的零维与一维基础情形，以及旧路线勘误

日期：2026-09-14。HEAD `2965b32bc79bdb24921c633df12102450eaedcc4`。
起始独立回执 `build/verification/20260913T182956.860385Z/report.json` 为 passed；
重新计算确认其全部 384 个文件、HEAD 与快照完全一致，快照 SHA256 为
`5da779982b20637487bfaf6fbb8aa98ea7c1671485373d9aae6c4b4204077817`。
全部未提交及未跟踪成果保留；本轮不提交、不推送。历史决定不改写。

## 已完成的独立定理

新模块 `formalization/FunctionalInequalities/Analysis/Sard.lean` 中：

```lean
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem sard_of_finrank_le_one {u : V → ℝ}
    (hdim : Module.finrank ℝ V ≤ 1)
    (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0
```

完整命名为 `FunctionalInequalities.Analysis.sard_of_finrank_le_one`。
只有 `propext / Classical.choice / Quot.sound`，无直接洞或传递 `sorryAx`。
没有新增辅助公开定理，没有复制 Mathlib 的零导数像集结论。
模块仅导入 Mathlib 的 Jacobian、ContDiff.Basic、FiniteDimension；本地导入闭包为空，
不导入 KLS 或 WIP，没有迁移、兼容别名或证书聚合导入变更。

* 零维：`Module.finrank_zero_iff` 给 `Subsingleton V`；任意子集在 `u` 下的像都包含在
  单点 `{u 0}` 内，由 `measure_mono_null` 得零测。这一分支没有用 `hu` 推出可微性，
  不额外要求 C¹，甚至其像集论证适用于任意函数。
* 一维：`ContinuousLinearEquiv.ofFinrankEq` 给 `e : ℝ ≃L[ℝ] V`。
  取 `f = u ∘ e`、`S = {z | fderiv ℝ u (e z) = 0}`。
  由 C¹ 得到 `u` 处处可微，再用链式法则给每个 `z ∈ S` 的
  `HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) z`。
  转为 within 导数，应用 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume`；
  指定零导数的行列式用 `simp`。最后用 `e.symm`/满射性给
  `f '' S = u '' {x | fderiv ℝ u x = 0}`。
* 测度始终是目标 ℝ 上的 Lebesgue 测度。不需要定义域的测度结构、内积、等距性、
  紧支撑、有界性或临界集／临界值像集可测性。结论确实是**临界值像集零测**。

## 对上一轮的勘误

[正则超水平集决定](2026-09-14-regular-superlevel-smooth-domain.md) 保留原文；其末段低维路线
由本决定取代。连续线性等价足够，不需要 `LinearIsometryEquiv.measurePreserving`。
原来的 `fderiv ℝ u x : V →L[ℝ] ℝ` 不是自映射，不能直接谈其行列式；本轮只在 ℝ → ℝ
的零导数上使用同维 Jacobian 定理，完全不需要“行列式零当且仅当导数零”辅助引理。

原 `build/audit/AreaFormulaAudit.lean` 已补上
`import FunctionalInequalities.Analysis.Divergence`；测试内容完整保留，没有关闭检查。
`WIP/CheegerInfimum.lean` 仅把 `ae_exists_superlevel` 的 docstring `u - t` 改为 `t - u`，
匹配构造实际采用的负子水平集约定；声明及证明未改。
HANDOFF、LEAN_DESIGN、两个当前 README、verification 和 tasks 的当前状态已更新。
旧的日期轮次不作为现状；历史决定未改写。

## 独立验证及边界

* 新模块与 `Analysis/AreaFormula`、`Analysis/Divergence`、`KLS/Geometry/SmoothDomain`
  均重新运行 `lake env lean -DwarningAsError=true`，无诊断。
* `build/audit/SardLowDimAudit.lean` 严格通过：7 个客户端和目标定理共 8 条报告，全部标准三公理。
  覆盖一般一维实赋范空间、`Fin 0 → ℝ` 上的任意函数、ℝ 上 C¹ 函数、常函数、平方函数，
  以及独立证明平方函数在零点临界且不是常函数。一般空间客户端没有内积或测度实例。
* 修复的 AreaFormulaAudit 严格通过，6 条报告全部标准三公理。
  另外重跑 SuperlevelDomainAudit、SuperlevelSardScope、SardBaseRouteReview、BoundaryChartAudit、
  CheegerInfimumAudit、CutoffRouteReview、DilationAudit、DistanceCutoffAudit、GaussGreenAudit、
  MinkowskiCoareaAudit、MinkowskiConstantAudit、MollifiedBoundaryScope、PerimeterInterfaceAudit、
  RecoveryAudit、SubgraphDivergenceAudit；合计 16 个既有客户端全都严格通过。
* SuperlevelSardScope 分别报告 `Analysis.sard`、`Analysis.ae_forall_fderiv_ne_zero`、
  `SmoothDomain.ae_exists_superlevel` 的公理；**三者都仍含 `sorryAx`**。
  `frontier_superlevel_subset` 仍只有标准三公理。
* 三个 WIP 文件逐个实际普通模式编译，只有 **3 / 3 / 5** 个直接洞警告，无其他诊断。
  低维新增结果没有消去原来的 **11** 个洞。
* 默认 `lake build` 已通过（3393 jobs）。根目录 `python3 research/verify.py` 的最终结果以
  `build/verification/latest.json` 为准；验证后另行比对所有最终文件和新增模块的重放范围。
  审计客户端位于忽略的 build 目录，不冒充正式证书；其源文件和日志的哈希留在
  `research/explorations/2026-09-14-sard-low-dimensional-audit.json`。
* 正式证书仍为 **24**；周长 infrastructure 仍为 **missing**。
  一般 Sard、加权 coarea、水平集积分可测性、反方向 `h_S ≤ h_M`、Cheeger 常数相等
  与整条比较链均未证明。本地验证不代表远程 CI。

## 与一般 Sard 之间仍有什么缺口

现有工具已经提供链式法则、连续／高阶导数、逆／隐函数、二可数空间的可数邻域子覆盖。
Mathlib `Analysis/Calculus/TaylorIntegral.lean` **已有多维**
`map_add_eq_sum_add_integral_iteratedFDeriv`，不能把多维 Taylor 本身列为完全缺失。
`ContDiff.continuous_iteratedFDeriv` 给高阶导数连续性；
`Topology/Bases.lean` 的 `countable_cover_nhdsWithin` 给可数覆盖工具。
本仓库 `Analysis/ImplicitGraph.lean` 的现有几何接口面向 C∞ 正则水平集，
不能不加论证地当作仅 C^n 临界分层所需的全部有限阶接口。

仍需构造并控制 `C_j = {x | D^k u(x)=0, 1≤k≤j}` 的层次：

1. 对非平坦部分 `C_j \ C_{j+1}`，由某个 j 阶导数分量的一阶导数非零构造局部超曲面，
   将临界值问题降到低一维，随后作可数拼接。**必须追踪正则性损失**：
   从 C^n 函数的 j 阶导数得到的图表通常仅 C^(n-j)，当 j>1 时不够直接对
   `u ∘ chart` 套用要求 C^(n-1) 的归纳假设。高阶平坦性下的粗糙复合／延拓论证
   （或能避开该损失的替代论证）仍需建立；有隐函数定理不等于已完成下降。
2. 对最终平坦部分 C_n，从 Taylor 工具导出在紧集上**一致**的 o(r^n) 振幅控制，
   再和 O(r^(-n)) 个小块的有限覆盖计数结合，用目标区间的长度控制外测度，
   最后可数穷尽。现有可数覆盖 API 本身不提供这个定量零测论证。

因此不能由低维结果和“有归纳路线”推断一般 Sard 的证明基础已经闭合。

### 最小下一引理：平坦点的一致二阶余项（尚未证明）

建议先做独立的 `Analysis.exists_uniform_quadratic_remainder`（命名待实际 API 搜索）。
假设一般有限维实赋范空间 V、`u : V → ℝ` 为 C²、`K : Set V` 紧。
精确结论为：

```lean
∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x ∈ K, fderiv ℝ u x = 0 → iteratedFDeriv ℝ 2 u x = 0 →
    ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ 2
```

没有要求 K 所有点平坦；量词对 K 中满足两个零导数条件的 x 统一使用同一个 δ。
y 不必属于 K。空 K、零维及 y=x 都包括在内；没有定义域测度或内积假设。
`build/audit/SardNextStatement.lean` **仅严格检查此命题的类型**和已有 Taylor API，
没有声明已证明的定理，不使用 `sorry` 或公理占位。

可从 C² 的积分型 Taylor（取一阶多项式、二阶余项）、二阶导数在 K 邻域的一致控制
和线段积分估计证明，不需要任何 WIP 结果。它是二维平坦层覆盖论证所需的独立估计，
**本身尚不给临界值零测**，也不解决非平坦层下降或一般维数。
