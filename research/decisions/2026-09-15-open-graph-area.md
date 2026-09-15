# 开域带权图面积（L8）

2026-09-15。本轮**证明了加权 coarea 路线的 L8**：带权图面积换元从"参数函数全局 `C¹`"
放宽到"只在开集 `O` 上 `C¹`"。不提交、不推送、不改历史决定。起始 HEAD 为
`2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260915T040555.802878Z/report.json`（与 `build/verification/latest.json`
逐字节相同），重新计算的完整快照与回执相等：427 个文件，SHA256
`61aec2ce1f3db09ecea5c80d51f2c06567fd23f52d55faf4b860434a92cc3b2b`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 本轮证明的内容

新模块 `formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean`：

```lean
/-- C¹ 局部延拓：开集上 C¹ 的函数在每点的某个球上与某个全局 C¹ 函数相等 -/
theorem FunctionalInequalities.Analysis.exists_contDiff_one_eqOn_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) (hz : z ∈ O) :
    ∃ (ρ : ℝ) (w : E → F), 0 < ρ ∧ Metric.ball z ρ ⊆ O ∧ ContDiff ℝ 1 w ∧
      Set.EqOn w f (Metric.ball z ρ)

/-- 无平移的带权换元（既有 `setLIntegral_image_graphChartMap` 的 `x₀ = 0` 特例） -/
theorem FunctionalInequalities.Analysis.setLIntegral_image_graphMap …

/-- L8 -/
theorem FunctionalInequalities.Analysis.setLIntegral_image_graphMap_of_contDiffOn
    (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1) (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ))
    {O S : Set H} {v : H → ℝ} {f : V → ℝ≥0∞}
    (hO : IsOpen O) (hv : ContDiffOn ℝ 1 v O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hf : Measurable f) :
    ∫⁻ x in graphMap ι e v '' S, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H)
```

与路线记录的 L8 完全一致（只把结论里的权重变量名写作 `f`），没有增加任何假设：
`S` 不要求有界或有限测度，权重不要求可积、有界或有限（允许恒为 `⊤`），
`v` 在 `O` 外没有任何正则性要求，`O = ∅` 与 `S = ∅` 都被覆盖。
客户端 `target` 用路线原语句逐字复述并证明。

## 为什么必须做可数局部化

**开集上 `ContDiffOn` 的函数一般不能延拓成全局 `C¹` 函数**：`x ↦ x⁻¹` 在 `(0, ∞)` 上是
标准反例。所以不能"先延拓再用既有全局定理"一步做完。真正成立的是
`exists_contDiff_one_eqOn_ball`：每点有一个球，球上与某个全局 `C¹` 函数相等
（乘以支撑在 `O` 内的 `ContDiffBump`，可微性是局部性质）。这是路线记录要求的
**开集内部局部化**；它**不是**闭集上的 Whitney 延拓——那是独立的未证明义务 **L6**，本轮未动。

装配：第二可数性从上述球族取出可数子族覆盖 `O`；`disjointed` 把它变成 `S` 的可数两两不交
可测分片；`graphMap` 单射（既有 `graphMap_injective`）使各分片的像两两不交，
既有 `measurableSet_image_graphMap` 给出像可测；等式两边都对这些分片可数可加
（`lintegral_iUnion`），每片上用既有全局定理作用于该片的局部代表；
梯度相等是因为两函数在每点周围的**开**球上相等（`Filter.EventuallyEq.gradient_eq`）。

`Analysis/SmoothSard.lean` 已有 `C^∞` 版本 `exists_contDiff_eventuallyEq`（结论是某点附近的
`EventuallyEq`，不给出显式球）。**本轮刻意不动它**：把它推广到一般阶数或加强结论都会改变
一条已发表的签名，所以这里单独证明所需的 `C¹` 版本。客户端的
`preserved_setLIntegral_image_graphChartMap` 以具名参数确认既有全局定理的语句未变。

## 本轮没有做的事

* **L9（正则开域 C¹ coarea）未证明**：还需要**带水平参数 `t` 的** C¹ 隐函数族
  （不是固定单个水平的图包含关系）、同维 Jacobian 换元与 Tonelli，并算出
  `|det DΦ| = |Du(e)|` 与 `√(1+‖D_yψ‖²) = ‖∇u‖/|Du(e)|` 两边相消。L8 只给**图**的面积，
  不给 coarea。
* **L11、L12 未证明**；**加权 coarea 等式仍是直接洞**
  （`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 及其 `C¹` 特化）。
  直接洞按预期仍为 **2/3/5，总数 10**。
* **L6/L6a/L7 的 Whitney 延拓未动**。本轮的局部化只在开集内部，用 bump 即可，
  不涉及闭集上的一阶 jet 延拓。
* 尖锐 `C^(finrank)` 的 `Analysis.sard` 仍带 `sorryAx`；
  `smoothConstant_le_minkowskiConstant`、`smoothConstant_mul_lintegral_min_superlevel_le`、
  两个 Cheeger 常数相等、Eilenberg 常数的尖锐性均仍未证明。

## 验证

* `Analysis/OpenGraphIntegral.lean` 以 `-DwarningAsError=true` 单独编译通过。
* `build/audit/OpenGraphAudit.lean` 以 `-DwarningAsError=true` 编译通过：1 条语句 `#check`
  （逐字复述路线记录的 L8）与 6 条定理——`target`、`global_case`（取 `O = univ` 复得既有全局
  定理，说明 L8 是真推广）、`top_weight`（权重恒为 `⊤`）、`empty_parameter_set`、
  `inv_on_Ioi`（`x ↦ x⁻¹` 于 `(0, ∞)`，**无全局 `C¹` 延拓**，既有全局定理覆盖不到）、
  一条 `preserved_*` 具名参数签名检查——以及 9 条 `#print axioms`。
  全部 9 个声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
* 重跑 `CriticalSliceAudit`、`LevelSetMeasurableAudit`、`BorelSliceAudit`、
  `CompactSliceAudit`、`EilenbergMajorantAudit`、`NullSlicingAudit`、
  `WeightedCoareaRouteStatements`、`WeightedCoareaInfrastructure`、`AreaFormulaAudit`、
  `CheegerInfimumAudit`、`MinkowskiConstantAudit`、`SuperlevelSardScope`、`SmoothSardAudit`、
  `SmoothSardRouteStatements`，全部严格编译通过，未作任何修改。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **2/3/5，总数 10**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-open-graph-area.json`，最终核对另存
  `build/audit/opengraph-final-snapshot.json`。`build/` 被 gitignore，故 `build/audit`
  的哈希由证据 JSON 单独绑定。
* 证书仍 **24**，perimeter infrastructure 仍 **missing**。
