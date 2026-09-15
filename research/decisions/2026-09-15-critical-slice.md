# C¹ 函数临界部分的截面零测（L10）

2026-09-15。本轮**证明了加权 coarea 路线的 L10**：`C¹` 实函数的临界集与几乎每个水平集的交
具有零 `surfaceMeasure`。这是 L1 的第一个真正下游消费者。不提交、不推送、不改历史决定。
起始 HEAD 为 `2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260915T035117.865459Z/report.json`（与 `build/verification/latest.json`
逐字节相同），重新计算的完整快照与回执相等：424 个文件，SHA256
`2fb5014b1bbfb1bbd8b05a41cbc7a5e45529fc97783da9305036597d7be7ce9d`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 本轮证明的内容

新模块 `formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean`：

```lean
theorem FunctionalInequalities.KLS.isClosed_critical {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    IsClosed {x : V | fderiv ℝ u x = 0}

theorem FunctionalInequalities.KLS.exists_lipschitzOnWith_critical_cover
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧ (∀ n, MeasurableSet (T n)) ∧
      {x : V | fderiv ℝ u x = 0} ⊆ ⋃ n, T n ∧
      ∀ n, LipschitzOnWith ε u ({x : V | fderiv ℝ u x = 0} ∩ T n)

theorem FunctionalInequalities.KLS.ae_surfaceMeasure_critical_ball_eq_zero
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) (R : ℕ) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ Metric.closedBall 0 R ∩ {x | u x = t}) = 0

theorem FunctionalInequalities.KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0
```

与路线记录的 L10 相比只去掉了从未使用的 `[CompleteSpace V]`，没有增加任何假设：
`u` **不要求** Lipschitz、有界或紧支撑；临界集**不要求**可测（它自动是闭集）；
`V` 允许零维。客户端 `target` 用带 `[CompleteSpace V]` 的原语句逐字复述并证明。

## 这不是 Sard 定理

**必须分清两件事**，本轮只做了后者：

* **Sard**：临界**值**集 `u '' {fderiv = 0}` 在 `ℝ` 中 Lebesgue 零测。一般需要 `C^(finrank)`
  正则性，在本仓库仍是直接洞 `Analysis.sard`（本轮未动、无下游消费者、仍带 `sorryAx`）。
* **L10**：每个水平集中**临界那一部分**的余维一测度为零，几乎每个水平成立。对**仅 `C¹`** 的
  函数在任意维数都成立。

L10 **不蕴含** Sard：一个 `C¹` 函数完全可以有正测度的临界值集，L10 对此没有任何断言，
只说那些水平上临界部分的 `ℋ^{n-1}` 测度是零。客户端的 `constant_exceptional_level` 把区别
做成具体计算：常数函数的临界集是全空间，故它在所取到的那个水平上的截面就是整条直线，
`surfaceMeasure ℝ ≠ 0`。所以 L10 的"几乎处处"不能加强成"处处"，临界集本身也不带任何小性。

## 证明设计

**L1 的第一个真正下游消费者。** 临界集上导数为零，而 Mathlib 的
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 的逼近线性映射取自导数的值
（其结论的最后一条给出 `∃ y ∈ s, A n = f' y`），所以在临界集上这些线性映射**全为零**，
`ApproximatesLinearOn u 0 (C ∩ T n) ε` 就直接是 `LipschitzOnWith ε u (C ∩ T n)`。
该引理同时给出**两两不交的可测**分片，所以不需要再做 `disjointed`。

固定球半径 `R` 与尺度 `ε = (k+1)⁻¹`：

1. 取上述分片，令 `D n := C ∩ closedBall 0 R ∩ T n`（可测、两两不交、并为 `C ∩ ball`）。
2. 对每个 `D n` 用 **L1**（`KLS.exists_measurable_majorant`）得可测支配函数 `F n`，
   `∫⁻ F n ≤ eilenbergConstant V · ε · volume (D n)`。
3. `G k := fun t ↦ ∑' n, F n t` 可测（`ENNReal.tsum_eq_iSup_sum` 加有限和可测性），
   由可数次可加性支配 `C ∩ ball ∩ {u = t}` 的截面测度；由 `lintegral_tsum`、
   `ENNReal.tsum_mul_left` 与不交可测集的 `measure_iUnion`，
   `∫⁻ G k ≤ eilenbergConstant V · volume (closedBall 0 R) · (k+1)⁻¹`。
4. `H := fun t ↦ ⨅ k, G k t` 仍可测、仍支配，且 `∫⁻ H ≤ ∫⁻ G k` 对每个 `k` 成立；
   右端趋于 `0`（`volume (closedBall 0 R) < ∞` 是关键，所以**必须**先局部化到球），
   由 `ge_of_tendsto'` 得 `∫⁻ H = 0`，再由 `lintegral_eq_zero_iff` 得 `H = 0` 几乎处处。
5. 对 `R` 取可数并（`Metric.iUnion_closedBall_nat`）去掉球：`ae_all_iff` 加
   `measure_iUnion_null`。

**没有循环论证**：可测性只用在构造出来的支配函数上，临界截面函数本身的可测性从未被假设
（L3/L4 也未被使用——临界集是闭集但不紧，球内的交才是紧的，而这里不需要紧性）。

## 本轮没有做的事

* **没有证明 Sard**：尖锐 `C^(finrank)` 的 `Analysis.sard` 与
  `Analysis.ae_forall_fderiv_ne_zero` 仍带 `sorryAx`，仍是直接洞。
* **没有证明 L8/L9/L11**：正则部分的 C¹ coarea（L9）、开域带权图面积（L8）与
  一般 C¹ 带权 coarea（L11）都未动。L10 只处理**临界**部分，把正则部分留给 L9。
* **加权 coarea 等式仍是直接洞**：`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  与 `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`。
  直接洞按预期仍为 **2/3/5，总数 10**。
* `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等仍未证明。
* Eilenberg 常数的尖锐性仍未证明。

## 验证

* `KLS/Geometry/CriticalSlice.lean` 以 `-DwarningAsError=true` 单独编译通过。
* `build/audit/CriticalSliceAudit.lean` 以 `-DwarningAsError=true` 编译通过：1 条语句 `#check`
  （逐字复述路线记录的 L10）与 7 条定理——`target`、`target_of_not_completeSpace`、
  `ae_slice_eq_regular`（L11 将消费的形式：几乎每个截面可以先丢掉临界集再算）、
  `surfaceMeasure_real_singleton`、`constant_exceptional_level`（例外水平的截面测度非零）、
  `not_lipschitz`（`Real.exp`，`C¹` 但非全局 Lipschitz）、一条 `preserved_*` 具名参数签名
  检查——以及 11 条 `#print axioms`。全部 11 个声明只依赖 `propext`、`Classical.choice`、
  `Quot.sound`，**无 `sorryAx`**。
* 重跑 `LevelSetMeasurableAudit`、`BorelSliceAudit`、`CompactSliceAudit`、
  `EilenbergMajorantAudit`、`NullSlicingAudit`、`WeightedCoareaRouteStatements`、
  `WeightedCoareaInfrastructure`、`AreaFormulaAudit`、`CheegerInfimumAudit`、
  `MinkowskiConstantAudit`、`SuperlevelSardScope`、`SmoothSardAudit`、
  `SmoothSardRouteStatements`，全部严格编译通过，未作任何修改；`LevelSetMeasurableAudit`
  再次确认迁出的结果无 `sorryAx` 而加权 coarea 等式与 `Analysis.sard` 仍带 `sorryAx`。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **2/3/5，总数 10**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-critical-slice.json`，最终核对另存
  `build/audit/critical-final-snapshot.json`。`build/` 被 gitignore，故 `build/audit`
  的哈希由证据 JSON 单独绑定。
* 证书仍 **24**，perimeter infrastructure 仍 **missing**。
