# Borel 集截面与可测权重（L4、L5，以及目标 T1 的语句）

2026-09-15。本轮**证明了加权 coarea 路线的 L4 与 L5**，并由此在审计客户端里**证明了第一个
原始目标 T1 的完整语句**——即 WIP 直接洞 `Analysis.aemeasurable_lintegral_levelSet` 的语句。
**没有修改任何 WIP 文件**：把该声明迁出 WIP 是单独的决定，所以直接洞数不变，那个洞仍然是洞。
不提交、不推送、不改历史决定。起始 HEAD 为
`2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260915T024959.891644Z/report.json`（与 `build/verification/latest.json`
逐字节相同），重新计算的完整快照与回执相等：419 个文件，SHA256
`812dd3511f20a8d7260ee89a56db0a2a2a2c4dff4cb21c595cba1a509b3bdff9`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 本轮证明的内容

全部加在既有的 `formalization/FunctionalInequalities/KLS/Geometry/SurfaceSlicing.lean`，
没有新建模块，没有修改任何其他 `.lean` 文件。

```lean
/-- 内正则性分解 -/
theorem FunctionalInequalities.KLS.exists_isCompact_seq_volume_sdiff_eq_zero
    {S : Set V} (hS : MeasurableSet S) :
    ∃ C : ℕ → Set V, (∀ n, IsCompact (C n)) ∧ (∀ n, C n ⊆ S) ∧
      (volume : Measure V) (S \ ⋃ n, C n) = 0

/-- L4 -/
theorem FunctionalInequalities.KLS.aemeasurable_surfaceMeasure_inter_levelSet
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}
    (hc : Continuous u) (hu : LipschitzOnWith K u S) (hS : MeasurableSet S) :
    AEMeasurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) (volume : Measure ℝ)

/-- L5 -/
theorem FunctionalInequalities.KLS.aemeasurable_setLIntegral_inter_levelSet
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞}
    (hc : Continuous u) (hu : LipschitzOnWith K u S) (hS : MeasurableSet S)
    (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ)
```

与路线记录的 L4/L5 相比：去掉了从未使用的 `[CompleteSpace V]`，并把**全局** `LipschitzWith K u`
**减弱**为 `Continuous u` 加上**只在 `S` 上**的 `LipschitzOnWith K u S`，没有增加任何假设。
`S` 不要求有界、非空或有限体积；`g` 不要求有限值、可积或有界（允许 `g ≡ ⊤`）。
客户端 `target_L4`、`target_L5` 用带 `[CompleteSpace V]` 与全局 Lipschitz 的原语句逐字复述并
证明，`target_L4_of_lipschitzOnWith`、`target_L5_of_lipschitzOnWith` 证明减弱后的版本。

## 目标 T1 的语句已证明，但洞未填

客户端 `BorelSliceAudit.target_T1` 逐字复述并证明了

```lean
∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ)
```

这与 `KLS/WIP/AnalyticPrerequisites.lean` 里 `Analysis.aemeasurable_lintegral_levelSet` 的
语句相同（由 L5 取 `S = univ` 并化简 `Set.univ_inter` 得到）。**本轮没有动 WIP**：
按本仓库既有惯例（见 2026-09-15 的 superlevel 迁出决定），把声明迁出 WIP 并接线是**单独一轮**
的决定。因此：

* 直接洞仍为 **3/3/5，总数 11**；`Analysis.aemeasurable_lintegral_levelSet` 仍带 `sorry`。
* 不能说"第一个 coarea 洞已填"，只能说**它的语句已在无洞模块的基础上被证明**，迁出即可闭合。

## 证明设计

**L4 = L3（紧集）+ L2（零测余项）+ 内正则性，三者缺一不可。**

1. `exists_isCompact_seq_volume_sdiff_eq_zero`：对可测 `S`，用空间的紧穷竭
   `compactCovering V m` 把 `S` 切成有限体积的块（Haar 测度在紧集上有限），对每块用
   `MeasurableSet.exists_isCompact_isClosed_sdiff_lt` 取出误差 `< (k+1)⁻¹` 的紧子集，
   以 `Nat.unpair` 把二重族排成一列。无限体积由紧穷竭处理，不需要任何有限性假设。
2. 令 `A n := Set.accumulate C n`（有限并，故紧）。由 `measure_iUnion_eq_iSup_accumulate`
   （对**不必可测**的集合列也成立的下连续性），
   `surfaceMeasure V ((⋃ n, C n) ∩ {u = t}) = ⨆ n, surfaceMeasure V (A n ∩ {u = t})`，
   右端每项由 **L3** 可测（`A n` 紧、`u` 连续），故上确界可测。
3. 余项 `N := S \ ⋃ n, C n` 满足 `volume N = 0` 且 `LipschitzOnWith K u N`（由
   `hu.mono`），故 **L2** 给出：几乎每个 `t` 有 `surfaceMeasure V (N ∩ {u = t}) = 0`。
   在这样的 `t` 上，次可加性与单调性把 `surfaceMeasure V (S ∩ {u = t})` 夹成
   `⨆ n, surfaceMeasure V (A n ∩ {u = t})`。于是 L4 成立，且见证的可测函数是**显式**的。

**L5 = L4 + 简单函数逼近，不用任何参数积分定理。**
`lintegral_eq_iSup_eapprox_lintegral` 把 `∫⁻ y in S ∩ {u = t}, g` 写成简单函数积分的上确界；
每个简单函数的积分按 `SimpleFunc.lintegral` 展开成**有限和**
`∑ c ∈ range, c * surfaceMeasure V ((S ∩ s ⁻¹' {c}) ∩ {u = t})`，而 `S ∩ s ⁻¹' {c}` 可测，
`u` 在其上仍 Lipschitz，所以每项由 L4 是 AEMeasurable；有限和（`Finset.aemeasurable_sum`）
与可数上确界（`AEMeasurable.iSup`）保持 AEMeasurable。

**没有使用需要 `SFinite` 的参数积分定理。** 路线记录指出
`Measurable.lintegral_prod_right'` 要求内层测度 `SFinite`，而正维环境的余维一 Hausdorff 测度
不满足；本轮的论证完全绕开它，只用逐水平的有限和与单调极限。

**没有循环论证。** L4 的见证函数是由紧子集列构造出来的，其可测性来自 L3，不是假设来的；
L2 只用在体积零的余项上。

## 本轮没有做的事

* **没有修改 WIP**，所以 `Analysis.aemeasurable_lintegral_levelSet` 仍是直接洞，
  直接洞数仍为 11（3/3/5）。迁出与接线是下一轮的单独决定。
* **加权 coarea 等式本身（L6–L12 与目标 T2/T3）完全未动**：
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 与
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 仍是直接洞。
  L4/L5 只给可测性，**不给任何等式**。
* 尖锐 `C^(finrank)` 的 `Analysis.sard`（已无下游消费者）及
  `Analysis.ae_forall_fderiv_ne_zero` 仍带 `sorryAx`。
* `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等仍未证明。
* Eilenberg 常数的尖锐性仍未证明。
* 没有触及 L6/L6a/L7 的 Whitney 延拓与 C¹ 分片，也没有触及 L8–L11。

## 验证

* `KLS/Geometry/SurfaceSlicing.lean` 以 `-DwarningAsError=true` 单独编译通过。
* `build/audit/BorelSliceAudit.lean` 以 `-DwarningAsError=true` 编译通过：3 条语句 `#check`
  （逐字复述路线记录的 L4、L5 与目标 T1）与 12 条定理——`target_L4`、`target_L5`、`target_T1`、
  两条减弱假设的版本、`eilenberg_borel`（L1 + L4 的合并形式）、`weighted_one`（L5 在权重 `1`
  处回到 L4）、`infinite_volume`（无界、无限体积的可测集）、`top_weight`（`g ≡ ⊤`）、
  三条 `preserved_*` 具名参数签名检查——以及 15 条 `#print axioms`。
  全部 15 个声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
* 重跑 `CompactSliceAudit`、`EilenbergMajorantAudit`、`NullSlicingAudit`（前三轮客户端，
  未作修改）、`WeightedCoareaRouteStatements`、`WeightedCoareaInfrastructure`、
  `AreaFormulaAudit`、`CheegerInfimumAudit`、`MinkowskiConstantAudit`、`SuperlevelSardScope`、
  `SmoothSardAudit`、`SmoothSardRouteStatements`，全部严格编译通过；它们的 `preserved_*`
  再次以具名参数确认前三轮的语句未变。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **3/3/5，总数 11**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-borel-slice-measurable.json`，最终核对另存
  `build/audit/borelslice-final-snapshot.json`。`build/` 被 gitignore，故 `build/audit`
  的哈希由证据 JSON 单独绑定。
* 证书仍 **24**，perimeter infrastructure 仍 **missing**（gap 列表按本轮更新：
  L1–L5 全部改为已证明，并写明 T1 的语句已证明而 WIP 洞未填）。
