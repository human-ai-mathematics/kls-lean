# 紧集截面的可测性（L3）

2026-09-15。本轮**证明了加权 coarea 路线的 L3**：连续函数在紧集上的水平截面，其
`surfaceMeasure` 是水平的 Borel 可测函数。不提交、不推送、不改历史决定。起始 HEAD 为
`2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260914T213846.405397Z/report.json`（与 `build/verification/latest.json`
逐字节相同），重新计算的完整快照与回执相等：416 个文件，SHA256
`c81cf7e5258b328c5c9546bf6d134b41a65ec626cd76137bdeaddb01c2acf373`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 本轮证明的内容

### 新模块 `formalization/FunctionalInequalities/Analysis/HausdorffContent.lean`

只依赖 Mathlib，任意 `EMetricSpace`。给 `Measure.hausdorffMeasure_apply` 的内层下确界命名，
并加入**只用开集覆盖**的变体：

```lean
def FunctionalInequalities.Analysis.familyCost (d : ℝ) (T : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d

def FunctionalInequalities.Analysis.coverCost (d : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ i, T i) (_ : ∀ i, Metric.ediam (T i) ≤ r), familyCost d T

def FunctionalInequalities.Analysis.openCoverCost (d : ℝ) (r : ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨅ (T : ℕ → Set X) (_ : ∀ i, IsOpen (T i)) (_ : A ⊆ ⋃ i, T i)
    (_ : ∀ i, Metric.ediam (T i) ≤ r), familyCost d T
```

两条主结论：

```lean
theorem FunctionalInequalities.Analysis.iSup_openCoverCost_eq_hausdorffMeasure
    {d : ℝ} (hd : 0 ≤ d) (A : Set X) :
    ⨆ n : ℕ, openCoverCost d ((n : ℝ≥0∞) + 1)⁻¹ A = μH[d] A

theorem FunctionalInequalities.Analysis.measurable_hausdorffMeasure_inter_levelSet
    {d : ℝ} (hd : 0 ≤ d) {S : Set X} {u : X → ℝ}
    (hS : IsCompact S) (hu : Continuous u) :
    Measurable fun t : ℝ => μH[d] (S ∩ {x | u x = t})
```

中间接口：`hausdorffMeasure_eq_iSup_coverCost`、`coverCost_le`、`openCoverCost_le`、
`openCoverCost_lt_iff`、`coverCost_mono_scale`、`coverCost_le_openCoverCost`、
`coverCost_le_hausdorffMeasure`、`exists_cover_familyCost_lt`、`exists_thickening_radius`、
`openCoverCost_le_hausdorffMeasure`、`isOpen_setOf_slice_subset`、
`upperSemicontinuous_openCoverCost_slice`。

### `KLS/Geometry/SurfaceSlicing.lean` 新增归一化包装

```lean
theorem FunctionalInequalities.KLS.measurable_surfaceMeasure_inter_levelSet
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] {u : V → ℝ} {S : Set V}
    (hu : Continuous u) (hS : IsCompact S) :
    Measurable fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})
```

与路线记录的 L3 相比，去掉了从未使用的 `[CompleteSpace V]` **与 `[FiniteDimensional ℝ V]`**
（`surfaceMeasure` 只读 `Module.finrank`，不需要有限维），没有增加任何假设。客户端 `target`
用带这两个实例的原语句逐字复述并证明，`target_of_not_finiteDimensional` 证明去掉两者的版本。
零维、一维与自然数减法边界都由同一条语句覆盖，不需要维数分支。

## 证明设计

**不能直接宣称 `μH[d]` 上半连续**——路线记录明确警告过这一点，本轮也没有这样做。
真正成立的是两层结构：

1. **固定尺度上的开覆盖 content 是上半连续的。** 关键引理
   `isOpen_setOf_slice_subset`：若开集 `U` 包含紧集 `S` 的某个水平截面，则它包含附近所有水平的
   截面。证明用 `S \ U` 紧（`IsCompact.diff`）且与该水平不交，故连续函数 `|u - t|` 在其上取到
   正的最小值（`IsCompact.exists_isMinOn`），该最小值就是水平的允许扰动。`S \ U = ∅` 单独处理。
   由此：给定 `openCoverCost d r (S ∩ {u = t}) < c` 的一组开覆盖，**同一组覆盖**对附近所有水平
   都有效，所以 `{t | openCoverCost d r (S ∩ {u = t}) < c}` 是开集，即
   `upperSemicontinuous_openCoverCost_slice`。**限制到开覆盖正是这一步成立的原因**：任意覆盖
   没有紧性论证可用。

2. **开覆盖 content 的尺度极限仍是 `μH[d]`。** `≥` 方向平凡（开覆盖是覆盖的子族，故
   `coverCost ≤ openCoverCost`，再用 `coverCost` 对尺度的反单调性）。`≤` 方向是本轮的主要工作
   `openCoverCost_le_hausdorffMeasure`：对任意 `ε > 0`，取尺度 `r₀ = min (r/2) 1` 上成本
   `< μH[d] A + ε/2` 的近最优覆盖（`exists_cover_familyCost_lt`），逐块加厚成开集
   `Metric.thickening (b i) (C i)`。直径增量由 `Metric.ediam_thickening_le` 控制，
   `r₀ + r₀ ≤ r` 留出的余量吸收它；成本增量由 `ENNReal.exists_pos_sum_of_countable` 给出的
   可和正数列 `σ i` 吸收，逐块半径 `b i` 由 `exists_thickening_radius` 用
   `ENNReal.continuous_rpow_const` 的连续性在 `𝓝[>] 0` 上取到。空块用
   `Metric.thickening_empty` 保持成本 `0`。最后 `ENNReal.le_of_forall_pos_le_add` 收尾。

   **固定尺度上 `openCoverCost` 一般严格大于 `coverCost`**，所以这个等式必须经过尺度极限，
   不能在单个尺度上偷换。

3. L3 = 可数上确界的可测性：`Measurable.iSup` 加 `UpperSemicontinuous.measurable`。
   `d = 0` 由 Mathlib 自带的 `Nonempty` 保护覆盖（空块成本 `0`，不是 `0^(0:ℝ) = 1`）。

## 与 L1/L2 的关系

L3 **不是** L1 的推论：L1 只给构造出来的支配函数的可测性，对截面函数本身的可测性没有任何断言。
反过来 L3 也不给积分界。客户端的 `eilenberg_compact` 把两者合并成 L4/L5 将要消费的形式：

```lean
theorem CompactSliceAudit.eilenberg_compact (hu : LipschitzOnWith K u S)
    (hc : Continuous u) (hS : IsCompact S) :
    Measurable (fun t : ℝ => surfaceMeasure V (S ∩ {x | u x = t})) ∧
      (∫⁻ t, surfaceMeasure V (S ∩ {x | u x = t}) ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S
```

左端现在是一个**可测函数的真积分**。客户端在直线的单位区间上把两端都算出来：
`∫⁻ t, surfaceMeasure ℝ (Icc 0 1 ∩ {x | id x = t}) = 1`（每个水平恰一个点，`ℋ⁰` 计数），
而 Eilenberg 界是 `eilenbergConstant ℝ · 1 · volume (Icc 0 1) = 2`。两端都不空洞。

## 本轮没有做的事

* **L4（Borel 集截面 a.e. 可测）与 L5（可测权重）**仍未证明。L3 只对**紧** `S` 成立，
  对一般 Borel 集没有任何断言；L4 需要 Lebesgue 内正则性把 Borel 集分解为递增紧集并加一个
  体积零余项（余项由已证明的 L2 处理），本轮没有做。
* **三个原始 coarea 洞**未动：`Analysis.aemeasurable_lintegral_levelSet`、
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`、
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`。
  特别地，第一个洞要求对**任意** Borel 集（目标里是 `univ`）成立，紧集版本不能填它。
* 尖锐 `C^(finrank)` 的 `Analysis.sard`（已无下游消费者）及
  `Analysis.ae_forall_fderiv_ne_zero` 仍带 `sorryAx`。
* `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等仍未证明。
* 没有证明 `μH[d]` 自身的上半连续性（一般不成立），也没有声称 `openCoverCost` 在固定尺度上
  等于 `coverCost`。
* 没有触及 L6/L6a/L7 的 Whitney 延拓与 C¹ 分片，也没有触及 L8–L12。
* L3 不填任何原有 coarea 洞：直接洞按预期仍为 3/3/5，总数 11。

## 验证

* `Analysis/HausdorffContent.lean` 与 `KLS/Geometry/SurfaceSlicing.lean` 均以
  `-DwarningAsError=true` 单独编译通过。
* `build/audit/CompactSliceAudit.lean` 以 `-DwarningAsError=true` 编译通过：1 条语句 `#check`
  （逐字复述路线记录的 L3）与 11 条定理——`target`（带 `[CompleteSpace V]` 与
  `[FiniteDimensional ℝ V]` 的原语句）、`target_of_not_finiteDimensional`、
  `eilenberg_compact`（L1 + L3 的合并形式）、`measurableSet_slice_lt`、
  `exp_not_lipschitz`（连续但非全局 Lipschitz 的 `u`）、直线上的三条计算
  （`surfaceMeasure_real_singleton`、`slice_Icc`、`lintegral_slice_Icc = 1`）、
  `eilenberg_bound_Icc`（右端为 `2`）、两条 `preserved_*` 具名参数签名检查——
  以及 29 条 `#print axioms`（18 条库声明 + 11 条客户端声明）。
  全部 29 个声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
* 重跑 `EilenbergMajorantAudit`、`NullSlicingAudit`（前两轮客户端，未作修改）、
  `WeightedCoareaRouteStatements`、`WeightedCoareaInfrastructure`、`AreaFormulaAudit`、
  `CheegerInfimumAudit`、`MinkowskiConstantAudit`、`SuperlevelSardScope`、`SmoothSardAudit`、
  `SmoothSardRouteStatements`，全部严格编译通过。`EilenbergMajorantAudit` 的四条 `preserved_*`
  再次以具名参数确认前两轮的语句未变。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **3/3/5，总数 11**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-compact-slice-measurable.json`，最终核对另存
  `build/audit/compactslice-final-snapshot.json`。`build/` 被 gitignore，故 `build/audit`
  的哈希由证据 JSON 单独绑定。
* 证书仍 **24**，perimeter infrastructure 仍 **missing**（gap 列表按本轮更新：
  L1、L2、L3 改为已证明，L4 与 L5 仍列为缺口）。
