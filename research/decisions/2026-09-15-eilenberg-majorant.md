# Eilenberg 可测上界（带常数的 L1）

2026-09-15。本轮**证明了加权 coarea 路线的 L1**：Lipschitz 水平截面的 Hausdorff 测度具有
可测支配函数，其 Lebesgue 积分被 `C · K · volume S` 控制，常数显式且为正。上一轮的 L2
成为它的零测特例。不提交、不推送、不改历史决定。起始 HEAD 为
`2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260914T211119.924157Z/report.json`（与 `build/verification/latest.json`
逐字节相同），重新计算的完整快照与回执相等：414 个文件，SHA256
`ca32490215e2f001aadbd83b7d18110d74ef39b971c12818a91b635e2b40ec18`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 本轮证明的内容

### `Analysis/HausdorffSlicing.lean`（只依赖 Mathlib，任意 `EMetricSpace`）

```lean
theorem FunctionalInequalities.Analysis.exists_measurable_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {u : X → ℝ} {K : ℝ≥0} {S : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, μH[d] (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ 2 * (K : ℝ≥0∞) * μH[d + 1] S
```

这是 Mathlib 直径规范下的 Eilenberg 不等式，常数为 `2`，**没有维数、没有向量空间结构、
没有 `volume`**。两条新辅助引理：

```lean
theorem FunctionalInequalities.Analysis.exists_measurable_majorant_of_eqOn
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {u : Y → ℝ} {S : Set Y}
    (h : ∀ x ∈ S, ∀ y ∈ S, u x = u y) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧ (∀ t, μ (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) = 0

theorem FunctionalInequalities.Analysis.exists_cover_cost_lt
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {S : Set X} {r c : ℝ≥0∞} (hr : 0 < r) (hc : μH[d] S < c) :
    ∃ T : ℕ → Set X, S ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c
```

### `KLS/Geometry/SurfaceSlicing.lean`（归一化包装，常数显式）

```lean
def FunctionalInequalities.KLS.eilenbergConstant (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] : ℝ≥0 :=
  Real.toNNReal (4 * unitBallVolume (Module.finrank ℝ V - 1) / unitBallVolume (Module.finrank ℝ V))

theorem FunctionalInequalities.KLS.coe_eilenbergConstant : (eilenbergConstant V : ℝ≥0∞) = …  -- rfl
theorem FunctionalInequalities.KLS.eilenbergConstant_pos : 0 < eilenbergConstant V

theorem FunctionalInequalities.KLS.exists_measurable_majorant
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} (hu : LipschitzOnWith K u S) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * (K : ℝ≥0∞) * volume S
```

常数 `4 ω_{n-1} / ω_n` 是 Mathlib 常数 `2` 先按纤维测度归一化 `ω_{n-1}/2^{n-1}`、再按环境
测度归一化 `2^n/ω_n` 的结果。**不声称尖锐**。审计客户端把它算成具体数字：
`eilenbergConstant ℝ = 2`（`4·ω₀/ω₁ = 4/2`，用 `Γ(3/2) = √π/2`），
`eilenbergConstant (EuclideanSpace ℝ (Fin 0)) = 4`。

与路线记录的 L1 相比：`∃ C : ℝ≥0, 0 < C ∧ …` 由 `eilenbergConstant` 与 `eilenbergConstant_pos`
给出，并且**去掉**了 `[CompleteSpace V]`（从未使用）与 `[Nontrivial V]`（零维单独处理，见下），
没有增加任何假设。客户端的 `target` 用带 `[CompleteSpace V]` 与 `[Nontrivial V]` 的原语句
逐字复述并证明，`target_of_trivial` 证明去掉 `[Nontrivial V]` 的版本。

## 证明设计

与上一轮同一套覆盖骨架，只把"总覆盖成本趋零"换成"总覆盖成本趋近 `μH[d+1] S`"：
`Measure.mono_pre` 说每个尺度的下确界都 `≤ μH[d+1] S`，所以由 `exists_cover_cost_lt` 可在
尺度 `(k+1)⁻¹` 上取到成本 `< μH[d+1] S + (k+1)⁻¹` 的覆盖。水平区间、可测支配函数、
子类型索引的 `hausdorffMeasure_le_liminf_tsum` 逐点界、`lintegral_tsum` 与
`lintegral_indicator_const` 的积分界、Fatou 全部不变，极限由
`Tendsto (fun k ↦ 2K(μH[d+1] S + (k+1)⁻¹)) → 2K·μH[d+1] S` 给出。

**退化情形用显式分支，不是排除。**

* `K = 0`：`u` 在 `S` 上为常数，`exists_measurable_majorant_of_eqOn` 给出集中在单个水平上的
  `∞` 支配函数，积分为 `⊤ · 0 = 0`，正是此时右端要求的值。这同时解决了
  `μH[d+1] S = ⊤` 且 `K = 0` 的情形——那里覆盖论证根本取不到有限成本的覆盖。
* `μH[d+1] S = ⊤` 且 `K ≠ 0`：右端为 `⊤`，取 `F ≡ ⊤`。
* `d = 0`：仍然只对"区间含 `t`"的块求和（子类型索引），否则空块会贡献 `0^(0:ℝ) = 1`。
* 零维（KLS 层）：自然数减法给 `surfaceMeasure V = hausdorffNormalized V 0`，空间是
  `Subsingleton`，所以 `u` 在 `S` 上必为常数，同一条 `exists_measurable_majorant_of_eqOn`
  以 `μ = surfaceMeasure V` 收尾。**没有**把零维 `ℋ⁰` 当成零测度；
  上一轮客户端已算出 `surfaceMeasure (EuclideanSpace ℝ (Fin 0)) univ = 1`。
* 正维（KLS 层）：`((n-1 : ℕ) : ℝ) + 1 = (n : ℝ)` 需要 `1 ≤ n`，所以维数分支是必要的。

**没有循环论证。** 可测性仍然只对**构造出来的**支配函数成立，从未假设截面函数
`fun t ↦ surfaceMeasure V (S ∩ {u = t})` 可测。L3–L5 的截面可测性仍未证明。

## L2 与上一轮声明的处理

`ae_hausdorffMeasure_inter_levelSet_eq_zero` 与
`KLS.ae_surfaceMeasure_inter_levelSet_eq_zero` 的**语句逐字未变**，证明改为 L1 的推论
（右端为 `2K·0 = 0`，支配函数可测，`lintegral_eq_zero_iff` 适用）。
`exists_cover_of_hausdorffMeasure_eq_zero` 语句逐字未变，改为 `exists_cover_cost_lt` 的推论。
`exists_levelSlab` 语句逐字未变。

这四条由客户端**机器检查**：`preserved_*` 四条定理逐字复述上一轮决定记录里的语句，并用
**具名参数**（`(u := u) (K := K) (N := N) (d := d)`）调用库声明，所以改名绑定变量或改变
假设顺序都会在这里编译失败。改写过程中确实一度把 `exists_levelSlab` 的 `N` 写成 `S`，
正是这项检查报出 `Invalid argument name N`，随后已改回 `N`，没有留下签名变动。

## 本轮没有做的事

* **L3–L5 的截面可测性桥接**仍未证明：紧集纤维 Borel 可测性（L3，含开覆盖 content 的
  尺度极限与 `mkMetric'` 的对接）、Borel 集纤维 a.e. 可测性（L4）、带可测权重版本（L5）。
* **三个原始 coarea 洞**未动：`Analysis.aemeasurable_lintegral_levelSet`、
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`、
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`。
* 尖锐 `C^(finrank)` 的 `Analysis.sard`（已无下游消费者）及
  `Analysis.ae_forall_fderiv_ne_zero` 仍带 `sorryAx`。
* `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等仍未证明。
* 常数不声称尖锐；没有证明 `C = 1` 或任何下界。
* 没有触及 L6/L6a/L7 的 Whitney 延拓与 C¹ 分片，也没有触及 L8–L12。
* L1 不填任何原有 coarea 洞：直接洞按预期仍为 3/3/5，总数 11。

## 验证

* 两个库模块均以 `-DwarningAsError=true` 单独编译通过。
* `build/audit/EilenbergMajorantAudit.lean` 以 `-DwarningAsError=true` 编译通过：
  1 条语句 `#check`（逐字复述路线记录的 L1）与 12 条定理——`target`（带 `[CompleteSpace V]`
  与 `[Nontrivial V]` 的原语句）、`target_of_trivial`、6 条独立消费者
  （`null_slicing` 由 L1 独立重推的 L2、`ae_ne_top` 即 `volume S` 有限时几乎每个截面测度
  **有限**（L2 给不出的结论）、`constant_on_set` 即 `K = 0` 迫使积分为零、
  `univ_without_finiteness` 即 `S = univ` 无任何有限性假设、`eilenbergConstant_real = 2`、
  `eilenbergConstant_euclidean_zero = 4`）、4 条 `preserved_*` 具名参数签名检查——
  以及 23 条 `#print axioms`（11 条库声明 + 12 条客户端声明）。
  全部 23 个声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
* 重跑 `NullSlicingAudit`（上一轮客户端，未作修改）、`WeightedCoareaRouteStatements`、
  `WeightedCoareaInfrastructure`、`AreaFormulaAudit`、`CheegerInfimumAudit`、
  `MinkowskiConstantAudit`、`SuperlevelSardScope`、`SmoothSardAudit`、
  `SmoothSardRouteStatements`，全部严格编译通过。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **3/3/5，总数 11**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-eilenberg-majorant.json`，最终核对另存
  `build/audit/eilenberg-final-snapshot.json`。`build/` 被 gitignore，故 `build/audit`
  的哈希由证据 JSON 单独绑定。
* 证书仍 **24**，perimeter infrastructure 仍 **missing**（gap 列表按本轮更新：L1 与 L2
  改为已证明，L3–L5 仍列为缺口）。
