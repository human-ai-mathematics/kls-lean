# 零测集的 Lipschitz 水平切片

2026-09-15。本轮**证明了加权 coarea 路线的 L2**：体积零集在 Lipschitz 映射下的水平截面
几乎处处具有零 surfaceMeasure。不提交、不推送、不改历史决定。起始 HEAD 为
`2965b32bc79bdb24921c633df12102450eaedcc4`；起始 passed 回执为
`build/verification/20260914T194849.197366Z/report.json`（与 `build/verification/latest.json`
逐字节相同，SHA256 `cc265566fc376ff989c601791ca62964f9240578b7f6a439e49de20569738aaa`），
重新计算的完整快照与回执相等：410 个文件，SHA256
`0fb70f2270d6c2f6c52ba89931a3ffcf80b8c5d9a4eea3ef671a99157283c53b`。这里的逐字节核对指
逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 本轮证明的内容

新增两个模块，共两条主结论和两条辅助引理，全部只依赖标准三条公理，无 `sorry`、
无新公理、无占位定义。

### `formalization/FunctionalInequalities/Analysis/HausdorffSlicing.lean`

只依赖 Mathlib（`Mathlib.MeasureTheory.Measure.Hausdorff`、
`Mathlib.MeasureTheory.Measure.Lebesgue.Basic`、`Mathlib.MeasureTheory.Integral.Lebesgue.Add`），
对**任意** `EMetricSpace` 成立，不需要向量空间、内积、有限维或 Haar 测度：

```lean
theorem FunctionalInequalities.Analysis.exists_cover_of_hausdorffMeasure_eq_zero
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {N : Set X} (hN : μH[d] N = 0) {r c : ℝ≥0∞} (hr : 0 < r) (hc : 0 < c) :
    ∃ T : ℕ → Set X, N ⊆ ⋃ i, T i ∧ (∀ i, Metric.ediam (T i) ≤ r) ∧
      ∑' i, ⨆ _ : (T i).Nonempty, Metric.ediam (T i) ^ d < c

theorem FunctionalInequalities.Analysis.exists_levelSlab
    {X : Type*} [EMetricSpace X]
    {u : X → ℝ} {K : ℝ≥0} {N : Set X} (hu : LipschitzOnWith K u N)
    (T : ℕ → Set X) (hT : ∀ i, Metric.ediam (T i) ≠ ∞) :
    ∃ J : ℕ → Set ℝ, (∀ i, MeasurableSet (J i)) ∧
      (∀ i, volume (J i) ≤ 2 * (K : ℝ≥0∞) * Metric.ediam (T i)) ∧
      (∀ i, ∀ x ∈ T i ∩ N, u x ∈ J i)

theorem FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {u : X → ℝ} {K : ℝ≥0} {N : Set X} {d : ℝ} (hd : 0 ≤ d)
    (hu : LipschitzOnWith K u N) (hN : μH[d + 1] N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), μH[d] (N ∩ {x | u x = t}) = 0
```

### `formalization/FunctionalInequalities/KLS/Geometry/SurfaceSlicing.lean`

由既有 `KLS.surfaceMeasure` 定义给出的归一化包装。测度与结论都没有替换：

```lean
theorem FunctionalInequalities.KLS.ae_surfaceMeasure_inter_levelSet_eq_zero
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}
    (hu : LipschitzOnWith K u N) (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0
```

与路线记录的 L2 语句相比，只**去掉**了 `[CompleteSpace V]`（证明从未使用它，有限维内积空间
本来就完备），没有增加任何假设：`N` 不要求可测、有界、非空或非零测度以外的任何性质，
`u` 只在 `N` 上 Lipschitz，`K` 任意（含 `K = 0`），`V` 允许零维。
`build/audit/NullSlicingAudit.lean` 的 `target` 用**带** `[CompleteSpace V]` 的原语句逐字
复述并证明，所以路线记录中的 L2 已经闭合。

## 证明设计

**不是 Rademacher。** Rademacher 只给"不可微点集的体积为零"，对单个水平集的余维一测度
没有任何结论；本轮结论对任何在 `N` 上 Lipschitz 的 `u` 成立，甚至不要求 `u` 可测。

**覆盖 + 可测支配函数 + Fatou。** 对每个尺度 `k`：

1. 由 `Measure.hausdorffMeasure_apply` 的下确界表达式，从 `μH[d+1] N = 0` 取出可数覆盖
   `T k : ℕ → Set X`，直径 `≤ (k+1)⁻¹`，总 `(d+1)` 维覆盖成本 `< (k+1)⁻¹`。
   Mathlib 的成本里自带 `⨆ _ : (T i).Nonempty` 保护，所以空块的成本是 `0`，
   `d + 1 = 0` 的病态情形不会出现（本轮 `0 ≤ d`）。
2. 对每个与 `N` 相交的覆盖块，取块内 `N` 中的一个点 `p`，令水平轴上的区间为
   `Metric.closedBall (u p) (K · diam)`；由**只在 `N` 上**使用的 Lipschitz 估计，
   该块与 `N` 的交在 `u` 下的像落在此区间内，区间长度 `≤ 2 K · diam`。
   与 `N` 不相交的块取空区间。
3. 支配函数 `F k t := ∑' i, (J k i).indicator (fun _ => ediam (T k i) ^ d) t`
   **逐项可测**（常数 × 可测集的 indicator），故 `F k` 可测；这一步用
   `ENNReal.tsum_eq_iSup_sum` 加有限和的可测性，不引入新的导入。
4. 逐点上界：对固定 `t`，以子类型 `{i // t ∈ J k i}` 为索引调用
   `Measure.hausdorffMeasure_le_liminf_tsum`，得
   `μH[d] (N ∩ {u = t}) ≤ liminf (F · t)`。用子类型而不是全体 `ℕ` 是必须的：
   `d = 0` 时空块会贡献 `0 ^ (0 : ℝ) = 1`，对全体求和会得到 `⊤`。
5. 积分上界：`lintegral_tsum` 与 `lintegral_indicator_const` 给
   `∫⁻ F k ≤ 2 K (k+1)⁻¹`。`K = 0` 时每个区间是单点，右端为 `0`，不需要分支。
6. Fatou（`lintegral_liminf_le'`）作用在**已证明可测**的 `F k` 上，
   `∫⁻ liminf (F · t) = 0`，再由 `lintegral_eq_zero_iff`（前提是 `liminf` 可测，
   由 `Measurable.liminf` 给出）得 `liminf (F · t) = 0` 几乎处处，逐点上界收尾。

**没有循环论证。** 全过程从未假设截面函数
`fun t => μH[d] (N ∩ {u = t})` 可测，也没有从它的 `lintegral = 0` 推出 a.e. 零：
`lintegral_eq_zero_iff` 只用在**构造出来的**可测支配函数上。L3–L5 的截面可测性仍未证明。

**零维单独处理，不把零维 surfaceMeasure 当成零测度。** `finrank ℝ V = 0` 时自然数减法给
`surfaceMeasure V = hausdorffNormalized V 0 = hausdorffNormalized V (finrank ℝ V)`，
由既有 `KLS.hausdorffNormalized_finrank_eq_volume` 等于 Lebesgue 测度；截面是 `N` 的子集，
单调性对**每个** `t` 给零。审计客户端另外算出
`surfaceMeasure (EuclideanSpace ℝ (Fin 0)) univ = 1`，即零维纤维测度是单点的单位质量，
`ℋ⁰` 不是零测度。正维时 `((finrank - 1 : ℕ) : ℝ) + 1 = (finrank : ℝ)` 需要 `1 ≤ finrank`，
所以维数分支是必要的，不是装饰。

**一维的 `ℋ⁰` 保留计数效应。** 客户端算出
`surfaceMeasure ℝ ({0} ∩ {x | id x = 0}) = 1`：`N = {0}`、`u = id` 时水平 `t = 0`
的截面测度是 `1`，所以"几乎处处"是实质的，不能加强成"处处"。
平面上 `surfaceMeasure (EuclideanSpace ℝ (Fin 2)) (segment ℝ 0 e) ≠ 0`（`e ≠ 0`）
说明正余维时纤维测度同样不恒为零。

## 放置决定

原始 Hausdorff 引理放 `Analysis/HausdorffSlicing.lean`，**本地导入闭包为空**，只依赖
Mathlib，与路线记录第 6 节"L1/L2/L3 的底层覆盖可在 `Analysis/HausdorffSlicing.lean` 用原始
`μH` 表述"的建议一致（文件名按已实现内容取 `HausdorffSlicing`）。归一化包装放
`KLS/Geometry/SurfaceSlicing.lean`，导入 `Analysis/HausdorffSlicing.lean` 与
`KLS/Geometry/SmoothDomain.lean`（后者提供约定检查 `hausdorffNormalized_finrank_eq_volume`）。

没有迁移任何已有声明，没有修改任何已有公开签名，没有改动任何 `.lean` 库文件的现有内容，
没有扩大证书或 Blueprint `leanok` 范围，没有把新模块加入 `FunctionalInequalities.lean`
认证聚合导入（与 WIP 及其他非聚合模块的现有做法一致；两个新模块仍由 `verify.py` 的
`lake build +Module` 与 `leanchecker` 全量重放覆盖）。

## 本轮没有做的事

* **L3–L5 的截面可测性桥接**仍未证明：紧集纤维的 Borel 可测性（L3）、Borel 集纤维的
  a.e. 可测性（L4）、带可测权重的版本（L5）都还没有。L2 本身**不给**可测性。
* **三个原始 coarea 洞**未动：`Analysis.aemeasurable_lintegral_levelSet`、
  `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`、
  `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`。
* 尖锐 `C^(finrank)` 的 `Analysis.sard`（已无下游消费者）及
  `Analysis.ae_forall_fderiv_ne_zero` 仍带 `sorryAx`。
* `smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等仍未证明。
* 带常数的一般 L1（Eilenberg 可测上界，右端 `C K volume S`）没有证明：本轮只做零测特例，
  证明里用的是"总覆盖成本趋零"，没有给出任何有限正维数常数 `C`。
* 没有触及 L6/L6a/L7 的 Whitney 延拓与 C¹ 分片，也没有触及 L8–L12。

## 验证

* `FunctionalInequalities/Analysis/HausdorffSlicing.lean` 与
  `FunctionalInequalities/KLS/Geometry/SurfaceSlicing.lean` 均以
  `-DwarningAsError=true` 单独编译通过。
* `build/audit/NullSlicingAudit.lean` 以 `-DwarningAsError=true` 编译通过：1 个语句
  `#check`（逐字复述路线记录的 L2）、1 条 `target` 定理（带 `[CompleteSpace V]` 的原语句）、
  9 条独立消费者/退化情形定理（无 `N` 可测性的子集用法、`K = 0`、
  任意 `ℝ≥0∞` 权重的切片积分形式、零维、零维单位质量、一维及其例外水平、
  只在 `N` 上 Lipschitz 的不连续 `u`、平面非退化线段），以及 14 条 `#print axioms`。
  全部 14 个声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
* 重跑 `WeightedCoareaRouteStatements`、`WeightedCoareaInfrastructure`、`AreaFormulaAudit`、
  `CheegerInfimumAudit`、`MinkowskiConstantAudit`、`SuperlevelSardScope`、`SmoothSardAudit`、
  `SmoothSardRouteStatements`，全部以 `-DwarningAsError=true` 严格编译通过，未作任何修改。
* 三个 WIP 文件逐个实际编译成功，诊断中的直接洞分别 **3/3/5，总数 11**——L2 不填任何原有
  coarea 洞，所以这个数字按预期不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全相等；证据 JSON 为
  `research/explorations/2026-09-15-null-slicing.json`，忽略目录中的最终核对另存
  `build/audit/nullslicing-final-snapshot.json`，避免给回执自身制造循环哈希。
  `build/audit` 不在常规源码快照中，故由证据 JSON 单独绑定其哈希。
* 证书仍 **24**，perimeter infrastructure 仍 **missing**（gap 列表按本轮更新：
  L2 从"缺失"改为"已证明"，L3–L5 仍列为缺口）。
