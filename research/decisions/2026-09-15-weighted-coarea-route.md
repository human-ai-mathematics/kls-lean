# 加权 coarea 路线探查

2026-09-15。本轮只做路线探查，**没有证明新定理，没有修改任何 `.lean` 库源码**。
不提交、不推送、不改历史决定。起始 HEAD 为 `2965b32bc79bdb24921c633df12102450eaedcc4`；
起始 passed 回执为 `20260914T181901.237724Z`，重新计算的完整快照与回执相等：408 个文件，
SHA256 `c65036cc1bc9362b558864d470ec2c7f10c6dd15faba9d3f0a499b637e396adf`。
这里的逐字节核对指逐文件 SHA256（包括删除项）及完整快照结构一致，不是只看 HEAD。

## 判断与下一步

**数学路线可行；现有库尚不能装配出 coarea。** 推荐证明 L12：在任意有限维实内积空间上，
对全局 Lipschitz 实值 `u`、任意 Borel 集 `S` 和任意可测 `g : V → ℝ≥0∞`，同时给出
截面积分的 `AEMeasurable` 和加权等式。`S` 不要求有界、有限体积、有限周长；`g` 不要求
有限值、可积或有界。`V` 不加非零维限制，梯度保持 Mathlib 的 `gradient`。
具体 Lean 陈述全部见下方和 `build/audit/WeightedCoareaRouteStatements.lean`。

第一处确切障碍是 **L2：Lipschitz 映射的体积零集截面几乎处处具有零 surfaceMeasure**。
Rademacher 只给不可微集合的体积为零，不能直接推出 L2。
L1 是足够的更强基础设施：Eilenberg 型截面上界，以一个**可测上界函数**表达，故不循环
假设尚未证明的截面可测性。特别不能把任意函数的 Lean `lintegral = 0` 当作 a.e. 零；
在可测性建立前，这种论证缺少必要前提。

第二处确切障碍是 **L6 的 C¹ Whitney 一阶 jet 延拓**以及 **L6a/L7 的 Whitney–Lusin 分片**。
现有 Rademacher、可测导数、线性近似分片和 Egorov 都不直接给出“函数与导数同时精确相等”的
全局 C¹ 函数。卷积在 L¹ 中逼近不保持水平集，无法替代这个命题。
本仓库已证明的面积公式只覆盖 **C¹ 图**，所以不能跳过这些桥接直接对任意 Lipschitz 水平集使用。

建议下一轮先攻 **L2 的零集覆盖证明**（可以只证零测特例，不先完成带常数的全部 L1），
继而 L3–L5；这可独立推进第一个原始洞。随后补完整 L1 和 C¹ coarea，再处理 L6/L6a。
此顺序不承诺下一轮就能证完任一洞。

## 从 L12 回到三个原始目标

* 目标 T1：在 L12（或更早的 L5）中取 `S = Set.univ`，化简 `univ_inter`，取可测性分量。
* 目标 T2：同样取 `S = univ`，化简 `Measure.restrict_univ` 和 `univ_inter`，取等式分量。
* 目标 T3：直接应用 T2/L12 到其 `hK`、`hg`；其 C¹ 假设无需参与证明。
  原有 `ContDiff ℝ 1 u`、`SecondCountableTopology V` 等参数保留，不能趁机删改签名。

没有把 Lipschitz 目标换成 C¹ 目标。C¹ 是中间步骤，L7 与 L2 才把它提升到原来要求的
Lipschitz 范围。T1–T3 的源文件本轮整文件哈希未变；检查文件仅将未使用的命名证明参数写成
`_`，以通过 unusedVariables linter，其类型、量词顺序和结论不变。

## 分阶段依赖与证明设计（尚未形式化）

1. **零维 L0。** 有限维 `finrank = 0` 转为 `Subsingleton V`。所有梯度为零，`u` 的像
   至多一个实数。截面积分可能在这一点为 `⊤`，但在其补集恒零，因此 AEMeasurable 且积分为零。
   不使用 `surfaceMeasure = 0`：本仓库自然数减法给零维 `ℋ⁰`，不是负维 Hausdorff 测度。
   从一维开始才进入 L1 的 `[Nontrivial V]` 分支；一维的纤维是 `ℋ⁰`，必须保留计数效应。
2. **L1 → L2。** 对任意集合取尺度趋零的可数小直径覆盖，将各覆盖集与 `S` 相交；
   水平轴上用包含 `u` 的像的可测区间替代像本身。区间长度由 `K × diameter` 控制，
   每层截面成本是 `diameter^(n-1)`。`liminf` 的可测覆盖成本给上界 `F`，Fatou 与覆盖成本
   给 `∫ F ≤ C K volume S`。只要求某个有限正维数常数 C，不冒充 sharp 常数 1。
   顶维 Hausdorff 与 volume 的归一化等式已在仓库证明。`K = 0`、空覆盖以及 `volume S = ⊤`
   独立分支处理；零集特例由 `F = 0` a.e. 和逐点支配得 L2，不用可测选择、不用 Sard。
3. **L3 → L4 → L5。** 紧集与连续 `u` 的截面是紧集。先建立以严格直径界的有限开覆盖
   计算 Hausdorff content 的接口：每个尺度的 content 在 `t` 上上半连续，其趋零极限等于
   现有 `μH`（必须证明与 `mkMetric'` 定义的对接，不能直接宣称 `μH` 自身上半连续）。
   由此得 L3。Borel `S` 经 Lebesgue 内正则性分为递增紧集并集加体积零余集；L2 去掉余集，
   测度下连续性给 L4。对简单权重用有限加法，对一般 ENNReal 可测权重用递增简单函数
   和两层单调收敛得 L5，包括 `g = ⊤`。这一路不依赖 L6–L12，也不依赖 coarea 等式。
4. **L8 → L9。** 将已证明的无权全局 C¹ 图面积等式先升级到非负可测权重（简单函数、
   单调收敛），再通过开域内可数局部 C¹ 延拓和不交 Borel 分片，得到 L8。
   这里是开集内部的局部延拓，bump 局部化即可，**不依赖闭集 Whitney L6**。
   对正则点选单位方向 `e` 满足 `Du(e) ≠ 0`，用正交分解 `V ≃ H × ℝ` 和逆函数定理，
   令 `Φ(y,s) = (y,u(y+s e))`，其局部逆为 `(y,t) ↦ y+ψ(y,t)e`。
   需要 C¹ **带水平参数 t 的**图，不是仅固定一个水平的图包含关系。
   对固定 t 用 L8；对局部逆用 Mathlib 同维 Jacobian 换元与 volume 上的 Tonelli。
   计算 `|det DΦ| = |Du(e)|` 及
   `sqrt(1 + ‖D_y ψ‖²) = ‖gradient u‖ / |Du(e)|`，两边得到同一非负被积函数。
   先在可数小开块上计算，再取不交 Borel 分片求和。每个图域和 Jacobian 的可测性须同时建立。
   参数空间必须使用内积诱导的 Euclidean 范数/正交同构；不能把 `Fin n → ℝ` 的 sup norm
   直接当作 Euclidean Hausdorff 测度。当前 `Analysis/ImplicitGraph.lean` 中 C∞ 接口不直接适用；
   新增 C¹ 层，或直接使用 Mathlib 的 `ContDiffAt` 隐函数接口，不修改原公开签名。
5. **L1 → L10；L9 + L10 → L11。** 对 C¹ 函数临界集截到有限体积球，在每个精度 ε 下
   用 Mathlib 的 `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 分成可数不交
   Borel 片。该集合上的导数全为零，故每片上的限制 Lipschitz 常数可取 ε。
   对各片用 L1 并求和，得到截面上积分不超过 `C ε volume(ball)`；令 ε → 0 得 L10。
   此处直接用 L1 的可测上界，也可先对球上 Lipschitz 限制延拓后使用 L4。
   L10 是“临界**部分的截面**零测”，不是 C¹ 临界**值集**零测；后者在高维不能假定。
   用可测权重乘在零测截面上，连同正则部分 L9 得 L11。辅助 `v j` 无需全局 Lipschitz，
   所以 L11 刻意不加这条假设。
6. **L6a + L6 → L7。** Rademacher 给 a.e. 可微；`measurable_fderiv` 与一阶差商余项的
   可测编码，经有限体积上的简单函数逼近、Egorov、内正则性，提取覆盖 a.e. 的可数紧 jet 片，
   在每片导数连续且余项一致 o(distance)，即 L6a。这里需实现 Lusin 型紧集提取，现有库
   的 Lusin–Souslin（解析集分离/像可测）不是这个定理。然后 L6 在每片延拓，差分化紧片使其
   不交，得到 L7。导数相等明确写进结论，不从任意稀疏集合上的值相等推断它。
7. **L2 + L7 + L11 → L12。** 令 `N = (⋃j S j)ᶜ`。左侧忽略 volume-null 的 N；右侧
   **用原来的 Lipschitz u** 对 N 应用 L2。每片上 `u = v j` 使水平集相同，且导数相等使
   梯度相等。对可测权重在各片用 L11，再用可数不交加法和 Tonelli 得全局等式；L5 已独立
   给可测性。全程不用有限值减法，避免 `⊤ - ⊤`，也不要求 `g` 可积。

路线选择参考 Jerrard 的作者讲义第 3 节：其中分别处理截面上积分、紧集截面可测性与
C¹/Lipschitz 归约，并指出 Whitney 延拓在后一步的作用。这里只用它核对路线层次；以上
Lean 接口拆分、缺口和实现估计是对当前仓库的独立分析，并非讲义已完成的形式化。
[讲义原文](https://www.math.toronto.edu/rjerrard/1501/notes/week5-6.pdf)。

## 所需引理清单

下表行数为**新增 Lean 证明的大致行数**，不包括重用的已有模块，不是完成承诺。
“无”指当前 pin 的 Mathlib 没有该完整接口；“已有原料”不表示该引理已证明。
所有条目的精确语句按编号附在下方；没有隐含的有限性或非退化条件。

| 编号 | 内容与依赖 | Mathlib 是否已有（完整接口） | 估计行数 | 风险 |
|---|---|---|---:|---|
| L0 | 零维联合结论 | 无；subsingleton、实数 singleton 零测和 a.e. 同余可用 | 30–60 | 低；`0 * ⊤` 与 H⁰ |
| L1 | Eilenberg 可测上界；Hausdorff 覆盖、Fatou、归一化 | 无；`MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum` 有覆盖极限上界，但没有对水平参数积分的估计 | 400–800 | 高；双重覆盖、K=0、n=1、非可测 S |
| L2 | 零测集的 a.e. 零截面；L1 + L0 | 无 | 20–50（直接零集覆盖约 200–350） | 中；不能只用 Rademacher |
| L3 | 紧集截面 Borel 可测 | 无；`MeasureTheory.OuterMeasure.mkMetric'.eq_iSup_nat` 有尺度极限，缺开覆盖 content 的参数上半连续接口 | 200–400 | 高；不可偷换 μH/content；n=1 |
| L4 | Borel 集截面 a.e. 可测；L2 + L3 + 内正则性 | 无；`MeasurableSet.exists_isCompact_isClosed_sdiff_lt` 为现有原料 | 80–160 | 中；无限体积用可数耗尽 |
| L5 | 可测权重版本；L4 + 简单函数逼近 | 无；`MeasureTheory.lintegral_iSup` 可用 | 80–150 | 中；不假定内层测度 SFinite |
| L6 | 紧集一阶 Whitney jet 的 C¹ 延拓 | **无** | 800–1600 | 很高；新建 Whitney 覆盖/分割统一及边界可微证明 |
| L6a | a.e. 可微 Lipschitz 函数的紧 jet 提取 | **无**；`LipschitzWith.ae_differentiableAt`、`measurable_fderiv`、`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`、`exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt` 仅为原料 | 250–500 | 高；Lusin 型精确一致化和余项可测编码 |
| L7 | 可数 C¹ 精确分片；L6a + L6 | 无 | 80–160 | 中；必须同时保留导数相等 |
| L8 | 开域带权图面积 | 无；本仓库 `FunctionalInequalities.Analysis.hausdorffNormalized_image_graphMap` 已有全局无权版 | 180–350 | 中；开域与可数局部化 |
| L9 | C¹ 正则开域 coarea；L8 + 带参数隐函数 + Jacobian | 无；`ContDiffAt.implicitFunction`、`ContDiffAt.contDiffAt_implicitFunction`、`ContDiffAt.eventually_apply_eq_iff_implicitFunction`、`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` 可用 | 500–1000 | 高；图族、行列式与 Hausdorff 归一化 |
| L10 | C¹ 临界部分截面零测；L1 + 线性近似分片 | 无；`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 可用 | 150–300 | 高；不能调用 C∞ Sard 代替 |
| L11 | 任意 C¹ 函数带权 coarea；L9 + L10 | 无 | 80–160 | 中；无全局 Lipschitz 界 |
| L12 | 一般 Lipschitz 联合结论；L0/L2/L5/L7/L11 | 无 | 120–240 | 中；对 N 使用原函数，处理无穷权重 |
| T1/T2/T3 | 原始三个目标；L12 取 univ（T1 可先由 L5） | 无；现有 WIP 声明均含直接洞 | 各 3–10 | 低；只有前提全部证明后才能填 |

行数范围针对这一选定路线，不声称是最小成本。更直接的替代路线是把现有 C¹ 图面积公式
推广到 Lipschitz/可微分片上的面积公式，配合双 Lipschitz 正则分片；那样可以避免 L6，
但必须另证“可微分片的余维一面积公式”与临界截面估计，不能说 Mathlib 的同维 Jacobian
换元已经给了这个结论。本轮不将未经拆解的替代路线列为已可实施捷径。BV 路线还须证明
有限周长、约化边界/水平集识别与 BV coarea；当前选择不引入这套额外基础设施。

## 可测性是否值得本轮单独证明

L2–L5 的路线表明它**独立于 coarea 等式**，但在当前库上不是一个廉价参数积分包装。
`Measurable.lintegral_prod_right'` 的实际签名要求 `[SFinite ν]`。
正维环境 V 上的 `(n-1)` 维 Hausdorff 测度不能满足这个要求：可取不可数多两两不交的
平行超平面片，每片具有正有限表面积；SFinite 测度不可能有这样的不交正测集族。
`u = constant` 时某一水平甚至是整个环境空间，不能对所有纤维暗加局部有限性。
因而本轮没有声称证明 T1，也没有只证明带 SFinite/正则值附加假设的弱版来计作填洞。
L0 或 L8 的全局带权子例虽较便宜，但不能关闭三个目标中的任意一个；本轮交付完整语句和
障碍定位，不新建这些辅助声明。新增结果的公理审计为空（没有新增结果），不是“已证 coarea”。

## 放置、验证与边界

后续 L6/L6a/L7 宜放 `Analysis/WhitneyExtension.lean`、`Analysis/LipschitzC1Pieces.lean`，
只依赖 Mathlib；L1/L2/L3 的底层覆盖可在 `Analysis/HausdorffSlicing.lean` 用原始 `μH`
表述，归一化包装再依赖既有 `KLS/Geometry/SurfaceMeasure`。L8 扩展现有 `Analysis/AreaFormula`
的职责，L9–L12 放独立 `Analysis/Coarea.lean`，C¹ KLS 包装留在适当的 Geometry 层。
这些只是未来模块建议，本轮未创建模块、未迁移声明、未修改签名或证书/leanok 范围。

* `WeightedCoareaRouteStatements.lean`：17 个 `#check`，只有 import/open 与命题检查，
  无声明、无证明、无占位公理，以 `-DwarningAsError=true` 编译。
* `WeightedCoareaInfrastructure.lean`：20 个既有 API 的 `#check`，同样严格编译；实际签名
  记录在 `build/audit/coarea-infrastructure.log`，包括参数积分的 SFinite 条件。
* 重跑 `AreaFormulaAudit`、`CheegerInfimumAudit`、`MinkowskiConstantAudit`、
  `SuperlevelSardScope`、`SmoothSardAudit`、`SmoothSardRouteStatements`，全部严格编译；
  三个 WIP 文件实际逐个编译成功，诊断中的直接洞分别 **3/3/5，总数 11**。
* 默认 `lake build` 和根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，需与最终全部源码快照再次完全相等。
  证据 JSON 为 `research/explorations/2026-09-15-weighted-coarea-route.json`，记录输入快照、
  源码/语句/日志哈希；忽略目录中的最终核对另存 `build/audit/coarea-final-snapshot.json`，
  避免给回执自身制造循环哈希。`build/audit` 不在常规源码快照中，故由证据 JSON 单独绑定。

明确未完成：尖锐 **C^(finrank) `Analysis.sard`**（已无下游消费者）；两个 Analysis coarea
洞及 Isoperimetry 的 C¹ 洞；**`smoothConstant_le_minkowskiConstant`**、
**`smoothConstant_mul_lintegral_min_superlevel_le`**、**两个 Cheeger 常数相等**。
已有 C∞ Sard 与迁出 WIP 的 `ae_exists_superlevel` 保持无 `sorryAx`，但整条链没有闭合。
证书仍 24，perimeter infrastructure 仍 **missing**。

## 精确 Lean 语句

以下与检查文件逐条对应；L0–L12（含 L6a）全部待证，T1–T3 为原始待证目标。
通用 import/open 与检查文件一致；所有实例显式列出，不把新假设藏在 section 中。

### L0

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Subsingleton V] (u : V → ℝ) {g : V → ℝ≥0∞}, Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L1

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V], ∃ C : ℝ≥0, 0 < C ∧
    ∀ {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzOnWith K u S →
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, KLS.surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * (K : ℝ≥0∞) * volume S)
```

### L2

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}, LipschitzOnWith K u N →
    (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure ℝ), KLS.surfaceMeasure V (N ∩ {x | u x = t}) = 0)
```

### L3

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
    Measurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t})))
```

### L4

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzWith K u → MeasurableSet S →
    AEMeasurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t}))
      (volume : Measure ℝ))
```

### L5

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ))
```

### L6

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ Set.EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x)
```

### L7

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ (S : ℕ → Set V) (v : ℕ → V → ℝ),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j ↦ Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x)
```

### L8

```lean
#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V}
    {O S : Set H} {v : H → ℝ} {g : V → ℝ≥0∞},
    ‖e‖ = 1 → (∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) →
    IsOpen O → ContDiffOn ℝ 1 v O → MeasurableSet S → S ⊆ O → Measurable g →
    (∫⁻ x in Analysis.graphMap ι e v '' S, g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))) =
      ∫⁻ y in S, ENNReal.ofReal (Analysis.graphJacobian (gradient v y)) *
        g (Analysis.graphMap ι e v y) ∂(volume : Measure H))
```

### L9

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
    MeasurableSet S → S ⊆ O → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L10

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ}, ContDiff ℝ 1 u →
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0)
```

### L11

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L12

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L6a

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ S : ℕ → Set V, (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      ∀ j, IsCompact (S j) ∧ (∀ x ∈ S j, DifferentiableAt ℝ u x) ∧
        ContinuousOn (fderiv ℝ u) (S j) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x ∈ S j, ∀ y ∈ S j, ‖y - x‖ < δ →
            ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ ε * ‖y - x‖)
```

### T1

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ))
```

### T2

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}
    (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### T3

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    {u : V → ℝ} (_ : ContDiff ℝ 1 u)
    {K : ℝ≥0} (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ))
```
