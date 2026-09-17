# 一般 C¹ 函数的带权 coarea（L11），目标 T3 随之证明

2026-09-16。本轮**证明了加权 coarea 路线的 L11**，并由此在审计客户端**证明了第三个原始目标
T3 的完整语句**——即直接洞 `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
的语句。**没有修改任何 WIP 文件**：迁出是单独的决定，所以直接洞数不变，那个洞仍然是洞。
不提交、不推送，不改写历史决定。

起始 HEAD 为 `737abc396576abfaa596a284e46a706e8e5fd383`；起始 passed 回执为
`build/verification/20260915T113452.444474Z/report.json`，与起始工作区完全一致：
450 个文件，SHA256 `856a6b6bd93a8fea3099878a5b65b2cfc4ecfdb0fd1407b60e976f8036f5ad60`。
起始工作区含上一轮尚未提交的四处证据收尾改动，本轮在其之上继续。

## 本轮证明的内容

新模块 `formalization/FunctionalInequalities/KLS/Geometry/SmoothCoarea.lean`：

```lean
theorem FunctionalInequalities.KLS.isOpen_regular {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    IsOpen {x : V | fderiv ℝ u x ≠ 0}

/-- L11 -/
theorem FunctionalInequalities.KLS.coarea_of_contDiff {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hu : ContDiff ℝ 1 u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ)
```

与路线记录的 L11 相比只去掉了从未使用的 `[CompleteSpace V]`，没有增加任何假设：
`u` **不要求** Lipschitz、有界或紧支撑；`S` 只要可测，不要求有界或有限体积；
`g` 允许无界、不可积或恒为 `⊤`；**对导数没有任何非退化要求**——临界集可以是整个空间。
客户端 `target` 用带 `[CompleteSpace V]` 的原语句逐字复述并证明。

## 两半如何接上，以及为什么两半都必需

令 `C = {x | fderiv ℝ u x = 0}`、`R = Cᶜ`。`C` 闭（`isClosed_critical`，L10 轮已证），
故 `R` 开（`isOpen_regular`）。

* **左端**：`S = (S ∩ R) ∪ (S ∩ C)` 不交可测，而 `C` 上 `gradient u = 0`，
  故被积函数在 `S ∩ C` 上恒为零，`∫⁻_S ‖∇u‖ₑ·g = ∫⁻_{S∩R} ‖∇u‖ₑ·g`。
* **右端**：由 **L10**，几乎每个水平 `t` 满足 `surfaceMeasure V (C ∩ {u = t}) = 0`，
  于是 `(S∩R)∩{u=t}` 与 `S∩{u=t}` 在 `surfaceMeasure V` 下 a.e. 相等
  （`ae_eq_set` 加 `Measure.restrict_congr_set`），两个切片积分对几乎每个 `t` 相等。
* **中间**：对开集 `R` 与可测子集 `S ∩ R` 调用 **L9**，得等式与 `AEMeasurable`。
* 同一条 a.e. 相等把 L9 的 `AEMeasurable` 分量搬到完整切片函数上（`AEMeasurable.congr`），
  并把右端的两个积分接起来（`lintegral_congr_ae`）。

**L9 与 L10 缺一不可**：L9 只覆盖导数非零的开域，L10 只说临界部分的切片零测；
两者都不单独给出 L11。

## 目标 T3 的语句已证明，但洞未填

客户端 `SmoothCoareaAudit.target_T3` 逐字复述并证明了路线的 T3，
`SmoothCoareaAudit.wip_isoperimetry_statement` 逐字复述并以**具名参数**证明了
`KLS/WIP/CheegerInfimum.lean` 中

```lean
theorem Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet
    {u : V → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ)
```

的语句：它由 L11 取 `S = univ` 并化简 `Set.univ_inter` 得到，**`hK` 这条 Lipschitz 假设
完全没有参与**——该声明本来就假设了 `ContDiff ℝ 1 u`。

**本轮没有动 WIP**，所以：

* 直接洞仍为 **2/3/5，总数 10**；该声明仍带 `sorry`。
* 准确说法是"**它的语句已在无洞模块基础上被证明，迁出即可闭合**"，
  不能说"C¹ coarea 洞已填"。迁出会把 `KLS/WIP/CheegerInfimum.lean` 从 3 洞降到 2 洞，
  总数 10 → 9，按仓库惯例（见 2026-09-15 的两次迁出决定）是单独一轮。

## 本轮没有做的事

* **没有证明 Lipschitz 情形**：`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  是对**全局 Lipschitz**（不假设 C¹）的 `u` 陈述的，仍是直接洞。它需要 **L12**，
  而 L12 需要 **L7** 的精确 C¹ 分片，L7 需要 **L6** 的闭集 Whitney 一阶 jet 延拓——
  L6/L6a/L7 全部未证明，本轮未动。
* 没有证明尖锐 `C^(finrank)` 的 `Analysis.sard`（仍带 `sorryAx`，仍无下游消费者）。
* 没有证明 Eilenberg 常数的尖锐性、`smoothConstant_le_minkowskiConstant`、
  `smoothConstant_mul_lintegral_min_superlevel_le`、两个 Cheeger 常数相等。
* 没有扩大证书或 Blueprint `leanok` 范围；证书仍 **24**，
  perimeter infrastructure 仍 **missing**。
* 没有修改任何已有 `.lean` 源码（只新增一个模块与一个客户端）。
* **没有提交、没有推送。**

## 验证

* `KLS/Geometry/SmoothCoarea.lean` 以 `-DwarningAsError=true` 单独编译通过。
* `research/audits/SmoothCoareaAudit.lean`（直接放进受版本控制的路径）以
  `-DwarningAsError=true` 编译通过：1 条语句 `#check`（逐字复述路线记录的 L11）与 11 条定理
  ——`target`、`target_of_not_completeSpace`、`target_T3`、`wip_isoperimetry_statement`、
  `top_weight`（`g ≡ ⊤`）、`empty_set`、`everywhere_critical`（常数函数，临界集是全空间）、
  `constant_function`（**独立于 L11** 地核对 `⊤ · 0` 边界：常数函数在所取水平上的切片是整条
  直线、表面测度无穷，而等式两端都是 `0`，因为例外水平集 Lebesgue 零测）、
  两条 `preserved_*` 具名参数签名检查——以及 12 条 `#print axioms`。
  全部 12 个声明只依赖 `propext`、`Classical.choice`、`Quot.sound`，**无 `sorryAx`**。
* 重跑其余 16 个审计客户端（`research/audits/` 10 条含本轮新增 + `build/audit/` 6 条），
  全部严格编译通过，未作任何修改；`LevelSetMeasurableAudit`、`SuperlevelSardScope` 中的
  `sorryAx` 是刻意报告仍开的洞。
* 三个 WIP 文件逐个实际编译成功，直接洞分别 **2/3/5，总数 10**。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过。最终回执为
  `build/verification/latest.json`，与最终全部源码快照完全一致；证据 JSON 为
  `research/explorations/2026-09-16-smooth-coarea.json`，最终核对另存
  `build/audit/smoothcoarea-final-snapshot.json`。
