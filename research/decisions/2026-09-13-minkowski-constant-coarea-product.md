# Minkowski Cheeger 下确界的乘积余面积界

日期：2026-09-13。承接 [Minkowski 余面积记录](2026-09-13-minkowski-coarea-inequality.md)。
起始 HEAD 仍为 `2965b32`；上轮 passed 回执 `build/verification/latest.json` 的 376 个文件条目与
开始时的工作区快照逐字匹配（`snapshot.sha256` 相同）。保留此前未提交与未跟踪成果，
本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

`KLS.Isoperimetry.minkowskiConstant_mul_lintegral_min_superlevel_le` 已证明，声明文本与原目标
逐字一致：

```
theorem minkowskiConstant_mul_lintegral_min_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) :
    minkowskiConstant ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V)
```

迁移前后的 `pp.all` 签名（`minkowskiConstant`、`minkowskiConstant_eq_top_of_subsingleton` 与本目标
三条）逐字节相同，`diff` 为空。全部数学范围保留：任意有限维实内积空间；**任意**概率测度，允许
奇异与原子；`u` 只要求原有的 `C¹`、全局 Lipschitz 与 `[0,1]` 值域。没有加密度、绝对连续性、
非原子性、正维数、`minkowskiConstant` 有限或非零、超水平集边界零测等假设，`minkowskiConstant`
的 admissible sets（Borel、`0 < ν B < 1`）与 `minkowskiContent` 的定义一字未改。证明不使用光滑
恢复序列、加权 coarea、Sard，也不使用任何带 `sorryAx` 的 WIP 定理。

本轮把直接洞从 **15** 降到 **14**：AnalyticPrerequisites **3**、CheegerInfimum **6**、
Energy/WIP/Cheeger **5**。正式证书仍为 **24**，`lem:relative-perimeter-smoothing` 的
infrastructure 仍为 `missing`，整条 Cheeger 比较链**未**完成。

## 实际证明

记 `m(a) = min {a, 1 - a}`，`A_t = {x | t ≤ u x}`，`I = ∫⁻_{Ioo 0 1} m(ν{u > t}) dt`。

1. **开、闭超水平集质量几乎处处一致**（`ae_measure_superlevel_lt_eq_le`）。声明取到实际依赖的
   最弱形式：对**任意** `[SFinite μ]` 的 `Measure V` 和**任意可测** `u`（不需要连续、有界值域或
   密度）
   `∀ᵐ t ∂volume, μ {x | t < u x} = μ {x | t ≤ u x}`。
   证明用 Mathlib 的 `MeasureTheory.Measure.countable_meas_level_set_pos`（水平集
   `{u = t}` 两两不交，s-有限测度只给可数多个正质量），`Set.Countable.measure_zero` 把可数集变成
   Lebesgue 零测，再由 `{u ≥ t} ⊆ {u > t} ∪ {u = t}` 与 `measure_union_le` 得等号。
   结论在全实轴上成立，第 3 步通过 `ae_restrict_of_ae` 限制到 `Ioo 0 1`。
2. **下确界的乘积形式**（`minkowskiConstant_mul_min_le`）。对任意可测 `B`
   `minkowskiConstant ν * m(ν B) ≤ minkowskiContent ν B`。
   分类只有两支：`m(ν B) = 0` 时 `mul_zero` 直接收尾，`⊤ * 0 = 0` 在 ENNReal 中成立，因此零质量
   与满质量的层**不需要**代入下确界，admissible sets 也没有被放宽；`m(ν B) ≠ 0` 时由
   `min` 的两个分量非零推出 `0 < ν B` 与 `ν B < 1`（用 `prob_le_one`），`iInf_le` 加三次
   `iInf_pos` 给出 `h_M ≤ ν⁺(B) / m(ν B)`，再用 `ENNReal.le_div_iff_mul_le`
   （侧条件 `m ≠ 0`、`m ≠ ⊤`，后者由 `m ≤ 1`）换成乘法形式。全程不做除法消去 `h_M`。
3. **平衡量的可测性**（`measurable_min_measure_superlevel`）。`t ↦ ν {x | t < u x}` 反单调、
   `t ↦ 1 - ν {x | t < u x}` 单调，`Antitone.measurable.min Monotone.measurable`。对**任意**
   `u : V → ℝ` 成立，不要求 `u` 可测。这段原先内联在 `tendsto_lintegral_min_superlevel` 的
   `hFmeas` 里；本轮把它提取为公共引理并**迁移原消费者**，WIP 里的那三行被替换成对新引理的调用，
   没有复制证明。
4. **组装**。`lintegral_const_mul`（被积函数可测由第 3 步给出）把 `h_M` 移进积分——这是唯一一处
   会出现 `⊤ * I` 的地方，移进去之后 `⊤` 只在逐点层面与 `m = 0` 相遇并被 `mul_zero` 吸收；
   `lintegral_mono_ae` 配合第 1、2 步的逐点界换成闭超水平集的 content；
   `setLIntegral_le_lintegral` 把 `Ioo 0 1` 上的积分放大到全实轴；最后接上已证的
   `lintegral_minkowskiContent_superlevel_le`。右端被积函数
   `t ↦ minkowskiContent ν {u ≥ t}` **没有**被假设可测：`lintegral_mono_ae` 与
   `setLIntegral_le_lintegral` 对任意函数都成立。全程不使用除法、不使用缺少侧条件的 ENNReal
   连续性或乘除法规则。

`hu01` 是原声明固定数学范围的一部分，证明只用到把层积分限制在 `Ioo 0 1`，因此该假设在证明中
未被使用。沿用本仓库既有做法，用 `set_option linter.unusedVariables false in` 静音 linter，
**不缩小声明范围**、不改名、不加下划线前缀。

## 分层与迁移

* 新模块 `formalization/FunctionalInequalities/KLS/Geometry/MinkowskiConstant.lean` 无洞，
  本地导入闭包恰为 **1** 个模块：同样无洞的 `Geometry/MinkowskiContent.lean`（其自身闭包为空）。
  没有恢复序列、Sard、加权 coarea、相对周长或任何 WIP 依赖。
* `minkowskiConstant` 与 `minkowskiConstant_eq_top_of_subsingleton` 从 `KLS/WIP/CheegerInfimum.lean`
  **原样迁入**新模块，命名空间仍为 `FunctionalInequalities.KLS.Isoperimetry`，全名与 `pp.all`
  签名逐字不变，因此没有兼容别名、转发声明、空壳模块或重复证明。`minkowskiConstant` 这一轮下移，
  正是因为本轮结论必须无洞，而完成的定理不能反向导入 WIP 模块。
* 新增的三条基础引理（第 1、2、3 步）与本轮结论一并放在该模块。
* `smoothConstant`、`smoothConstant_eq_top_of_subsingleton`、层积分恒等式
  `lintegral_measure_symmDiff_superlevel`、`min_measure_le_add_measure_symmDiff`、
  `tendsto_lintegral_min_superlevel`、距离截断、以及两条未完成的比较仍留在应用层
  `KLS/WIP/CheegerInfimum.lean`，该文件改为导入新模块（`MinkowskiContent` 由新模块传递提供）。
  `smoothConstant` 没有跟着下移：它此刻的用途仍是那些未完成的比较。
* 放在 `KLS/Geometry/` 而不是 `Analysis/`：迁移的是 `KLS.Isoperimetry` 命名空间下的既有公共定义，
  搬进 `Analysis/` 会连带改名。

## 验证

* `minkowskiConstant`、`minkowskiConstant_eq_top_of_subsingleton`、`minkowskiConstant_mul_min_le`、
  `ae_measure_superlevel_lt_eq_le`、`measurable_min_measure_superlevel`、
  `minkowskiConstant_mul_lintegral_min_superlevel_le`、`minkowskiContent`、
  `lintegral_minkowskiContent_superlevel_le` 的传递公理均为
  `propext / Classical.choice / Quot.sound`，无 `sorryAx`。
* 新模块与既有的 `Geometry/MinkowskiContent.lean` 都以
  `lake env lean -DwarningAsError=true` 直接编译通过
  （`build/audit/minkowski-constant-strict-MinkowskiConstant.log`、
  `build/audit/minkowski-constant-strict-MinkowskiContent.log`）。
* 新的独立客户端 `build/audit/MinkowskiConstantAudit.lean` 同样严格编译，含 9 个客户端与
  17 条公理报告，全部只用标准三条公理：显式带“对每个 Haar 测度都不绝对连续”与“存在原子”的
  奇异原子律仍得结论；空集与全空间的零平衡量（`⊤ * 0 = 0`，下确界不被代入不可取集）；
  零维（`Subsingleton V`，`h_M = ⊤`）**推出**层平衡积分为零；常函数同样把层平衡积分压成零；
  Dirac 律右端化为该点的梯度范数；显式假设 `h_M = ⊤` 且右端有限时层平衡积分必为零（`⊤` 的合法
  使用，不做除法）；Dirac 律上的开闭超水平集几乎处处一致；任意 `u` 的平衡量可测；`V = ℝ` 的
  一维实例。
* 既有客户端 `MinkowskiCoareaAudit`、`RecoveryAudit`、`DilationAudit`、`GaussGreenAudit` 重跑，
  严格模式通过，18 + 14 + 17 + 22 条公理报告仍只用标准三条公理。
* 三个 WIP 文件实际普通模式重编译，诊断为 **3/6/5** 个直接洞，没有其他诊断
  （`build/audit/minkowski-constant-wip-*.log`）；仍不是严格模式通过。
* 默认 `lake build` 通过，随后从根目录 `python3 research/verify.py`；最终源码回执为
  `build/verification/latest.json`。`research/tasks.json` 中 `lem:relative-perimeter-smoothing`
  的证据加入新模块条目，gaps 改写为下一步的实际缺口，status 仍为 `missing`。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 下一项：`minkowskiConstant_le_smoothConstant` 的精确组装

目标 `minkowskiConstant ν ≤ smoothConstant ρ (interior ν.support) ν`。本轮结论是它的最后一个
分析输入；现已核对过全部 API，剩下的确实都是组装，但组装本身有五处必须写出的侧条件，**不能**
把它当成已经完成。

1. **外层三次 `le_iInf`。** `smoothConstant` 是 `⨅ U, ⨅ (0 < ν U.carrier), ⨅ (ν U.carrier < 1), …`。
   固定这样的 `U`，令 `m = min (ν U.carrier) (1 - ν U.carrier)`。由 `0 < ν U.carrier` 与
   `ν U.carrier < 1` 得 `m ≠ 0`，由 `m ≤ 1` 得 `m ≠ ⊤`，于是
   `ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)` 把目标换成 `h_M * m ≤ P_ρ(U)`。
   这里既不假设 `h_M` 有限，也不做除法。
2. **相对周长为 `⊤` 的情形。** `exists_smooth_recovery_sequence` 的第三个参数就是
   `relativePerimeter ρ (interior ν.support) U ≠ ⊤`，所以必须先分类：`P_ρ(U) = ⊤` 时
   `h_M * m ≤ ⊤` 由 `le_top` 平凡，恢复序列根本不被调用；只有 `P_ρ(U) ≠ ⊤` 的分支取序列。
3. **恢复序列的三项拆包。** `exists_smooth_recovery_sequence hρ U hPne` 给出 `u : ℕ → V → ℝ` 与
   `∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K : ℝ≥0, LipschitzWith K (u j)) ∧ ∀ x, u j x ∈ Icc 0 1`，
   `Tendsto (fun j ↦ ∫⁻ ‖u j - 𝟙_{U.carrier}‖ₑ dν) atTop (𝓝 0)`，以及
   `limsup (fun j ↦ ∫⁻ ‖∇(u j)‖ₑ dν) atTop ≤ P_ρ(U)`。
   逐项应用本轮定理需要把 `ContDiff ℝ ∞` 降到 `ContDiff ℝ 1`：`ContDiff.of_le` 的侧条件是
   `(1 : WithTop ℕ∞) ≤ ∞`，**`le_top` 不适用**（`∞` 不是该类型的 `⊤`，`ω` 才是），已核实
   `(by simp)` 可以给出。Lipschitz 常数要从 `∃ K` 里取出来。由此
   `h_M * I_j ≤ ∫⁻ ‖∇(u j)‖ₑ dν`，其中 `I_j = ∫⁻_{Ioo 0 1} m(ν{u_j > t}) dt`。
4. **把 L¹ 收敛传到平衡量。** 已证明的 `tendsto_lintegral_min_superlevel` 给
   `Tendsto I_j atTop (𝓝 m)`，它要求每个 `u j` 可测（由 `ContDiff → Continuous → Measurable`）、
   `[0,1]` 值、`B = U.carrier` 可测（`U.isOpen.measurableSet`，`SmoothDomain` 的 `isOpen` 字段），
   以及上面的 L¹ 收敛。注意该引理目前仍住在 `KLS/WIP/CheegerInfimum.lean`，但其本身无洞、
   无传递 `sorryAx`。
5. **常数乘法的极限与 limsup 比较。** `ENNReal.Tendsto.const_mul`（签名已核实为
   `Tendsto m f (𝓝 b) → b ≠ 0 ∨ a ≠ ⊤ → Tendsto (fun x ↦ a * m x) f (𝓝 (a * b))`）用
   `Or.inl hm0` 作侧条件——这正是 `h_M = ⊤` 时仍然合法的地方，因为极限 `m` 非零；
   `Filter.Tendsto.limsup_eq`（`atTop` 在 `ℕ` 上 `NeBot`）把 `h_M * m` 写成
   `limsup (fun j ↦ h_M * I_j)`，`Filter.limsup_le_limsup`（`ℝ≥0∞` 完备，两个
   `autoParam` 的有界性侧条件由 `isBoundedDefault` 自动给出）配第 3 步的逐项界，得
   `h_M * m ≤ limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ P_ρ(U)`。

因此真正剩余的不是新数学，而是上述 2、3、5 三处侧条件的具体书写，以及一个**分层决定**：
组装完成后 `minkowskiConstant_le_smoothConstant` 将无传递 `sorryAx`，但它与它依赖的
`tendsto_lintegral_min_superlevel`、`lintegral_measure_symmDiff_superlevel`、
`min_measure_le_add_measure_symmDiff`、`smoothConstant` 仍在 WIP 模块里，届时应按本仓库既有做法
把这一组连同消费者迁入无洞层，而不是留在 WIP 里带着已填的体。

另一方向 `smoothConstant_le_minkowskiConstant` 仍需 `WIP/AnalyticPrerequisites` 的 Sard 与加权
coarea，以及 `lintegral_enorm_gradient_distanceCutoff_le` 与
`smoothConstant_mul_lintegral_min_superlevel_le`；本轮没有任何进展。因此不能把本轮表述为
coarea 公式、Cheeger 常数相等或整条比较链已证。
