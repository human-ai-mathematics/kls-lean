# Minkowski 余面积不等式

日期：2026-09-13。承接 [光滑恢复序列记录](2026-09-13-smooth-recovery-sequence.md)。
起始 HEAD 为 `2965b32`；上轮 passed 回执的 374 个文件与开始时的工作区快照逐一匹配
（含已删除的 `KLS/WIP/RelativePerimeter.lean`，其条目记为 `null`）。
保留此前未提交和未跟踪成果，本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

`KLS.Isoperimetry.lintegral_minkowskiContent_superlevel_le` 已证明，声明文本与原目标逐字一致：

```
theorem lintegral_minkowskiContent_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V)
```

全部数学范围保留：任意有限维实内积空间；**任意**概率测度，允许奇异与原子；`u` 只要求原有的
`C¹` 与全局 Lipschitz，没有加有界值域、紧支撑、非零维数、密度、绝对连续性、正维数、额外可积性
或超水平集边界零测的假设；左侧是**闭**超水平集，积分遍历整条实轴；`minkowskiContent` 的定义
（开增厚、ENNReal 截断减法、`𝓝[>] 0` 上的 liminf）一字未改。证明不使用加权 coarea、Sard 或任何
带 `sorryAx` 的 WIP 定理。

本轮把直接洞从 **16** 降到 **15**：AnalyticPrerequisites **3**、CheegerInfimum **7**、
Energy/WIP/Cheeger **5**。正式证书仍为 **24**，`lem:relative-perimeter-smoothing` 的
infrastructure 仍为 `missing`，整条 Cheeger 比较链**未**完成。

## 实际证明

记 `A t = {x | t ≤ u x}`，`v_r = ballSup u r`，`q_r = (v_r - u)/r`。

1. **局部上确界。** 新增 `ballSup u r x = sSup (u '' closedBall x r)`。全局 Lipschitz 给出
   `bddAbove_image_closedBall`（`u y ≤ u x + K r`，对任意实 `r` 成立，空球情形平凡），
   于是 `le_ballSup`（`u x ≤ v_r x`，`0 ≤ r`）与 `ballSup_le_add`（`v_r x ≤ u x + K r`），
   合起来给 `0 ≤ q_r ≤ K`。`lipschitzWith_ballSup` 用平移 `z ↦ z + (y - x)` 把一个闭球的成员
   送进另一个闭球，得到 `v_r` 与 `u` 同常数 Lipschitz，因此连续、可测。没有引入新的紧性、
   上确界或可测性基础设施，也没有使用有限维紧球或 Sard。
2. **近邻见证与条带。** `thickening_superlevel_subset`：
   `thickening r (A t) ⊆ {x | u x < t ∧ t ≤ v_r x} ∪ A t`。证明只用
   `Metric.mem_thickening_iff` 取出 `dist x z < r` 且 `t ≤ u z` 的见证 `z`，它落在 `closedBall x r`。
   由此对每个 `t`
   `ν(A_t^r) - ν(A_t) ≤ ν(S_r t)`，其中 `S_r t = {x | u x < t ∧ t ≤ v_r x}`；
   用 `tsub_le_iff_right` 与 `measure_union_le` 完成，**没有**先证
   `ν(A_t^r) - ν(A_t) = ν(A_t^r \ A_t)`，因而也不需要补集可测性。
3. **条带的联合可测性与 Tonelli。** 条带写成 `ℝ × V` 上的可测集
   `T_n = {p | u p.2 < p.1 ∧ p.1 ≤ v_{r_n} p.2}`（`u`、`v_{r_n}` 连续）。
   `measurable_measure_prodMk_left` 给出 `t ↦ ν (S_{r_n} t)` 可测——这正是绕过
   “`t ↦ minkowskiContent ν (A t)` 是否可测” 的地方：**Fatou 只作用在条带商上**，原被积函数
   只通过 `lintegral_mono` 的逐点比较进入，`∫⁻` 对任意函数都有定义，不需要它可测。
   `Measure.prod_apply` 与 `Measure.prod_apply_symm` 给
   `∫⁻ t, ν (S_{r_n} t) = ∫⁻ x, volume (Ioc (u x) (v_{r_n} x)) dν = ∫⁻ x, ofReal (v_{r_n} x - u x) dν`，
   常数因子用 `lintegral_mul_const'`（`(ofReal r_n)⁻¹ ≠ ⊤`）出入积分号，
   `ENNReal.ofReal_div_of_pos` 完成实数商与 ENNReal 商的换算。
4. **半径序列与两个方向的 liminf。** 取 `r n = 1/(n+1) > 0`，
   `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` 给 `r → 0` 在 `𝓝[>] 0` 中；
   `Tendsto.liminf_le_liminf_comp` 给出**正确方向**
   `liminf_{𝓝[>]0} f ≤ liminf_n f(r n)`（序列滤子更细，liminf 更大），
   因此原邻域定义只被**放大**，没有被替换成某个序列极限。
   随后 `lintegral_mono` + `lintegral_liminf_le`（Fatou，用到第 3 步的可测性）把逐点比较
   传到积分。
5. **梯度控制。** `limsup_ofReal_ballSup_le`：只证上界。由
   `hasGradientAt_iff_isLittleO_nhds_zero` 与 `Metric.eventually_nhds_iff` 取 `δ`，
   对 `‖h‖ ≤ r < δ` 有 `u(x+h) ≤ u x + ⟪∇u x, h⟫ + ε‖h‖ ≤ u x + (‖∇u x‖+ε) r`
   （`real_inner_le_norm`），故 `q_{r_n}(x) ≤ ‖∇u x‖ + ε` 最终成立，
   `ENNReal.le_of_forall_pos_le_add` 收尾。**没有**证明 `q_r → ‖∇u‖`，因为积分上界只需要上半连续那一侧。
   由 `0 ≤ q_{r_n} ≤ K` 与 `ν` 的概率性得支配函数 `ofReal K`（积分为 `ofReal K < ⊤`），
   `limsup_lintegral_le` 把 `limsup` 移进积分，最后 `liminf_le_limsup`。
   右端因此正是原声明的 `∫⁻ ‖gradient u‖ₑ dν`，不是任何粗糙的 `K` 上界。

## 分层、迁移与命名

* 新模块 `formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean` 无洞，
  **本地传递导入闭包为 0 个模块**：它只依赖 Mathlib，不导入任何 KLS 或 WIP 层。
* `minkowskiContent`、`measure_closure_eq_of_minkowskiContent_ne_top` 与新定理一并迁入该模块，
  命名空间仍为 `FunctionalInequalities.KLS.Isoperimetry`，**全名逐字不变**，
  因此没有兼容别名、转发声明或空壳模块，也没有重复证明。
  `measure_closure_eq_of_minkowskiContent_ne_top` 的证明原样移动，未改动。
* 未完成的 Cheeger 下确界比较（`minkowskiConstant`、`smoothConstant`、两条乘积不等式、
  两个方向的下确界比较）留在应用层 `KLS/WIP/CheegerInfimum.lean`，该文件改为直接导入新模块。
  `minkowskiConstant` 没有跟着下移：它此刻唯一的用途就是那些仍未完成的比较。
* 放在 `KLS/Geometry/` 而不是 `Analysis/`：迁移的是 `KLS.Isoperimetry` 命名空间下的既有公共定义，
  搬进 `Analysis/` 会连带改名。定理本身确实是 KLS 无关的分析结论，这一点由零本地导入闭包体现。
* `lintegral_minkowskiContent_superlevel_le` 的 `[FiniteDimensional ℝ V]` 在证明后成为未用的
  section 变量。沿用本仓库既有做法（`constant_eq_minkowskiConstant_intrinsic`），
  用 `set_option linter.unusedSectionVars false in` 静音 linter，**不改声明的数学范围**。

## 验证

* `lintegral_minkowskiContent_superlevel_le`、`minkowskiContent`、
  `measure_closure_eq_of_minkowskiContent_ne_top`、`ballSup` 及四条 `ballSup` 引理、
  `limsup_ofReal_ballSup_le` 的传递公理均为 `propext / Classical.choice / Quot.sound`，无 `sorryAx`。
* 新模块以 `lake env lean -DwarningAsError=true` 直接编译通过
  （`build/audit/minkowski-strict-MinkowskiContent.log`）。
* 新的独立客户端 `build/audit/MinkowskiCoareaAudit.lean` 同样严格编译，含 8 个客户端与
  18 条公理报告，全部只用标准三条公理：任意概率律（显式带上“对每个 Haar 测度都不绝对连续”
  与“`u` 值域无界”的假设）仍得结论；常函数给出零；零维（`Subsingleton V`）给出零；
  原子律（Dirac）右端化为该点的梯度范数；`ballSup u 0 = u`；近邻见证；
  任意正半径的增长商 `≤ K`；实轴上 `u = id` 给出全轴积分 `≤ 1`。
* 既有 `RecoveryAudit`、`DilationAudit`、`GaussGreenAudit` 三个客户端重跑，严格模式通过，
  14 + 17 + 22 条公理报告仍只用标准三条公理。
* 三个 WIP 文件实际普通模式重编译，诊断为 **3/7/5** 个直接洞，没有其他诊断
  （`build/audit/minkowski-wip-*.log`）；仍不是严格模式通过。
* 默认 `lake build` 通过（3393 jobs），随后从根目录 `python3 research/verify.py`；
  最终源码回执为 `build/verification/latest.json`。
  `research/tasks.json` 中 `lem:relative-perimeter-smoothing` 的证据加入新模块条目，
  gaps 改写为下一步的实际缺口，status 仍为 `missing`。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 下一项：`minkowskiConstant_mul_lintegral_min_superlevel_le` 还缺什么

目标：
```
minkowskiConstant ν * ∫⁻ t in Ioo 0 1, min (ν {u > t}) (1 - ν {u > t}) ≤ ∫⁻ ‖∇u‖ₑ dν
```
对 `C¹`、Lipschitz、`[0,1]` 值的 `u`。本轮结论是它的唯一分析输入；剩下的是测度论组装。

1. **开、闭超水平集质量几乎处处一致。** 需要的是
   `ν {x | t < u x} = ν {x | t ≤ u x}` 对 Lebesgue-几乎所有 `t` 成立。
   两个集合之差是 `{u = t}`，这些集合对不同的 `t` 两两不交，而 `ν` 有限，
   所以 `{t | ν {u = t} ≠ 0}` 可数，可数集 Lebesgue 零测。
   等价的路线是：`t ↦ ν {x | t < u x}` 反单调，反单调函数至多可数个不连续点，
   而 `ν {u ≥ t} = lim_{s↑t} ν {u > s}`。两条都不需要 `u` 有界或密度。
   这是下一轮唯一真正要证的新引理。
2. **零质量与满质量的层。** `minkowskiConstant` 的下确界只跑 `0 < ν B < 1`。
   当 `ν(A_t) ∈ {0, 1}` 时 `min (ν A_t) (1 - ν A_t) = 0`，逐点不等式退化为
   `h_M * 0 ≤ ν⁺(A_t)`，在 ENNReal 中恒真（`mul_zero` 对 `⊤` 同样成立）。
   因此**不需要**对这些层另作分类讨论，也不需要额外假设。
3. **ENNReal 中的 `⊤ * 0`。** 危险只在外层：若 `h_M = ⊤` 而整条积分为 `0`，左端是 `⊤ * 0 = 0`，
   结论平凡；若积分为正则必须避免把 `h_M` 从积分里除出去。正确写法是**不做除法**：
   先用 `lintegral_const_mul` 把常数 `h_M` 移进积分（需要被积函数可测，
   而 `t ↦ ν {u > t}` 反单调故可测，`min` 与 `1 - ·` 保持可测——`tendsto_lintegral_min_superlevel`
   的证明里已经有这段 `hFmeas`），再用 `lintegral_mono_ae` 配合第 1、2 步的逐点界，
   最后 `Measure.restrict_le_self` 把 `Ioo 0 1` 上的积分放大到全轴并接上本轮定理。
   这样 `⊤` 只在逐点层面出现一次，且被 `mul_zero` 正确吸收。
4. **下确界展开。** 对 `0 < ν(A_t) < 1` 的层，由 `iInf` 的定义得
   `h_M ≤ ν⁺(A_t) / min (ν A_t) (1 - ν A_t)`，再用 `ENNReal.le_div_iff_mul_le`
   （分母非零、非 `⊤`）换成乘法形式。需要 `MeasurableSet {x | t ≤ u x}`，由 `u` 连续给出。

## 再下一步：`minkowskiConstant_le_smoothConstant` 的组装

有了第 2 项之后，这条定理不再需要任何新的分析：固定中间质量的光滑域 `U`，
`P_ρ(U) = ⊤` 时商为 `⊤` 平凡；否则取本仓库已证明的
`RelativePerimeter.exists_smooth_recovery_sequence`（每项 `C^∞`、全局 Lipschitz、`[0,1]` 值），
逐项用第 2 项得 `h_M * I_j ≤ ∫ ‖∇u_j‖ dν`；已证明的
`tendsto_lintegral_min_superlevel` 把 `L¹(ν)` 收敛变成 `I_j → min (ν U) (1 - ν U)`；
`ENNReal.Tendsto.const_mul`（侧条件由 `ν U > 0` 给出 `min ≠ 0`）传到左端，
`limsup` 一侧用恢复序列的 `limsup ∫ ‖∇u_j‖ ≤ P_ρ(U)`，最后 `ENNReal.le_div_iff_mul_le`
与 `le_iInf` 收尾。

另一方向 `smoothConstant_le_minkowskiConstant` 仍需 `WIP/AnalyticPrerequisites` 的 Sard 与
加权 coarea，以及 `lintegral_enorm_gradient_distanceCutoff_le`；本轮没有任何进展。
因此不能把本轮表述为 coarea 公式、Cheeger 常数相等或整条比较链已证。
