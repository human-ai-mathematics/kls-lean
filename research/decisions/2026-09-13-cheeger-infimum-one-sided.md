# Cheeger 下确界的一个方向：`h_M ≤ h_S`

日期：2026-09-13。承接 [Minkowski 常数记录](2026-09-13-minkowski-constant-coarea-product.md)。
起始 HEAD 仍为 `2965b32`；上轮 passed 回执 `build/verification/latest.json` 的 378 个文件条目与
开始时的工作区快照逐字匹配（`snapshot.sha256` 相同）。保留此前未提交与未跟踪成果，
本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

`KLS.Isoperimetry.minkowskiConstant_le_smoothConstant` 已证明，声明文本与原目标逐字一致：

```
theorem minkowskiConstant_le_smoothConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    minkowskiConstant ν ≤ smoothConstant ρ (interior (ν : Measure V).support) ν
```

迁移前后六条声明（`smoothConstant`、`smoothConstant_eq_top_of_subsingleton`、
`lintegral_measure_symmDiff_superlevel`、`min_measure_le_add_measure_symmDiff`、
`tendsto_lintegral_min_superlevel`、本目标）的 `pp.all` 签名逐字节相同，`diff` 为空——包括本目标
本身：它此前是 `sorry`，section 变量因而全部保留；填体之后 `unusedSectionVars` 没有报告任何未用
变量，所以类型与假设一个没变、一个没加。

全部数学范围保留：任意有限维实内积空间，**含零维**；对 Lebesgue `volume` 的任意 Borell 概率密度；
没有加支撑有界、区域有界、边界总测度有限、常数有限或正值、存在中间质量光滑域、相对周长有限等
任何假设；`smoothConstant` 的 `iInf` 定义、`relativePerimeter` 的归一化、
`Ω = interior ν.support` 与全部 admissible sets 一字未改。证明不使用反方向比较、加权 coarea、
Sard，也不使用任何带 `sorryAx` 的 WIP 定理。

本轮把直接洞从 **14** 降到 **13**：AnalyticPrerequisites **3**、CheegerInfimum **5**、
Energy/WIP/Cheeger **5**。正式证书仍为 **24**。**只证明了一个方向**：
`smoothConstant_le_minkowskiConstant` 与 `minkowskiConstant_eq_smoothConstant` 仍是 `sorry`／
传递依赖 `sorryAx`，`lem:relative-perimeter-smoothing` 的 infrastructure 仍为 `missing`，
整条 Cheeger 比较链**未**完成，两个 Cheeger 常数相等**未**证。

## 实际证明

记 `m = min (ν U.carrier) (1 - ν U.carrier)`，`P = relativePerimeter ρ (interior ν.support) U`。

1. **展开与除法转换。** `simp only [smoothConstant]` 后三次 `le_iInf` 固定任意
   `U : SmoothDomain V` 与 `0 < ν U.carrier`、`ν U.carrier < 1`。`lt_min hUpos (tsub_pos_of_lt hUlt)`
   给 `m ≠ 0`，`m ≤ 1` 与 `prob_le_one` 给 `m ≠ ⊤`，
   `ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)` 把目标换成 `h_M * m ≤ P`。
   **没有**为此增加非空性或正维数假设：当没有可取光滑域时，`le_iInf` 的前提是空的，目标自动为
   `h_M ≤ ⊤`，由 `iInf` 结构本身覆盖。
2. **`P = ⊤` 的分支。** `rcases eq_or_ne P ⊤`，`⊤` 一支由 `le_top` 直接收尾，
   `RelativePerimeter.exists_smooth_recovery_sequence` **只在** `P ≠ ⊤` 的一支被调用。
   它的有限周长参数因此始终是分支内的局部事实，没有被提升成定理的前提。
3. **恢复序列与逐项界。** 拆包得 `u : ℕ → V → ℝ`，每项 `ContDiff ℝ ∞`、各自存在
   `∃ K : ℝ≥0, LipschitzWith K (u j)`（不要求对 `j` 一致）、`[0,1]` 值、`L¹(ν)` 收敛到 `𝟙_{U.carrier}`、
   `limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ P`。降阶用 `ContDiff.of_le`，其侧条件是
   `(1 : WithTop ℕ∞) ≤ ∞`——注意 `∞` 不是该类型的 `⊤`（`ω` 才是），`le_top` 不适用，本轮实际用的是
   `(by simp)`。逐项应用上一轮的 `minkowskiConstant_mul_lintegral_min_superlevel_le` 得
   `h_M * I_j ≤ ∫⁻ ‖∇(u j)‖ₑ dν`，其中 `I_j = ∫⁻_{Ioo 0 1} min (ν{u_j > t}) (1 - ν{u_j > t}) dt`。
4. **平衡量收敛。** 直接复用已证的 `tendsto_lintegral_min_superlevel`，前提由现有正则性给出：
   可测性 `(hureg j).1.continuous.measurable`、`[0,1]` 值 `(hureg j).2.2`、
   `U.carrier` 可测 `U.isOpen.measurableSet`，以及第 3 步的 `L¹` 收敛。得 `I_j → m`。
   没有重新证明 layer-cake 或平衡量收敛。
5. **常数乘法与 limsup。** `ENNReal.Tendsto.const_mul hItend (Or.inl hm0)`——侧条件由 `m ≠ 0` 给出，
   这正是 `h_M = ⊤` 时仍然合法的地方，全程**没有**假设或推出 `h_M` 有限，也**没有**除以 `h_M`。
   随后 `Tendsto.limsup_eq`（`atTop` 在 `ℕ` 上 `NeBot`）把 `h_M * m` 写成
   `limsup (fun j ↦ h_M * I_j)`，`limsup_le_limsup (Eventually.of_forall hstep)`（`ℝ≥0∞` 完备，
   两个 `autoParam` 有界性侧条件自动）接到 `limsup ∫⁻ ‖∇(u j)‖ₑ dν`，最后接恢复序列的上界得 `≤ P`。
   没有交换未经证明的极限与积分。

## 分层与迁移

* 新模块 `formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean` 无洞，
  本地导入闭包 32 个模块，**其中没有任何 WIP 模块**；它只在既有的两条无洞链
  `Geometry/PerimeterRecovery`（恢复序列）与 `Geometry/MinkowskiConstant`（乘积余面积界）之上。
* 迁入该模块的是本轮结论实际依赖的最小集合：`smoothConstant`、
  `smoothConstant_eq_top_of_subsingleton`、`lintegral_measure_symmDiff_superlevel`、
  `min_measure_le_add_measure_symmDiff`、`tendsto_lintegral_min_superlevel`。证明原样移动，
  命名空间仍为 `FunctionalInequalities.KLS.Isoperimetry`，全名与 `pp.all` 签名逐字不变，
  因此没有兼容别名、转发证明、空壳模块或复制辅助证明。
* `Geometry/MinkowskiConstant.lean` **未被改动**：光滑恢复、相对周长与任何 WIP 依赖都没有被塞进
  这一基础层，它的本地闭包仍只有 `Geometry/MinkowskiContent`。
* 留在应用层 `KLS/WIP/CheegerInfimum.lean` 的是：Sard 与加权 coarea 的两条 KLS 侧义务、
  距离截断 `distanceCutoff` 及其引理与 `lintegral_enorm_gradient_distanceCutoff_le`、
  已证的 `exists_smooth_approximation_lipschitz`、反方向的
  `smoothConstant_mul_lintegral_min_superlevel_le` 与 `smoothConstant_le_minkowskiConstant`、
  等式 `minkowskiConstant_eq_smoothConstant` 及仿射支撑传输段。该文件改为只导入新模块
  （`MinkowskiConstant` 与 `PerimeterRecovery` 由新模块传递提供）。
* 放在 `KLS/Geometry/` 而不是 `Analysis/`：迁移的是 `KLS.Isoperimetry` 命名空间下的既有公共定义，
  搬进 `Analysis/` 会连带改名。文件名与 WIP 同名但路径不同，两者的角色在各自的模块 docstring 里
  写明。

## 验证

* `smoothConstant`、`smoothConstant_eq_top_of_subsingleton`、`lintegral_measure_symmDiff_superlevel`、
  `min_measure_le_add_measure_symmDiff`、`tendsto_lintegral_min_superlevel`、
  `minkowskiConstant_le_smoothConstant`、`RelativePerimeter.exists_smooth_recovery_sequence`、
  `minkowskiConstant_mul_lintegral_min_superlevel_le` 的传递公理均为
  `propext / Classical.choice / Quot.sound`，无 `sorryAx`。
* 新模块以及 `Geometry/MinkowskiContent`、`Geometry/MinkowskiConstant`、
  `Geometry/PerimeterRecovery` 都以 `lake env lean -DwarningAsError=true` 编译通过
  （`build/audit/cheeger-infimum-strict-*.log`）。
* 迁移前后的 `#check` 输出（`set_option pp.all true`）逐字节 `diff` 为空，确认 section 变量没有
  变化，没有无意增加假设或改变类型。
* 新的独立客户端 `build/audit/CheegerInfimumAudit.lean` 严格编译通过，含 6 个客户端与 14 条公理
  报告，全部只用标准三条公理：一般情形（显式带“支撑无界”假设）；零维（两个下确界都是 `⊤`，
  比较化为 `⊤ ≤ ⊤`）；**没有**可取光滑域时 `smoothConstant = ⊤`（由 `iInf` 结构本身，不需要存在性
  假设）；单个可取域相对周长为 `⊤` 时该项商为 `⊤`、对下确界无约束；某个可取域相对周长为 `0` 时
  推出 `minkowskiConstant = 0`；`minkowskiConstant = ⊤` 时推出每个可取光滑域的相对周长都是 `⊤`
  （`⊤` 的合法使用，不做除法）。客户端不为测试给生产定理添加任何假设。
* 既有客户端 `MinkowskiConstantAudit`、`MinkowskiCoareaAudit`、`RecoveryAudit`、`DilationAudit`、
  `GaussGreenAudit` 重跑，严格模式通过，17 + 18 + 14 + 17 + 22 条公理报告仍只用标准三条公理。
* 三个 WIP 文件实际普通模式重编译，诊断为 **3/5/5** 个直接洞，没有其他诊断
  （`build/audit/cheeger-infimum-wip-*.log`）；仍不是严格模式通过。
* 默认 `lake build` 通过，随后从根目录 `python3 research/verify.py`；最终源码回执为
  `build/verification/latest.json`。`research/tasks.json` 中 `lem:relative-perimeter-smoothing`
  的证据加入新模块条目，gaps 改写为下一步的实际缺口，status 仍为 `missing`。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 反方向的精确依赖

`smoothConstant_le_minkowskiConstant` 的路线是：对每个中间质量的 Borel 集 `B`，用距离截断
`w_r = (1 - d(·,B)/r)₊` 逼近 `𝟙_B`，把 `w_r` 换成光滑替身，再用 `h_S` 一侧的余面积不等式。
其依赖分成三类，必须区分：

**(a) 已经具备、不需要再证的输入。** `exists_smooth_approximation_lipschitz` **已证明**
（由 `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`，该结论已认证且无
`sorryAx`）：它把全局 Lipschitz、`[0,1]` 值的 `w` 换成逐项 `C^∞`、Lipschitz、`[0,1]` 值且
`L¹(ν)` 收敛、梯度积分收敛的序列，只需要 `ν ≪ m`（`m` 为 Haar）。距离截断的值域、Lipschitz
常数、在 `closure B` 上取 `1`、在 `thickening r B` 外取 `0` 以及
`tendsto_distanceCutoff_indicator` 也都已证明。本轮新证的
`tendsto_lintegral_min_superlevel` 一侧同样可以直接复用。

**(b) 仍需独立证明的三处。** 距离截断的梯度积分估计
`lintegral_enorm_gradient_distanceCutoff_le`；加权 coarea 公式
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 及其水平集积分的可测性
`Analysis.aemeasurable_lintegral_levelSet`；以及 Sard `Analysis.sard`
（`Analysis.ae_forall_fderiv_ne_zero` 与 `SmoothDomain.ae_exists_superlevel` 已填体，但传递依赖
`sorryAx`，随 Sard 一并消去）。后两类是真正的大块分析基础设施。

**(c) 组装层。** `smoothConstant_mul_lintegral_min_superlevel_le` 同时需要 Sard 与加权 coarea，
再往上才是 `smoothConstant_le_minkowskiConstant`。

### 选定的最小后续目标：`lintegral_enorm_gradient_distanceCutoff_le`

边界最清楚、且不依赖 Sard 或 coarea 的，是 (b) 中的第一条。原声明（在
`KLS/WIP/CheegerInfimum.lean`，本轮未改动）：

```
theorem lintegral_enorm_gradient_distanceCutoff_le (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) (B : Set V) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r
```

它消去的缺口是反方向链条上的距离截断梯度估计——`smoothConstant_le_minkowskiConstant` 三块缺口
中唯一与 Sard／coarea 无关的一块，因此可以独立完成，且完成后 `WIP/CheegerInfimum` 的直接洞
从 5 降到 4，而 Sard 与 coarea 的状态不变。

关键依赖与路线（已核对 Mathlib 名称，`v4.33.0`）：

1. `B = ∅` 单独一支：`Metric.infDist_empty` 给 `d ≡ 0`，于是 `w_r ≡ 1` 为常函数，左端为 `0`；
   右端是 `(0 - 0)/ofReal r = 0`。因此**不需要**给声明加非空性假设。
2. `B` 非空时写 `d x = Metric.infDist x B`（`1`-Lipschitz、连续）。
   由 `Metric.mem_closure_iff_infDist_zero` 与 `Metric.mem_thickening_iff_infDist_lt`：
   `closure B = {d = 0}`，`thickening r B = {d < r}`，而
   `{x | 0 < w_r x ∧ w_r x < 1} = {0 < d < r} = thickening r B \ closure B`，**是开集**（`d` 连续）。
3. **关键的一步不需要 Lebesgue 密度定理**：`w_r` 的值域是 `[0,1]`，在 `closure B` 上取到全局
   最大值 `1`，在 `{d ≥ r}` 上取到全局最小值 `0`。因此在这两个集合的**任何**可微点上，
   `IsLocalMax.fderiv_eq_zero` 与 `IsLocalMin.fderiv_eq_zero`（均已确认存在于 Mathlib）直接给出
   `fderiv = 0`，从而 `gradient = 0`。Mathlib 没有“Lipschitz 函数在水平集上梯度几乎处处为零”的
   一般引理，而这里根本用不到它——这是这个目标边界清楚的原因。
4. 可微性：`LipschitzWith.ae_differentiableAt`（Rademacher）在 Mathlib 中是**对任意
   `[μ.IsAddHaarMeasure]` 的 `μ`** 陈述的，所以可以直接取 `μ = m` 得 `∀ᵐ x ∂m, DifferentiableAt ℝ w_r x`，
   再由 `hac : ν ≪ m` 转成 `ν`-几乎处处。不需要在 Haar 与 `volume` 之间做任何比较，
   `hac` 正是在这里、也只在这里被用到。
5. 收尾：`lintegral_mono_ae` 把被积函数换成 `(A.indicator fun _ ↦ (1/r 的 ENNReal 形式))`，其中
   `A = thickening r B \ closure B`；`lipschitzWith_distanceCutoff`（已证，常数 `1/r`）给出可微点上
   `‖∇w_r‖ ≤ 1/r`（`LipschitzWith` 到 `‖fderiv‖ ≤ K`）；`lintegral_indicator_const` 得
   `(1/r) * ν A`；`measure_diff`（`closure B ⊆ thickening r B` 由 `Metric.closure_subset_thickening hr`、
   可测性由闭集与开集、有限性由概率测度）给 `ν A = ν (thickening r B) - ν (closure B)`；
   最后 `ENNReal.div_eq_inv_mul` 一类的换算对上右端。

其余两块（加权 coarea 与 Sard）不在这一目标范围内，本轮也没有任何进展；在它们完成之前，
`smoothConstant_le_minkowskiConstant`、`minkowskiConstant_eq_smoothConstant`、
`constant_eq_smoothConstant_intrinsic` 与 `inverseScale_eq_inv_smoothConstant_intrinsic`
都仍然传递依赖 `sorryAx`，不能表述为 Cheeger 常数相等或整条比较链已证。
