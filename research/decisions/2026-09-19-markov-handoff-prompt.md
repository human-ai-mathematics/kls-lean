# 交接提示词：缺口二——对数凹律热半群的 Markov 性

> 本文件是一份可直接粘贴给下一会话的任务提示词（风格同 2026-09-19 的 `S5` 任务）。
> 写于 2026-09-19，半群路线 `S1`–`S8` 与 `T` 具体化完成之后。owner 尚未启动此任务。

---

任务：在 Lean 4 / Mathlib 中证明对数凹律热半群 `P_t` 的 Markov 性（保正、次 Markov、保常数）

## 目标

在仓库 `KLS`（`/Users/lyuyuwei/Documents/ChatGPT/KLS`）里新增模块，对 `KLS/LogConcave/HeatSemigroup.lean` 定义的
`P_t = hν.heatSemigroup m B hi ht : L²(ν) →L[ℝ] L²(ν)` 证明：

* **M-A（保正）** `0 ≤ f` ⟹ `0 ≤ P_t f`（`Lp` 的序，`MeasureTheory.Lp.coeFn_nonneg`）；
* **M-B（次 Markov）** `0 ≤ f ≤ 1` ⟹ `0 ≤ P_t f ≤ 1`；
* **M-C（保常数）** `P_t 1 = 1`，其中 `1 = L2.const ν 1`（`ν` 是概率测度所以 `1 ∈ L²`）；
* **M-D（推论）** `∫ P_t f dν = ∫ f dν`（对称 + M-C：`⟪P_t f, 1⟫ = ⟪f, P_t 1⟫`），`|P_t f| ≤ P_t |f|`，以及 `f ∈ L² ∩ L^∞` 时 `‖P_t f‖_∞ ≤ ‖f‖_∞`。

这是 `tasks.json` 里 `thm:logconcave-cheeger-poincare-comparison` 的**缺口二**。没有它，Ledoux/De Ponti–Mondino 证法里的逐点界无从谈起。
证完它**不是** Buser 不等式的任何一步，节点不得获得进展标记；缺口三（Γ 演算）、四（热估计）不在本任务内。

## 环境

* Lean `leanprover/lean4:v4.33.0`，Mathlib `v4.33.0`（pinned，不升级、不改 lakefile）。工作目录 `formalization/`。
* 单文件编译：`lake env lean -DwarningAsError=true <相对路径>.lean`，必须 0 错误 0 警告。
* 新模块建议放 `formalization/FunctionalInequalities/Analysis/Semigroup/Markov*.lean`（抽象部分）与
  `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroupMarkov.lean`（具体部分）。

## 已有的、你要建在上面的 API（全部零洞，`#print axioms` 标准）

半群（`Analysis/Semigroup/`，14 个模块）：
* `resolventCLM T hT hs` = `J_s = (1 + sT†T)⁻¹`，由弱方程 `WeakResolvent T s f u : ∀ v ∈ D(T), ⟪u,v⟫ + s⟪Tu,Tv⟫ = ⟪f,v⟫` 刻画
  （`Resolvent.lean`：`resolventDomain_spec`、`eq_resolventDomain`（唯一性）、`resolventCLM_apply`（rfl）、`norm_resolventCLM_le`、`resolventCLM_symm`）。
* `yosida T hT hs` = `L_s = s⁻¹(1 − J_s)`（`YosidaApproximation.lean`，`yosida_apply`）。
* `semigroupApply T hT hd t f` = `P_t f`（`Generated.lean`），`semigroupApply_spec`：`exp(−t•L_s) f → P_t f`（ε–δ）；
  `semigroupCLM`（`SemigroupLaws.lean`），`eq_semigroupApply_of_tendsto`（极限唯一）、`norm_semigroupApply_le`、`inner_semigroupApply_left`、`semigroupApply_add`。
* `exp(−t•L_s)` 相关：`Yosida.lean` 的 `norm_exp_neg_smul_apply_le`（压缩），`SemigroupLimit.lean` 的 `norm_exp_neg_smul_sub_le`。
  注意 `NormedSpace.exp_add_of_commute` 在 `H₀ →L[ℝ] H₀` 上缺实例，用 `exp_add_of_commute_of_mem_ball (𝕂 := ℝ)` + `expSeries_radius_eq_top ℝ _`；
  `exp(a•1) x = Real.exp a * x` 用 `NormedSpace.map_exp` 沿 `algebraMap` 传输。

具体算子（`KLS/LogConcave/WeightedGradient.lean`、`HeatSemigroup.lean`；底层 `Energy/WeightedGradient/{Basic,Core,Closable}.lean`，算子定义在 `Basic.lean` 的 `Energy.WeightedGradient.operator`）：
* `hν.weightedOperator m B hi : L²(ν) →ₗ.[ℝ] L²(ν; V)`，域是全局 Lipschitz 的 `L²` 检验函数类，作用 `g ↦ B ∘ ∇g`；
  `weightedOperator_isClosable`、`dense_domain_weightedOperator`。读 `Energy/WeightedGradient/Basic.lean`（`operator`）与 `Core.lean`（`smoothCore`、`constantSmoothCore`）弄清域与作用的精确定义。
* `hν.closedWeightedOperator m B hi` = 闭包 `T̄`；`heatSemigroup hν m B hi ht` = `semigroupCLM T̄ …`；`heatSemigroup_apply`（rfl）。
* 松弛：`weighted_relaxation_of_mem`：`f ∈ D(T̄)` ⟹ `(PreEnergy.ofLinearPMap T).sequentialRelaxation f = ‖T̄ f‖₊²`；
  `weighted_relaxation_of_notMem`：`f ∉ D(T̄)` ⟹ `= ⊤`。`sequentialRelaxation x = ⨅ (逼近序列 f), sequenceEnergy f`
  （`Energy/Relaxation/Basic.lean`，`sequenceEnergy` 是 liminf）。**这是 M1 的关键工具**，见下。
* 常数：`Energy.WeightedGradient.constantSmoothCore ν = smoothCore ν ⊔ span {L2.const ν 1}`，常数属于算子的域且梯度为零——确认 `T 1 = 0` 的精确引理名。

Mathlib 的 `Lp` 序结构：`MeasureTheory.Lp.instLattice`（`LpOrder.lean`），`Lp.coeFn_le`、`Lp.coeFn_nonneg`、`Lp.coeFn_sup`、`Lp.coeFn_inf`，
`Lp.posPart`/`coeFn_posPart`，`LipschitzWith.compLp (hg : LipschitzWith c g) (g0 : g 0 = 0) : Lp E p μ → Lp F p μ`，
`L2.const`/`Lp.const`/`indicatorConstLp`。

## 推荐证法：Beurling–Deny，经预解走

**M1（形式是 Markov 的：单位压缩在 `D(T̄)` 上作用）。** 对 `φ : ℝ → ℝ` 1-Lipschitz、`φ 0 = 0`（本任务只需
`φ = max(·, 0)`、`φ = min(·, 1)` 和 `φ = min(max(·,0),1)`，后两者需先平移或处理 `φ 0 ≠ 0`——`min(·,1)` 在 0 处为 0，无碍），
`u ∈ D(T̄)` ⟹ `φ ∘ u ∈ D(T̄)` 且 `‖T̄(φ∘u)‖ ≤ ‖T̄ u‖`。

推荐路线（避开 Lipschitz 函数的几乎处处链式法则与「梯度在水平集上为零」引理）：
1. 对 **光滑** 1-Lipschitz `ψ`（`ψ 0 = 0`，`|ψ'| ≤ 1`）与检验函数 `g`（全局 Lipschitz），`ψ ∘ g` 仍是检验函数，
   经典链式法则给 `∇(ψ∘g) = ψ'(g)∇g`，故 `‖B∇(ψ∘g)‖ ≤ ‖B∇g‖` 逐点，`‖T(ψ∘g)‖ ≤ ‖T g‖`。
2. 取光滑 1-Lipschitz `ψ_n → φ` 一致（磨光；或对 `max(·,0)` 直接写 `ψ_n(x) = (√(x²+1/n²) + x)/2 − 1/(2n)` 之类的显式族，
   显式族省掉磨光机器）。
3. 对 `u ∈ D(T̄)`，取检验函数 `g_k → u`（`L²`）且 `T g_k → T̄ u`（闭包的定义）。对角化：`ψ_{n(k)} ∘ g_k → φ ∘ u` 于 `L²`
   （`‖ψ_n∘g_k − φ∘g_k‖₂ ≤ ‖ψ_n − φ‖_∞`，`‖φ∘g_k − φ∘u‖₂ ≤ ‖g_k − u‖₂`），能量 `‖T(ψ_{n(k)}∘g_k)‖² ≤ ‖T g_k‖² → ‖T̄ u‖²`。
4. 按 `sequentialRelaxation` 的定义（逼近序列 liminf 能量的下确界），`relaxation(φ∘u) ≤ ‖T̄ u‖² < ⊤`，
   由 `weighted_relaxation_of_notMem` 的逆否得 `φ∘u ∈ D(T̄)`，再由 `weighted_relaxation_of_mem` 得 `‖T̄(φ∘u)‖ ≤ ‖T̄ u‖`。

这一步是本任务唯一的真实分析内容；其余是 Hilbert 空间代数与极限。

**M2（`J_s` 保正）。** `J_s f` 是 `F(u) = ‖u − f‖² + s‖T̄ u‖²` 在 `D(T̄)` 上的唯一极小点：由弱方程直接算
`F(v) − F(u) = ‖v − u‖² + s‖T̄(v−u)‖² ≥ 0`（无需紧性）。若 `f ≥ 0`，令 `u = J_s f`、`u⁺ = u ⊔ 0`：
逐点 `|u⁺ − f| ≤ |u − f|`（因 `f ≥ 0`），M1 给 `‖T̄ u⁺‖ ≤ ‖T̄ u‖`，故 `F(u⁺) ≤ F(u)`，唯一性 ⟹ `u⁺ = u` ⟹ `u ≥ 0`。

**M3（`J_s` 次 Markov）。** 同法，`φ = min(·,1)`：`f ≤ 1` ⟹ `J_s f ≤ 1`。

**M4（`J_s 1 = 1`）。** `1 ∈ D(T̄)`，`T̄ 1 = 0`（常数是检验函数，梯度零），所以 `u = 1` 满足数据为 `1` 的弱方程，唯一性。
推论 `L_s 1 = 0`、`exp(−t•L_s) 1 = 1`（`exp` 的级数逐项为零，或 `exp(−t•L_s) 1 − 1` 的导数为零）。

**M5（`exp(−t•L_s)` 保正、次 Markov）。** `−t•L_s = (−t/s)•1 + (t/s)•J_s`，二者交换，
`exp(−t•L_s) = e^{−t/s} · exp((t/s)•J_s) = e^{−t/s} Σ_k (t/s)^k/k! · J_s^k`（`NormedSpace.exp_eq_tsum`、`expSeries_apply_eq`，
作用到 `f` 上用 `ContinuousLinearMap.map_tsum` 或 `tsum` 的连续线性像）。每个 `J_s^k f ≥ 0`（M2 迭代），部分和 `≥ 0`，
极限 `≥ 0`——需要 **`L²` 的正锥闭**：对 `Lp`，`{f | 0 ≤ f}` 闭。Mathlib 里查 `Lp` 上 `OrderClosedTopology`/`isClosed_le`；
若无，用对偶刻画 `0 ≤ f ↔ ∀ g ≥ 0, 0 ≤ ⟪f, g⟫`（一方向用 `g = f⁻`）。次 Markov：`Σ e^{−t/s}(t/s)^k/k! · J_s^k f ≤ Σ e^{−t/s}(t/s)^k/k! · 1 = 1`。

**M6（`P_t`）。** `exp(−t•L_s) f → P_t f`（`semigroupApply_spec`），正锥闭 ⟹ `P_t f ≥ 0`；`≤ 1` 同理（`1 − exp(−t•L_s) f ≥ 0` 取极限）；
`P_t 1 = 1` 由 M4 与极限唯一性（`eq_semigroupApply_of_tendsto`）。

**M7（推论 M-D）。** `⟪P_t f, 1⟫ = ⟪f, P_t 1⟫ = ⟪f, 1⟫` 即 `∫ P_t f = ∫ f`；`|P_t f| ≤ P_t |f|` 由 `−|f| ≤ f ≤ |f|` 与保正、线性；
`L^∞` 界由次 Markov 对 `f/‖f‖_∞` 缩放。

## 已知的死路 / 摩擦

1. 不要试图证 Lipschitz 函数复合的几乎处处链式法则（需要「Lipschitz `g` 的梯度在 `{g = c}` 上几乎处处为零」，
   Mathlib 没有，仓库的 coarea 机器也不直接给）。走上面的光滑逼近 + 松弛定义。
2. `ContinuousLinearMap` 类型上的通用 `norm_*`/`dist_*` 引理常因实例菱形失配；保持逐点形式。
3. `push_neg`、`ContinuousLinearMap.mul_apply`、`.smul_apply`、`.neg_apply`、`.one_apply` 在本 pin 弃用即报错；`abs_add` 是 `abs_add_le`；
   `Dense.exists_dist_lt` 不存在（用 `Metric.mem_closure_iff`）；`div_le_div_iff` → `div_le_div_iff₀`；`real_inner_comm x y : ⟪y,x⟫ = ⟪x,y⟫`。
4. `-DwarningAsError` 门：`unusedSectionVars`（`omit … in` 写在 docstring **之前**）、`unusedSimpArgs`、`unnecessarySimpa`、`haveI` 用于 Prop 改 `have`。
5. 抽象部分（M2–M6 的 Hilbert 空间骨架）建议参数化：对任意闭稠定 `T` 与一个「单位压缩在 `D(T)` 上作用」的假设 `hM`（即 M1 的结论）
   证 `P_t` 保正与次 Markov，再在具体模块用 M1 消掉 `hM`。这样 M1 与 M2–M6 可以并行给两个证明会话。

## 交付与验收

1. 先写路线语句文件 `research/audits/MarkovRouteStatements.lean`（只含 `#check`，每条带证明草稿），编译通过后再分发证明。
2. 新模块零 `sorry`、零占位公理，`-DwarningAsError=true` 下 0 错误 0 警告，每条公开声明有 docstring，模块文档写明这是缺口二、不提供缺口三/四、不是 Buser 的任何一步。
3. 审计客户端逐字重述路线语句并消解，`#print axioms` 全部 `[propext, Classical.choice, Quot.sound]`。
4. 如实报告哪些路线假设未用、证法与草稿的差异。若某条路线语句为假（先例：`S6` 的抽象写法为假，见 `2026-09-19-yosida-limit-route.md` 的 `Y0`），
   路线文件保持字节不变，证正确版本并记录。
5. 集成由主会话做：聚合根 import、`lake build`、`tasks.json` 证据哈希与 `note`/`gap` 追加、决策记录、`verify.py`。
   `infrastructure.status` 保持 `missing` 直到缺口三、四也关闭。

## 不要做的事

* 不改 `FunctionalInequalities.lean`、`lakefile.toml`、`tasks.json`、Blueprint `.tex`，不 `git add/commit/push`，不 `lake build`、不 `verify.py`（证明会话）。
* 不碰缺口三（Γ 演算、`‖∇P_t f‖ ≤ P_t‖∇f‖`）与缺口四（`‖P_t f − f‖₁ ≤ C√t·TV(f)`、`‖∇P_t f‖_∞ ≤ Ct^{−1/2}‖f‖_∞`），
  也不要声称本条与 Buser 不等式的距离比实际更近。
