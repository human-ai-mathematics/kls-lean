# 半群生成路线：已完成部分与交接清单

2026-09-19。本文件划分**本会话已证**与**移交他处**的边界，并给出后者的精确规格。
起点与终点均为 `HEAD = origin/main = 7986adf`（工作区未提交）。

## 一、已证（高置信，已验证）

模块 `Analysis/Semigroup/{Form,Resolvent}.lean`，审计 `research/audits/SemigroupFormAudit.lean`。

| 编号 | 声明 | 备注 |
| --- | --- | --- |
| `S1` | `completeSpace_graph` | 一行：`IsClosed` 按定义即图闭 |
| `S2` | `min_one_mul_graphNormSq_le` | **不需要 `0 < s`**，对任意实 `s` 成立 |
| `S3` | `existsUnique_weakResolvent` | **不需要 `Dense`**；用正交投影，非 Lax–Milgram |
| `S4` | `norm_le_of_weakResolvent`、`inner_nonneg_of_weakResolvent` | 弱方程取 `v = u` |
| 路线外 | `resolventCLM` + 压缩/自伴/非负三条 | `J_s = (1 + sT*T)⁻¹` 打包成 `H₀ →L[ℝ] H₀` |

**23 条 `#print axioms` 全部只有 `propext, Classical.choice, Quot.sound`，0 条 `sorryAx`。**
`lake build` 3519 jobs 通过；回执 `20260919T084529.261763Z`，10/10 门、246 模块重放。

## 二、交接：`S5`（边界情形，中等置信）

**目标**：`L` 有界、非负、自伴 ⟹ `‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖`（`t ≥ 0`）。

**推荐证法（导数单调性）**：令 `φ(t) = ‖exp(-t • L) f‖²`，则
`φ'(t) = -2⟪L exp(-t•L) f, exp(-t•L) f⟫ ≤ 0`，故 `φ` 在 `[0,∞)` 上递减，`φ(t) ≤ φ(0) = ‖f‖²`。

* **已确认存在**：`hasDerivAt_exp_smul_const`（`Mathlib/Analysis/SpecialFunctions/Exponential.lean`）、
  `NormedSpace.exp_add_of_commute`、`AntitoneOn` 由导数非正的判据。
* **已确认不存在**：`IsSelfAdjoint.spectralRadius_eq_nnnorm`。**不要走谱半径那条路**——
  本会话查过，这个名字在 pinned Mathlib 里没有，改走连续泛函演算需要额外考古。
* 主要摩擦：把内积的乘积法则与 `hasDerivAt_exp_smul_const` 接起来。

我对这一条的判断是**能做但不是「有把握」**，所以没有动手，留给接手方。

## 三、交接：`S6`–`S8`（低置信，`S6` 是真正的坎）

* **`S6`**（`exp(-t L_s)` 随 `s ↓ 0` 强收敛）：本路线从一开始就标为**高风险**，Mathlib 无先例。
  经典证法用 `‖exp(-tL_s)f - exp(-tL_r)f‖ ≤ t‖L_s f - L_r f‖`（两个交换的压缩半群之差），
  再证 `L_s f → T*T f` 于 `D(T*T)` 上、并用稠性与一致有界性推广。
  **注意**：这一步真正需要 `Dense (T.domain)` 与伴随算子 `T*`——而 `S1`–`S4` 都不需要，
  所以接手方要先补 `T*T` 的自伴性与 `D(T*T)` 的稠性（Mathlib 有 `LinearPMap.adjoint`，
  但没有 von Neumann 的 `T*T` 自伴性定理，可能要自己证）。
* **`S7`**、**`S8`**：依赖 `S6`，在其之后是套路。

**现成可用的起点**：`resolventCLM T hT hs` 已经是打包好的 `J_s`，
Yosida 近似直接写成 `L_s := s⁻¹ • (ContinuousLinearMap.id ℝ H₀ - resolventCLM T hT hs)`。

**2026-09-19 晚追加：`S6` 的两项前置已证。** von Neumann 定理（`T†T` 自伴、`D(T†T)` 稠密、`(1 + sT†T)J_s = 1`、`f − J_s f = s·J_s(T†T f)`）在 `Analysis/Semigroup/VonNeumann.lean`，预解极限（`J_s → 1` 强收敛、`J_s J_r = J_r J_s`）在 `Analysis/Semigroup/ResolventLimit.lean`，`T†T` 的定义在 `AdjointComp.lean`；见 [von Neumann 路线记录](2026-09-19-von-neumann-route.md)。`S6` 语句里的交换性假设由 `R3` 直接消掉。`S6` 本身仍未证。

**2026-09-19 夜追加：`S6` 已证。** `exp(-t L_s) f` 随 `s ↓ 0` 强收敛（`Analysis/Semigroup/YosidaLimit.lean`），核心是 `‖e^{-tA}f − e^{-tB}f‖ ≤ t‖Af − Bf‖`（`SemigroupLimit.lean`）。**注意**：本清单与路线文件里 `S6` 的抽象写法（只假设非负与交换）被证明为假（`YosidaFamily.lean` 的 `Y0`），修正版多一个稠密集上 Cauchy 的假设；见 [Yosida 极限路线记录](2026-09-19-yosida-limit-route.md)。`S7`、`S8` 仍开放。

**2026-09-19 深夜追加：`S7`、`S8` 已证，路线 `S1`–`S8` 完成。** `P_t = semigroupApply`（`Generated.lean`），半群律、压缩、对称、强连续在 `SemigroupLaws.lean`，生成元 `−T†T` 在 `Generator.lean`（经 `ExpMeanValue.lean` 的中值界，不用 Bochner 积分）；见 [生成半群路线记录](2026-09-19-generated-semigroup-route.md)。第三节交接的 `S6`–`S8` 至此全部关闭。缺口二/三/四（下一节）原封未动。

**2026-09-19 追加：`T` 已具体化。** `KLS/LogConcave/HeatSemigroup.lean` 把抽象半群套到加权梯度的闭包上：`heatSemigroup hν m B hi ht` 是 `L²(ν)` 上的 `P_t`，全部半群律、生成元、以及 `⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`（Dirichlet 形式 = 闭能量）都已转移；`intrinsicHeatSemigroup` 覆盖任意对数凹律。缺口一至此关闭。缺口二的交接提示词：[markov-handoff-prompt](2026-09-19-markov-handoff-prompt.md)。

## 四、交接：缺口二/三/四（纲领级）

见[基础设施评估](2026-09-19-buser-infrastructure-assessment.md)。其中**缺口三的正则化**是本会话
唯一明确表示**无法预估代价**的一段：一般对数凹测度的位势 `V` 不光滑、支撑可能有边界或降维，
Bochner 公式用不上，必须走「光滑严格对数凹逼近 + Neumann 边条件 + 极限过渡」。
这是整个 Buser 纲领里真正的数学内容所在。

## 五、一个可以大幅降本的决定（尚未采纳）

Blueprint 里该比较节点的**唯一**下游消费者是 `cor:tight-window-consumption`，
它要的是「无量纲边界下界」，**不需要常数 π**。把目标从 `Ψ² ≤ π C_P` 放松为
`Ψ² ≤ C·C_P`（`C` 显式、不必最优）是正当的，且便宜得多——π 要走 Bakry–Émery 的精细形式。
阶段一在一维拿的已经是 12 而不是 π，是同一个取舍。**此决定属 owner，尚未写入 `tasks.json`。**

**2026-09-19 晚，owner 决定：不采纳。** 目标保持 `Ψ² ≤ π·C_P`，常数 π 不放松。因此 Buser 半的 `n ≥ 2` 路线只能走半群 / Bakry–Émery（De Ponti–Mondino 的锐形式），局部化路线给不出 π，不再作为替代方案考虑；一维已证的常数 12 仍只是阶段性结果，不是该节点的证明。下一块 Lean 工作相应地是 `S6` 的前置：von Neumann 定理（`T*T` 自伴、`D(T*T)` 稠密）。
