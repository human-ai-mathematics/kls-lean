# 局部密度假设下的 raw/sequential-core 一致性：statement、语义对齐与证明

日期：2026-09-10（Asia/Shanghai）。基线：本地 `main` 提交 `5e5c704`，工作树含同日尚未提交的 Dirichlet 见证、
一维 `12·Var`、法向障碍工作。用户决定继续追一维系数 4（等待合作者提供 KLS 1995 原文），期间先做与该线无关的节点；
本节点是 HANDOFF 长期列为"尚未提供"的 raw/core 一致性，与一维常数无关。用户指示不 commit、不 push。

## 核对与节点选择

`thm:smooth-gradient-raw-core-agreement-density`（Blueprint 第 30 章）在 tasks.json 为 `local_argument / unchecked`，
atlas `ready` 列为 `inspect_infrastructure`。核对后发现基础设施基本齐备：`Energy/WeightedGradient/Closable.lean`
的可闭性、`Relaxation/LinearPMap.lean` 的"可闭算子的松弛等于闭包范数平方"、`LipschitzApproximation.
exists_compactSupport_weighted_L2` 的截断逼近、`Relaxation/LowerSemicontinuous.lean` 的恢复序列比较。
唯一缺口：可闭性定理以"支撑内部"为开集，而 Blueprint 允许任意开集 Ω（Ω 可小于支撑内部，例如去掉一个
密度趋零的点），且局部支配只在 Ω 的紧子集上成立。故把 `LocallyDominates` 推广为
`LocallyDominatesOn ν m Ω`，把可闭性推广为 `operator_isClosable_of_isOpen`。不需要新的 Mathlib 接口，
`unchecked → available` 并同轮证明。

## Statement 设计

新模块 [Energy/SmoothGradient/Core.lean](../../formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean)，
命名空间 `FunctionalInequalities.Energy.SmoothGradient`；对 [Probability/LocalDomination.lean](../../formalization/FunctionalInequalities/Probability/LocalDomination.lean)
与 [Energy/WeightedGradient/Closable.lean](../../formalization/FunctionalInequalities/Energy/WeightedGradient/Closable.lean) 的推广见下。

| 声明 | 内容 |
| --- | --- |
| `Probability.LocallyDominatesOn ν m Ω` | Ω 的每个紧子集上 `m ≤ C·ν`；`LocallyDominates ν m` 改为 `Ω = interior support` 的缩写（`abbrev`），引理移入 `LocallyDominatesOn` 命名空间并推广 |
| `WeightedGradient.operator_isClosable_of_isOpen hac hfr hΩ hΩν hloc` | 开集 Ω 承载 ν 且 m 在 Ω 的紧子集上被 ν 支配时加权梯度算子可闭；原 `operator_isClosable` 成为推论 |
| `structure LocalDensity ν m` | Blueprint 的密度假设：`Ω` 开、`ν Ωᶜ = 0`、`ν.restrict Ω = (m.restrict Ω).withDensity (ofReal ρ)`、`ρ` 可测、`ρ > 0` m-a.e. 于 Ω、`ρ⁻¹` 在 Ω 的紧子集上本质有界 |
| `LocalDensity.measure_eq`、`absolutelyContinuous`、`subset_support`、`subset_interior_support`、`frontier_support_null`、`locallyDominatesOn` | 由密度假设推出 `ν ≪ m`、`Ω ⊆ interior support`、支撑边界零测、局部支配 |
| `lipschitzOperator ν m D`、`lipschitzOperator_isClosable` | 单位权 Lipschitz 梯度算子及其可闭性 |
| `Test.memLp_gradient`、`Test.exists_domain_sequence_tendsto`、`Test.toL2_mem_closure_domain` | 光滑测试的梯度平方可积；截断序列在图范数中收敛；光滑测试属于闭包定义域且闭包值为其梯度 |
| `Test.coe_energy_eq_norm_toLp_sq`、`Test.energy_eq_nnnorm_sq` | 原始能量等于梯度 L² 类的范数平方 |
| `lipschitzRelaxation_le_relaxation` | 恢复序列：Lipschitz 松弛 ≤ 光滑松弛 |
| `preEnergy_agreesOnTests`、`preEnergy_isSequentialCoreFor` | `(preEnergy ν).AgreesOnTests (relaxation ν)`、`IsSequentialCoreFor` |
| `Intrinsic.preEnergy_agreesOnTests`、`Intrinsic.preEnergy_isSequentialCoreFor` | 内禀律 `intrinsicMeasure μ` 的实例 |

证书 `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate ν m D`：两条结论的合取。三个 `example`：
内禀律实例、欧氏族上"光滑测试类的松弛能量等于原始能量"、同一 L² 类的两个光滑测试能量相等。

**主张什么。** 上表全部声明与证书，对任意有限维实内积空间上带局部密度的概率律。**不主张什么。** 无密度假设时
不作任何断言（`obs:dirac-raw-energy`、`obs:normal-direction-raw-energy` 说明不可能）；不主张与 Cheeger 能量或
graph-norm core 的等价；不主张 Poincaré 不等式；不主张 Lipschitz 松弛等于光滑松弛（只证 ≤ 一侧，另一侧未用到）。
**有限范围与零维。** 空间有限维；零维空间上 Haar 测度与概率律的密度表示需 `m = ν`，结构可实例化时定理照常成立，
但证书未单列零维例子。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| 仿射支撑 `A = a + V`，ν 为内禀律 | 一般 `ν : ProbabilityMeasure V`，V 有限维内积空间；内禀律为 `Intrinsic.*` 实例 | Lean 更强（任意律），内禀实例保留 |
| 开集 Ω ⊆ V，`ν(V ∖ Ω) = 0` | `LocalDensity.Ω`、`isOpen`、`compl_null` | 一致 |
| Borel `ρ : V → [0,∞)`，`ν(B) = ∫_B ρ dLeb` 对 Borel `B ⊆ Ω` | `ρ : V → ℝ` 可测，`restrict_eq`（`ENNReal.ofReal ρ` 密度）；Lebesgue 测度换成任意 Haar 测度 `m` | 一致（`ofReal` 截去负值，正性 a.e. 使之无差别；Haar 一般化是 Lean 更强） |
| `ρ > 0` a.e. 于 Ω | `pos : ∀ᵐ x ∂m, x ∈ Ω → 0 < ρ x` | 一致 |
| `ρ, ρ⁻¹ ∈ L^∞_loc(Ω)` | 只假设 `inv_locallyBounded`（`ρ⁻¹` 在紧子集上本质有界）；`ρ ∈ L^∞_loc` 未假设 | Lean 更强（少一条假设），已在 Blueprint 块与文档说明 |
| "explicit positivity premise is retained: real inversion sends zero to zero" | `pos` 与 `inv_locallyBounded` 分开 | 一致 |
| `P_ν.AgreesOnTests(E_ν)` | `preEnergy_agreesOnTests` | 一致 |
| `IsSequentialCoreFor`，`SequentiallyGenerates` 定义性 | `preEnergy_isSequentialCoreFor := ⟨_, rfl⟩` | 一致 |

未发现 Lean 弱于 Blueprint 之处。`\uses` 未改。Blueprint 原无证明块，本次补充 `\begin{proof}\leanok …\end{proof}`
记录本地路线，并在定理块尾说明 Lean 的假设结构与"任意律"范围。

## 证明路线

1. **假设推导。** `measure_eq`：`ν s = ∫⁻_s ofReal ρ dm`（`s ⊆ Ω` 可测），由 `restrict_eq` 与
   `withDensity_apply`、`restrict_restrict`。`absolutelyContinuous`：`ν s = ν (s ∩ Ω) + ν (s ∖ Ω)`，前者是
   m-零集上的积分，后者 ≤ `ν Ωᶜ = 0`。`subset_support`：Ω 中点的每个邻域含开集 `W ⊆ Ω` 非空，
   `ν W = ∫⁻_W ofReal ρ > 0`（`setLIntegral_pos_iff` 加 Haar 的 `IsOpen.measure_pos` 与 a.e. 正性）。
   `frontier_support_null`：`frontier support ⊆ (interior support)ᶜ ⊆ Ωᶜ`。`locallyDominatesOn`：紧 `K ⊆ Ω` 上
   `ρ⁻¹ ≤ C'`（`C' = max C 1 > 0`）与正性给 `1 ≤ C' ρ` a.e.，故 `m (s ∩ K) ≤ C' ν (s ∩ K)`。
2. **可闭性推广。** `Closable.lean` 的辅助引理把 `K ⊆ interior support` 换成 `K ⊆ Ω`，`operator_isClosable_of_isOpen`
   的证明体只改两处：`Ω` 由参数给出（`IsOpen Ω`），最后一步用 `ν Ωᶜ = 0` 得 a.e. `x ∈ Ω`。原定理作为 `Ω = interior
   support` 的推论保留，唯一外部使用者 `KLS.LogConcave.locallyDominates` 因 `abbrev` 无需修改。
3. **截断。** `exists_compactSupport_weighted_L2`（B = id）给出全局 Lipschitz 紧支撑的 `g_j`，它们是
   `WeightedGradient.IsTest`，其类在算子定义域内，`(g_j, ∇g_j) → (f, ∇f)` 于 `L²(ν) × L²(ν;V)`
   （`Lp.edist_toLp_toLp` 加 `ENNReal.tendsto_toReal`）。
4. **闭包。** `mem_graph_topologicalClosure_iff` 加 `IsClosable.graph_closure_eq_closure_graph` 与 `LinearPMap.mem_graph_iff`
   给 `f ∈ dom T̄`、`T̄ f = ∇f`。
5. **松弛比较。** `sequentialRelaxation_le_of_recovery_sequences (preEnergy ν) (ofLinearPMap T)`：截断序列的能量
   `‖T g_j‖²` 收敛到 `‖∇f‖² = energy f`（`Tendsto.liminf_eq`），故 Lipschitz 松弛 ≤ 光滑松弛。
6. **装配。** `energy f = ‖T̄ f‖² = relax_Lip f ≤ relax_smooth f ≤ energy f`。

坑：`WeightedGradient/Core.lean` 不导入 `Closable.lean`，需显式导入；`theorem` 的 section 变量按 statement 包含，
`D` 未出现在结论中的定理需 `include D in`；`(preEnergy ν).Test` 与 `Test ν` 在 `rw` 的 implicit 透明度下不相等，
用 `exact` 传递 `Test.energy_eq_nnnorm_sq`；`Lp.edist_toLp_toLp` 需先 `rw [Test.toL2]` 展开；
`LinearPMap.mem_graph_iff` 的分量以 `(pair).1` 形式出现，先 `have` 重述再用 `▸`；`measure_inter_add_diff` 已弃用，
改 `measure_inter_add_sdiff`；`ContDiff.inner` 的首个显式参数是域 `ℝ`。

## 元数据同步

- ledger 新增 `thm:smooth-gradient-raw-core-agreement-density`（proved / lean，`kind: lemma` 按仓库遗留规则），
  二十个 proved 节点；`check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块；
  `Poincare/Foundation.lean` 导入 `Energy.SmoothGradient.Core`（与同日的 `NormalDirection`）。
- Blueprint 定理块锚定十五条声明与证书，声明与证明标 `leanok`；route-composition.yaml 无该节点 claim，未改。
- tasks.json：节点改为 `available`，登记新模块与库内、Mathlib 依赖哈希；`Closable.lean`、`LocalDomination.lean`
  改动后 `lem:covariance-core-closure` 的两条证据哈希同步刷新。
- 当前指南：HANDOFF（新节、二十计数、证书表、边界文字）、README、`verification.md`、`solutions/README.md`、
  `formalization/README.md`、`Energy/README.md`、`Poincare/README.md`、`blueprint/README.md`、`naming.md`
  （`LocallyDominatesOn`、`LocalDensity`、法向坐标三行）、`Foundation` 文档要点。statement golden、
  `STATEMENT_CHECKS`、路线配置未动。

## 证据边界

默认 `lake build` 通过；证书与十一条库级声明有标准公理守卫。最终验证收据由 `python3 research/verify.py` 在本记录
及所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；
未做隔离重建、远端 CI、commit 或 push。
