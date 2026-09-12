# 闭条件纤维形式 `lem:conditional-fiber-form`：核对、statement、语义对齐与证明

日期：2026-09-11（Asia/Shanghai）。基线：本地 `main` 提交 `5e5c704`，工作树含 2026-09-10 尚未提交的四个节点
（Dirichlet 见证、一维 `12·Var`、法向障碍、raw/core 一致性）及未跟踪的 `research/weekly/`；本地分支领先
`origin/main` 两个提交、落后三个文档提交，分叉与提交由用户处理。Lean/Mathlib 为 v4.33.0，Mathlib 提交
`db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示：一维常数从 12 改到 4 的线暂停，先做与之无关的节点，
按顺序核对 `lem:conditional-fiber-form`、`prop:weighted-spectator-obstruction`、`lem:relative-perimeter-smoothing`；
不 commit、不 push。开始前 `git status --short` 与用户描述一致，没有其他会话的改动。

## 核对与节点选择

`lem:conditional-fiber-form`（Blueprint 第 50 章"Conditional-fiber frame route"）在 tasks.json 为
`local_argument / unchecked`，atlas `ready` 列为 `inspect_infrastructure`；路线 sidecar 的 claim 为上游
`proved / checked_by: agent`。核对结论：基础设施 **available**，无 Mathlib 缺口。

- 库内：`KLS/ConditionalFiber.lean` 的六条契约与 `kernel := (jointLaw μ ρ).condKernel`、
  `compProd_baseLaw_kernel`（`Measure.disintegrate`）、`ae_restrict_congr`（把 μ-a.e. 性质推到 a.e. 纤维的模板）、
  `measurable_energyAt`；`Energy.ClosedQuadratic`/`Markovian`/`Dirichlet`；`WeightedGradient.dense_smoothCore`
  （任意有限维 Borel 概率律的 C_c^∞ 类稠密）与 `lipschitzWith_of_contDiff_hasCompactSupport`。
- Mathlib：`Measure.ae_ae_of_ae_compProd`、`lintegral_liminf_le`（Fatou）、`tendstoInMeasure_of_tendsto_eLpNorm`
  与 `TendstoInMeasure.exists_seq_tendsto_ae`（L² 收敛取 a.e. 子列）、`measurableSet_tendsto`、
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm'`、`lowerSemicontinuous_iff_frequently`、`evariance_mul`、
  `lintegral_prod`/`lintegral_prod_swap`/`Measure.prod_swap`、`ENNReal.le_liminf_mul`、
  `ENNReal.mul_div_mul_left`、`ContDiff.lipschitzWith_of_hasCompactSupport`。
- 需新写的唯一工具：两点方差恒等式 `2·eVar[X] = ∬‖X t − X s‖ₑ² d(ν⊗ν)`。Mathlib 只有带协方差项的
  `variance_sub`；扩展实数版本（X ∉ L² 时两边同为 ⊤）是闭性、Markov、平行四边形与 Lipschitz 界四处的共同工具。

因此 `unchecked → available` 并同轮证明。

## Statement 设计

新模块（均在 `formalization/FunctionalInequalities/`）：

| 模块 | 声明 | 内容 |
| --- | --- | --- |
| `Probability/TwoPointVariance.lean` | `Probability.integral_sub_sq_prod ν hX` | X ∈ L²：`∫(X t − X s)² d(ν⊗ν) = 2 Var X` |
| | `Probability.two_mul_evariance_eq_lintegral_prod ν hX` | a.e. 强可测 X：`2·eVar[X] = ∫⁻‖X p.1 − X p.2‖ₑ² d(ν⊗ν)`，X ∉ L² 时两边为 ⊤ |
| `KLS/ConditionalFiber/Closed.lean` | `twoPointMeasure κ b := (κ b).prod (κ b)`（abbrev）、`twoPointMeasure_swap`、`lintegral_twoPointMeasure_swap` | 纤维两点测度及其交换不变性（可逆性） |
| | `jump κ b f` | `∫⁻‖f(rec b p.1) − f(rec b p.2)‖ₑ² d(twoPointMeasure κ b)` |
| | `two_mul_evariance_eq_jump`、`two_mul_evariance_id`、`energyAt_of_not_nondegenerate`、`energyAt_eq_jump_div` | 非退化纤维上 `energyAt κ b f = jump κ b f / (2·eVar[id])`；退化纤维为 0 |
| | `jump_le_of_lipschitzWith`、`energyAt_le_of_lipschitzWith`、`energy_le_of_lipschitzWith`、`energy_ne_top_of_lipschitzWith` | 全局 L-Lipschitz 测试：纤维能量 ≤ L²，总能量 ≤ d·L² |
| | `energyAt_zero`、`energyAt_mul`、`energyAt_add_sub`、`energyAt_comp_le`、`energyAt_le_liminf` | 纤维层的零、二次齐性、平行四边形、收缩不增、Fatou |
| | `functional μ ρ := ⟨form μ ρ⟩`、`functional_apply`、`domain_functional`、`form_eq_energy_of_ae_eq` | 形式作为 `Energy.Functional`；定义域即 `domain μ ρ` |
| | `smoothCore_subset_domain`、`dense_domain` | C_c^∞ 类在有限定义域内；定义域稠密 |
| | `form_zero`、`form_smul`、`form_parallelogram`、`form_compL2_le`、`markovian` | 形式层的二次恒等式与 Markov 性 |
| | `energy_le_liminf`、`lowerSemicontinuous_form` | a.e. 收敛序列的 Fatou；L² 上下半连续 |
| | `closedQuadratic`、`dirichlet` | `Energy.ClosedQuadratic (functional μ ρ)`、`Energy.Dirichlet μ (functional μ ρ)` |

`KLS/ConditionalFiber.lean` 只把 `measurable_coordinates`、`measurable_reconstruct` 由 `private` 改为公开，
并新增 `measurable_reconstruct_left`；定义与六条契约未改。

证书 `Solutions.LemConditionalFiberForm.certificate μ ρ`：(1) `Energy.Dirichlet μ (functional μ ρ)`；
(2) 每个 Markov 核、基点与 Borel 测试在非退化纤维上的跳跃表示；(3) 每个纤维两点测度的交换不变性；
(4) 全局 Lipschitz 测试的 `d·L²` 界。五个 `example`：Blueprint 范围（对数凹、二阶矩、可容许框架——定理均未用）、
`Fin (n+1)` 上的稠密定义域与下半连续、Markov 不等式、C_c^∞ 核在定义域内、`Fin 0` 上球面概率律不存在。

**主张什么。** 上表全部声明与证书，对任意有限维实内积空间上的 Borel 概率律 μ 与球面上任意概率律 ρ。
**不主张什么。** 不主张与梯度能量的比较（`lem:conditional-fiber-energy-comparison`）、任何纤维 Poincaré 输入、
框架界、Poincaré 不等式或 KLS；不主张双线性极化形式的显式构造（`ClosedQuadratic` 已含二次结构，极化对称性由此自动）；
不主张 Lipschitz 松弛或任何其他能量与本形式相等。**有限范围与零维。** 空间有限维（`dense_smoothCore` 需要）；
零维时 `Direction E` 为空、ρ 不存在，命题空成立，与 Blueprint "d ≥ 1" 一致，证书以 `IsEmpty` 例子记录。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| `d ≥ 1`，全维对数凹、有密度、二阶矩有限的概率律 | 任意 `μ : ProbabilityMeasure E`，任意 `ρ`；Blueprint 范围为证书中的类型应用 | Lean 更强（去掉全部假设） |
| 形式 `D_{μ,ρ}` | `functional μ ρ`，值为 `form μ ρ`（`def:conditional-fiber-form` 的 `form`） | 一致 |
| 稠密定义 | `dense_domain : Dense (functional μ ρ).domain`，定义域即 `domain μ ρ` | 一致 |
| 闭 | `lowerSemicontinuous_form`，并合成 `ClosedQuadratic`（含 `zero`、`smul`、平行四边形） | 一致（Lean 另给二次恒等式） |
| 对称 | 跳跃表示 `energyAt_eq_jump_div`：被积函数在 (t,s) 中对称，且二次形式的极化自动对称 | 一致（按 Blueprint 证明原文"symmetric jump form"读取） |
| Markov | `markovian : Energy.Markovian μ (functional μ ρ)`（全部正规收缩，作用于 L² 类） | 一致 |
| 可逆 | `twoPointMeasure_swap : map swap (κ b ⊗ κ b) = κ b ⊗ κ b` 与 `lintegral_twoPointMeasure_swap` | 一致（Blueprint 证明原文"Symmetry of the two-point measure gives reversibility"） |
| 证明：`(2σ²)⁻¹∬(f(t)−f(s))²` | `two_mul_evariance_eq_jump`、`energyAt_eq_jump_div` | 一致 |
| 证明：a.e. 子列、分解、Fatou | `exists_seq_tendsto_ae`、`ae_ae_of_ae_compProd`、两层 `lintegral_liminf_le` | 一致 |
| 证明：Lipschitz 收缩减小平方差 | `energyAt_comp_le` 逐点 `edist_le_mul` | 一致 |
| 证明：L-Lipschitz ⇒ `D ≤ d L²`，C_c^∞ 在定义域且稠密 | `energy_le_of_lipschitzWith`、`smoothCore_subset_domain`、`dense_smoothCore` | 一致（Lean 不需要二阶矩：C_c^∞ 有界故在 L²） |

未发现 Lean 弱于 Blueprint 之处。`\uses{def:conditional-fiber-form}` 在 Lean 中实际使用。Blueprint 引理块尾补充了
Lean 读法（`functional`、`Energy.Dirichlet`、对称/可逆的两点表示、任意律范围、零维空成立），证明块追加本地路线；
第 50 章开头"本章唯一 leanok 是定义"改为定义与本引理；"Pinned provenance"段记录上游 agent 评审之外新增的 Lean 证据；
第 00 章条件纤维一句加注"structural form lemma is Lean-certified"。

## 证明路线

1. **两点恒等式。** X ∈ L²：令 Y = X − E X，`(X t − X s)² = Y t² + Y s² − 2 Y t Y s`，`Integrable.comp_fst_iff`/
   `comp_snd_iff`/`mul_prod` 给可积性，`integral_prod_mul` 与 `∫Y = 0` 消去交叉项，`integral_prod` 加常数积分得
   `2∫Y² = 2 Var`；再 `ofReal_integral_eq_lintegral_ofReal` 与 `enorm_pow`/`Real.enorm_of_nonneg` 转成 `‖·‖ₑ²`。
   X ∉ L²：`evariance_eq_top` 给左边 ⊤；若右边有限，Tonelli 后 `ae_lt_top'` 取一点 x₀ 使 `t ↦ X x₀ − X t ∈ L²`，
   与常数相减得 X ∈ L²，矛盾。
2. **跳跃表示。** `energyAt` 展开为 `if Nondegenerate then eVar/σ² else 0`；非退化时用恒等式与
   `ENNReal.mul_div_mul_left` 把 `eVar/σ²` 写成 `jump/(2σ²)`。
3. **Lipschitz 界。** `rec b t − rec b s = (t − s)•θ`，`‖θ‖ = 1`，故被积函数 ≤ L²‖t − s‖ₑ²，积分得
   `jump ≤ L²·(2σ²)`，`ENNReal.div_le_iff` 得 `energyAt ≤ L²`；基律为概率律，`energy ≤ d·L²`。
4. **二次恒等式。** 齐性用 `evariance_mul`（含 c = 0，ENNReal 中 `0·⊤ = 0`）；平行四边形在跳跃层逐点用实数
   `(a+b)² + (a−b)² = 2a² + 2b²` 经 `ofReal` 转换，`lintegral_add_left`/`lintegral_const_mul` 装配，再 `ENNReal.add_div`、
   `mul_div_assoc`。形式层用 `Lp.coeFn_add/sub/smul` 与 `energy_congr_ae` 换代表元。
5. **Markov。** `φ.coeFn_compL2` 换代表元；跳跃层逐点 `φ.lipschitz.edist_le_mul`，`ENNReal.div_le_div_right`。
6. **闭性。** `lowerSemicontinuous_iff_frequently` + `exists_seq_forall_of_frequently` 取序列 f_n → f 且
   `form f_n ≤ y`；`tendsto_Lp_iff_tendsto_eLpNorm'` → `tendstoInMeasure_of_tendsto_eLpNorm` →
   `exists_seq_tendsto_ae` 取 a.e. 收敛子列。`energy_le_liminf`：收敛写成 `f_n − f → 0`，`measurableSet_tendsto`
   给可测性，`ae_map_iff` 经 `coordinates` 推到联合律，`compProd_baseLaw_kernel` + `ae_ae_of_ae_compProd` 推到
   a.e. 纤维；纤维上 `quasiMeasurePreserving_fst/snd.tendsto_ae` 推到两点空间，`Tendsto.liminf_eq` +
   `lintegral_liminf_le` 得 `jump f ≤ liminf jump f_n`，`ENNReal.le_liminf_mul` 处理除以常数；基律再一次
   `lintegral_mono_ae` + `lintegral_liminf_le` + `le_liminf_mul`。最后 `liminf_le_of_le` 得 `form f ≤ y`。
7. **装配。** `closedQuadratic` 五字段、`dirichlet := ⟨closedQuadratic, markovian⟩`。

坑：`omit` 不能去掉被 `Kernel (Direction E × E) ℝ` 引用的 `[MeasurableSpace E]`，只能省略 `BorelSpace`/
`SecondCountableTopology`/`InnerProductSpace`；`Measurable.add`/`Measurable.mul` 给出的是 `f + g`、`(fun _ ↦ c) * f`
的 Pi 形式，作为 `rw` 引理参数时要用 `(f := fun x ↦ f x + g x)` 命名参数固定为 λ 形式；`unfold jump` 后出现
未 β 归约的 `(fun x ↦ …) (reconstruct b p.1)`，先 `beta_reduce` 再 `rw`；`zero_le` 在 ENNReal 上参数隐式，
写 `exact zero_le`；`mul_le_mul_left'` 已不存在，用 `mul_le_mul' le_rfl`；`ofReal_norm_eq_enorm` 已弃用改
`ofReal_norm`；`Lp.coeFn_zero` 的 `E p μ` 是显式参数；`probReal_univ` 是概率律 `μ.real univ = 1` 的名字。

## 元数据同步

- ledger 新增 `lem:conditional-fiber-form`（proved / lean，`kind: lemma` 按仓库遗留规则），二十一个 proved 节点；
  `check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块；根聚合 `FunctionalInequalities.lean`
  导入 `KLS.ConditionalFiber.Closed`（传递导入 `Probability.TwoPointVariance`）。
- Blueprint 引理块锚定十五条声明与证书，声明与证明标 `leanok`；route-composition.yaml 的 claim 保持 `proved`，
  在上游 `agent_review` 之外新增 `kind: lean` 证据（`check_blueprint` 要求 Lean 证据来源为本地 `kls-lean`，
  ledger 节点 proved/lean，且 `\lean{}` 含该声明）。`research/tests/test_check_blueprint.py` 的合成夹具为该节点
  补上 Lean 证据（夹具对 `CERTIFICATES` 中的标签自动生成 `\leanok` 块，仅评审证据会被检查器拒绝），103 项测试通过。
- tasks.json：节点改为 `available`，登记两个新模块、证书、`ConditionalFiber.lean`、`Energy/Dirichlet.lean`、
  `Energy/ClosedQuadratic.lean`、`WeightedGradient/Core.lean` 与所用 Mathlib 文件哈希；`def:conditional-fiber-form`
  的 `ConditionalFiber.lean` 证据哈希同步刷新。
- 当前指南：HANDOFF（新节、二十一计数、证书表、条件纤维路线状态与下一阶段文字、边界段）、README、
  `verification.md`、`solutions/README.md`、`formalization/README.md`（Probability 行、KLS 行、基础段）、
  `KLS/README.md`（两行）、`blueprint/README.md`、`naming.md`（两行）、根模块文档要点。statement golden、
  `STATEMENT_CHECKS`、`FoundationAxiomAudit` 未动。

## 证据边界

默认 `lake build` 通过；证书与十一条库级声明有标准公理守卫。最终验证收据由 `python3 research/verify.py` 在本记录
及所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；
未做隔离重建、远端 CI、commit 或 push。下游 `lem:conditional-fiber-energy-comparison`、
`cor:conditional-fiber-twelve-bound` 与 `q:conditional-fiber-frame` 未获得新证明。
