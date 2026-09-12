# 一维对数凹 Poincaré 界 `C_P^lit(ν) ≤ 12·Var_ν`：statement、语义对齐与证明

日期：2026-09-10（Asia/Shanghai）。基线：本地 `main` 提交 `5e5c704`，工作树含同日尚未提交的
Dirichlet 见证工作（`thm:smooth-gradient-relaxation-dirichlet`）及未跟踪的 `research/weekly/`；
本地分支领先 `origin/main` 两个提交、落后三个文档提交。用户指示不 commit、不 push。
Lean/Mathlib 为 v4.33.0，Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。
用户在 Dirichlet 见证完成后批准"接着做一维 12·Var"。

## 核对与节点选择

开始前默认 `lake build` 通过；Dirichlet 见证的收据 `build/verification/20260910T092922.606486Z` 通过。
`thm:one-dimensional-logconcave-poincare` 在 Blueprint 中标为"verified published input, not a local
Lean proof"，路线 sidecar 的 claim 为 `imported`（Bobkov 1999 Corollary 4.3 与 (1.3)）；tasks.json 为
`mathematics: published`、优先级 5、基础设施 `unchecked`。它是条件纤维分支
`cor:conditional-fiber-twelve-bound` 的唯一数值输入。库内已有 Borell 密度表示
（`IsBorellDensity`：可测、非负、上半连续、对数凹、`withDensity` 表示；支撑内部连续正）、
`LogConcave.absolutelyContinuous_of_interior_support_nonempty`、`LogConcave.convex_support`、
环境二阶矩 `LogConcave.memLp_id_two`/`integrable_id`、光滑测试与文献常数相等
`LogConcave.smoothTest_constant_eq_localSlope`、以及 `Poincare.SmoothTest.Admissible.variance_le_integral_sq_sub`。
Mathlib 已有分部积分 `intervalIntegral.integral_mul_deriv_eq_deriv_mul`、反常积分
`integral_Ioi_of_hasDerivAt_of_tendsto`、`Directed.measure_iUnion`、`ofReal_variance`、`variance_dirac`。
不需要新的 Mathlib 接口，故 `unchecked → available` 并同轮证明。

## Statement 设计

Blueprint：每个"线上"的对数凹概率律 ν 满足 `C_P^lit(ν) ≤ 12 Var_ν(T)`，含零方差情形。

新增模块（均在 `formalization/FunctionalInequalities/`）：

| 模块 | 内容 |
| --- | --- |
| `Probability/Line/Cdf.lean` | `Probability.Line.cdf μ x := μ.real (Iic x)`；单调、有界、极限；有 Lebesgue 密度时的增量积分、连续性、导数 `hasDerivAt_cdf`、中位数存在 `exists_cdf_eq_half`、单点零测、均匀推前 `map_cdf_eq_uniform : μ.map (cdf μ) = volume.restrict (Icc 0 1)`、`∫ cdf = 1/2`、`∫ (cdf − 1/2)² = 1/12`、`∫ (cdf − 1/2)³ = 0`、`integrable_comp_cdf` |
| `Probability/Line/ExpIntegral.lean` | `C·exp(κ(s − x₀))` 的区间积分与衰减方向的半直线积分及可积性 |
| `KLS/LogConcave/Line/Density.lean` | `structure KLS.LineDensity μ`（`ρ`、`isBorell`）；`LogConcave.exists_lineDensity`、`convex_interior_support`、`measure_compl_interior_support`、`mem_interior_support_of_cdf`；`LineDensity.pos`、`concaveOn_log`、`ae_eq_zero_of_not_mem_interior_support`、`logSlope`、弦下界 `mul_exp_le_of_mem_Icc`、外推上界 `le_mul_exp_of_not_mem_Ioo`、支撑指数 `exists_supergradient` |
| `KLS/LogConcave/Line/Hazard.lean` | 四点不等式 `mul_le_mul_of_add_eq`；单调失效率 `mul_measureReal_Ioi_le`、`mul_cdf_le`；中位数界 `two_mul_measureReal_Ioi_le`（`2ρ(m)·μ(Ioi x) ≤ ρ x`，`m ≤ x`）、`two_mul_cdf_le`（`2ρ(m)·F x ≤ ρ x`，`x ≤ m`）；支撑线界 `le_add_mul_cdf_sub`（`ρ x ≤ ρ m + k(F x − 1/2)`） |
| `KLS/LogConcave/Line/Hardy.lean` | 区间 Hardy 步骤 `Probability.Line.integral_sq_mul_le_of_le_integral_abs`；`integral_sq_sub_mul_le_right/left`；半直线 `setIntegral_Ioi_sq_sub_le`、`setIntegral_Iic_sq_sub_le`；`LineDensity.smoothTest_holds : SmoothTest.Holds μ (1/ρ m)²` |
| `KLS/LogConcave/Line/Variance.lean` | `hasDerivAt_comparison`、`comparison_deriv_nonpos`、`quadratic_bound_le_sub`、`one_div_le_integral_mul`（`1/(12ρ(m)) ≤ ∫(x−m)(F−1/2)`）、`one_div_le_variance`（`1/(12ρ(m)²) ≤ Var`） |
| `KLS/LogConcave/Line/Poincare.lean` | `KLS.logConcave_dirac`；`LogConcave.smoothTest_holds_twelve_variance`、`direction_eq_bot_or_interior_support_nonempty`、`localSlope_constant_le_twelve_variance`、`localSlope_constant_le_twelve_evariance` |
| `Poincare/LocalSlope/Basic.lean`（追加） | `Intrinsic.constant_eq_zero_of_direction_subsingleton`、`constant_eq_zero_of_direction_eq_bot` |

证书 `Solutions.ThmOneDimensionalLogConcavePoincare.certificate ν hν`：
`Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (12 * variance id ν)` 与
`≤ 12 * evariance id ν`。三个 `example`：常数有限；原点 Dirac 律（对数凹、方差零、常数 `≤ 0`）；
支撑内部非空时的光滑测试不等式 `SmoothTest.Holds ν (12·Var)`。

**主张什么。** 上表全部声明与证书，对 ℝ 上任意紧集对数凹概率律。**不主张什么。** 不主张更小的普适常数
（历史上的 4）、任何高维结论、Cheeger 不等式、谱隙或生成元、原始测试能量上的结论；不主张 Hardy 常数
`1/ρ(m)²` 最优。**有限范围与零维。** 线取为 ℝ，坐标 T 为 `id`；零方差即仿射支撑为一点，方向空间零维，
常数为 0，由统一定理覆盖。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| 线上的对数凹概率律 ν | `ν : ProbabilityMeasure ℝ`，`KLS.LogConcave ν`（`def:log-concave-law` 的紧集定义） | 一致 |
| `C_P^lit(ν)` | `Poincare.LocalSlope.Intrinsic.constant ν`（`def:literature-poincare-constant`；先取内禀律） | 一致 |
| `Var_ν(T)` | `variance id ν`（Mathlib `ProbabilityTheory.variance`，对数凹律二阶矩有限，由 `memLp_id_two` 保证） | 一致 |
| 不等式 `≤ 12 Var` | `≤ ENNReal.ofReal (12 * variance id ν)`；另给 `≤ 12 * evariance id ν` | 一致（扩展实数中读取；扩展方差形式为补充） |
| 含零方差情形 | 方向空间 `= ⊥` 时常数为 0；Dirac 例子 `logConcave_dirac` 与 `variance_dirac` | 一致 |
| 证明："verified published input, not a local Lean proof" | 本地 Lean 证明，路线与 Bobkov 的 Cheeger 论证不同 | Lean 更强：节点从 `imported` 变为 `proved`，已记录 |
| 证明注记：常数 4 的历史出处 | 未触及 | 保留为历史出处 |

未发现 Lean 弱于 Blueprint 之处。`\uses{def:log-concave-law,def:literature-poincare-constant}` 在 Lean 中实际使用；
证明另外使用了 `thm:selected-literature-constant-equivalence`（光滑测试与文献常数相等），已在证明文字中
以 `\cref` 指出，但 `\uses` 未改（避免改变节点的依赖图；如需可在后续节点评审时补充）。
Blueprint 定理块尾补充了 Lean 中 ℝ、`id`、`ENNReal.ofReal` 的读取方式与零维说明；证明块保留 Bobkov
来源并追加本地路线摘要，删除"not a local Lean proof"。

## 证明路线

1. **零维/正维二分。** `(affineSupport ν).direction : Submodule ℝ ℝ` 是 ℝ 的理想，`Ideal.eq_bot_or_top`；
   `⊥` 时 `holds_zero_of_subsingleton` 给常数 0；`⊤` 时仿射支撑非空故 `affineSupport = ⊤`，
   `interior_support_nonempty_of_affineSupport_eq_top` 给支撑内部 Ω 非空。
2. **密度与支撑。** Ω 开凸（区间），`μ Ωᶜ = 0`（支撑凸 ⇒ 边界 Haar 零测 + 绝对连续）；Borell 密度 ρ 在 Ω 上
   连续正、`log ρ` 凹、Ω 外 a.e. 为零；F 连续，在 Ω 上 `F' = ρ`；中位数 m 存在且 `m ∈ Ω`。
3. **失效率与中位数界。** 凹性的四点不等式 `ρ a ρ e ≤ ρ b ρ c`（`a ≤ b ≤ c ≤ e`、`a + e = b + c`），沿平移
   `s ↦ s + (y − x)` 用 `MeasurePreserving.setIntegral_preimage_emb` 积分得 `ρ x·μ(Ioi y) ≤ ρ y·μ(Ioi x)`
   与镜像；取 x = m 得 `2ρ(m)(1 − F) ≤ ρ`（右）与 `2ρ(m)F ≤ ρ`（左），对所有 x 成立（Ω 外两侧同时为零）。
4. **Hardy。** 对光滑容许测试 f，`g = f − f(m)`。在 `[m, x] ⊂ Ω` 上对 `g²·(1 − F)'` 分部积分：
   `∫ g²ρ = −g(x)²(1−F(x)) + ∫ 2gg'(1−F) ≤ ∫ 2|g||g'|(1−F)`，再用 `2(1−F) ≤ ρ/c` 与
   `2|g||g'|/c ≤ g² + g'²/c²` 得 `∫_m^x g²ρ ≤ c⁻²∫_m^x g'²ρ`；左侧用 F 对称。半直线：把 `∫_S g² dμ` 写成
   `μ.withDensity (ofReal g²)` 的测度，`Ioi m ∩ Ω ⊆ ⋃_{q ∈ ℚ ∩ Ω, q > m} Ioc m q`（有向族，`Directed.measure_iUnion`），
   Ωᶜ 零测，得 `∫_{Ioi m} g² dμ ≤ c⁻²∫_{Ioi m} f'² dμ`；两侧相加并用 `variance_le_integral_sq_sub`，
   `gradient_eq_deriv'` 把能量写成 `∫ f'²`，得 `SmoothTest.Holds μ (1/c)²`。不需要 Cauchy–Schwarz、Fubini 或反常积分。
5. **方差下界。** 中位数处 `log ρ` 的支撑斜率 k（右斜率上确界）给 `ρ s ≤ c·e^{k(s−m)}`；与弦下界/上界的
   指数积分（`ExpIntegral`）结合，分 `k` 的符号与 x 相对 m 的位置四种情形得 `ρ ≤ c + k(F − 1/2)`。
   令 `φ(u) = (u−1/2)/c − k(u−1/2)²/(2c²)`，`Ψ(x) = φ(F x) − (x − m)`，`Ψ' = ρ(c − kδ)/c² − 1 ≤ 0`
   （`r(c − kδ) ≤ c²` 当 `0 ≤ r ≤ c + kδ`），FTC 给 `Ψ ≤ 0`（x ≥ m）、`Ψ ≥ 0`（x ≤ m），故
   `φ(F)(F−1/2) ≤ (x−m)(F−1/2)` 于 Ω；均匀推前给 `∫φ(F)(F−1/2) dμ = 1/(12c)`；`∫(F−1/2) dμ = 0` 把
   `x − m` 换成 `x − E`；`ab ≤ c a²/2 + b²/(2c)` 与 `∫(F−1/2)² = 1/12` 给 `Var ≥ 1/(12c²)`。
6. **装配。** `(1/c)² = 12·(1/(12c²)) ≤ 12·Var`，`Holds.mono`；`smoothTest_constant_eq_localSlope` 与
   `constant_le` 给 `Intrinsic.constant ν ≤ ofReal (12 Var)`；`ofReal_variance` 给扩展方差形式。

坑：`theorem` 的 section 变量只按 statement 包含（`continuous_cdf` 等需 `include d in`）；`HasDerivAt.mul`
与 `^2` 的实例路径不同，`simpa`/`convert` 失败而 `exact` 成立；`Continuous.intervalIntegrable` 的 `a b` 参数若写在
括号外会被当作外层函数的参数；`if_pos ⟨_, _⟩` 需写 `And.intro`；`set` 的 `Directed` 族用 `if … then … else ∅`
以 ℚ 为指标避免子类型上的 `max`；`Set.mem_Ioi`/`mem_Iic` 形式的假设需先 `have : x < s := hsx` 才能供 `linarith`
使用；`positivity` 不识别 `variance` 非负；`ENNReal.ofReal_eq_coe_nnreal` 把 `ofReal` 换成 `NNReal` 强制转换以套用
`constant_le`。

## 元数据同步

- ledger 新增 `thm:one-dimensional-logconcave-poincare`（proved / lean，`kind: lemma` 按仓库遗留规则），十九个
  proved 节点；`check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块；根聚合
  `FunctionalInequalities.lean` 导入 `KLS.LogConcave.Line.Poincare`（传递导入 `Probability/Line/*` 与 `Line/*`）。
- Blueprint 定理块锚定十六条声明与证书，声明与证明标 `leanok`；路线 sidecar 的 claim 由 `imported` 改为 `proved`，
  新增 Lean 证据并保留 Bobkov 的 published 引用作为出处。
- tasks.json：节点改为 `available`，登记七个新模块、`LocalSlope/Basic.lean` 与所用的库内、Mathlib 依赖哈希；
  `LocalSlope/Basic.lean` 追加两条引理后，三个引用它的既有证据哈希同步刷新。
- 当前指南：HANDOFF（新节、十九计数、证书表、条件纤维分支与"一维输入"文字、下一阶段列表）、README、
  `verification.md`、`solutions/README.md`、`formalization/README.md`、`blueprint/README.md`、`KLS/README.md`、
  `KLS/LogConcave/README.md`（`Line/` 五行与依赖说明）、`Poincare/README.md`、`naming.md`（`Probability.Line.cdf`、
  `KLS.LineDensity` 与 12·Var 命名）、根模块文档要点。statement golden、`STATEMENT_CHECKS` 未动。

## 证据边界

默认 `lake build` 通过（3369 jobs），证书与十三条库级声明有标准公理守卫。最终验证收据由
`python3 research/verify.py` 在本记录及所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。
本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI、commit 或 push；本地与远端分支的分叉留待用户处理。

## 补记：与原文系数 4 的差异及文献核实（2026-09-10，同日追加）

用户指出条件纤维桥原文写的是系数 4，本次认证的一维输入是 12，因而接下来能装配的是
`D_{μ,ρ}(f) ≤ 12∫|∇f|² dμ`，`Var_μ(f) ≤ C·D_{μ,ρ}(f) ⟹ C_P(μ) ≤ 12C`：路线对 KLS 的充分性保留，数值 4 未复现。
同日对系数 4 的文献核实结果：

- Bobkov 1999（Ann. Probab. 27, p. 1915）Corollary 4.3 给出 `1/(12 Var) ≤ λ₁ ≤ 1/Var`，并明确写道
  "We do not know, however, if the constant on the left is optimal"；Proposition 4.1 的两个界
  `1/√(3 Var) ≤ Is ≤ √2/√Var` 分别在均匀律与双边指数律取等。
- Cattiaux–Guillin 的 arXiv 2018 版 (2.25) 与 GAFA 修订版 (2.13) 均为 `Var_ν(f) ≤ 4 Var_ν(x) ν(|∇f|²)`，
  注明"credited to Kannan, Lovász and Simonovits, mentioned in [Alonso-Gutiérrez–Bastero] p.11"，
  对一维应用的措辞两版都是 "it seems that we may replace 12 by 4"。KLS 1995 的原始位置本次仍无法取得，
  与 2026-09-05 评审记录"primary KLS 1995 location … not verified"一致。
- 指数律 `e^{-x}`（`C_P = 4`，`Var = 1`）说明任何 κ < 4 都不成立：4 是下限。
- 本地证明路线到不了 4：Hardy 步 `C_P ≤ 1/ρ(m)²` 在指数律取等，方差步 `Var ≥ 1/(12ρ(m)²)` 在均匀律取等，
  两步乘积的极值律不同；Cheeger 路线同样受均匀律限制（`h·σ = 2/√12 < 1`）。可能的路线是
  Muckenhoupt 定理 `C_P ≤ 4B`（`B = sup_x μ(Ioi x)∫_m^x ρ⁻¹` 及镜像）加上对数凹律的 `B ≤ Var`；后者在
  指数、均匀、Gauss、Laplace、截断指数、指数加均匀等例子上数值成立（截断于 2π 的指数律 0.88 对 0.926），
  但目前没有证明，也未在文献中找到。
- CMH 精确值（线、乘积、Dirichlet 分布）属于矩映射 Stein 核常数，仓库尚无 CMH(μ) 与 W₂ 定义
  （`thm:cmh-recovery-affine-poincare-bound` 记为 missing），与本节点和现有 Gaussian 结果不可比。

结论：系数 4 目前是未经验证的文献主张而非可形式化的定理输入；本节点保持 12，Blueprint 的历史出处段落不变。

### 补记二：Alonso-Gutiérrez–Bastero 原书核实（2026-09-10，同日追加）

用户提供了 Alonso-Gutiérrez–Bastero（LNM 2131, 2015）全书 PDF。核实结果：

- p.11（Section 1.4 开头）原文为 "Kannan, Lovász and Simonovits [37] proved that
  `Var_μ f ≤ 4 inf_{x₀∈ℝⁿ} E_μ|x − x₀|² E_μ|∇f|²` for any locally Lipschitz function f in L²(μ)"，
  是一般维数 n 的陈述，只引用 KLS 1995，书中没有证明。
- 书中实际证明的 KLS 结果是 Theorem 1.13（Section 1.6.1，局部化方法）：Cheeger 型不等式
  `μ⁺(A) ≥ (C / inf_{x₀} E|x − x₀|) min{μ(A), μ(Aᶜ)}`，常数 C 是未具体化的绝对常数。
- 书中一维情形是 Theorem 1.5（Section 1.4.2，沿 Bobkov）：`1/(3 Var) ≤ Is(μ)² ≤ 2/Var`，
  `Is(μ) = 2 e^{−W(a)}`（a 为中位数），以及 `1/(12 Var) ≤ λ₁(μ) ≤ 1/Var`——正是本节点认证的常数 12。

结论：该书不能作为一维系数 4 的证明来源；4 的唯一可能原始出处仍是 KLS 1995 本文，待取得后核对。
本节点保持 12。
