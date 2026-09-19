# 半群生成路线：`S7`（半群律与强连续）与 `S8`（生成元）路线轮

2026-09-19，紧接 [`S6` 轮](2026-09-19-yosida-limit-route.md)。本轮**只写定义与语句，不证明**；
证明交给并行 Opus 会话，依赖关系决定分三批。不 commit、不推送。

## 定义模块（本轮已写并编译）

`formalization/FunctionalInequalities/Analysis/Semigroup/Generated.lean`：把 `S6` 里存在量化的极限命名为算子。

| 声明 | 内容 |
| --- | --- |
| `semigroupApply T hT hd t f` | `t ≥ 0` 时取 `exists_limit_exp_neg_smul_yosida` 给出的极限（`Classical.choose`），`t < 0` 时取 `f` |
| `semigroupApply_spec` | `t ≥ 0` ⟹ `exp(-t • L_s) f → semigroupApply t f`（ε–δ） |
| `semigroupApply_of_not_nonneg` | `t < 0` 的约定值 |

形式上 `P_t f = exp(-t T†T) f`。`P_t` 的线性与压缩在路线里是待证义务（`P2`、`P3`），所以这里只定义函数，
`ContinuousLinearMap` 版本留给证明模块打包。

## 语句文件

`research/audits/GeneratedSemigroupRouteStatements.lean`，只含 `#check`，11 条全部通过类型检查：

| 编号 | 内容 | 输入 | 风险 |
| --- | --- | --- | --- |
| `P1` | 极限唯一：满足 ε–δ 收敛的 `g` 等于 `P_t f` | `semigroupApply_spec` | 低 |
| `P2` | `P_t` 线性 | `P1` | 低 |
| `P3` | `‖P_t f‖ ≤ ‖f‖` | `S5` + 极限 | 低 |
| `P4` | `⟪P_t f, g⟫ = ⟪f, P_t g⟫` | `yosida_symm` → `IsSelfAdjoint (L_s)` → `IsSelfAdjoint.exp` → `adjoint_inner_left`，取极限 | 中低：Mathlib 的 star = adjoint 结构 |
| `P5` | `P_0 = 1` | `exp_zero` + `P1` | 低 |
| `P6` | `P_{t+u} = P_t P_u` | `exp_add_of_commute` + `S5` + `P1` | 中 |
| `P7` | `‖P_t f − f‖ → 0`（`t ↓ 0`） | `Y6`（`B = 0`）+ `Y5` + 稠密 + `P3` | 中 |
| `P8` | `ContinuousOn (t ↦ P_t f) (Ici 0)` | `P6` + `P3` + `P7` | 中低 |
| `G1` | `S6` 收敛在 `τ ∈ [0, t]` 上一致 | `Y6` 的界对 `τ ≤ t` 一致 + 稠密 + 压缩 | 中 |
| `G2` | `‖e^{-tA} f − f + t·Af‖ ≤ C·t`，若 `‖e^{-τA}(Af) − Af‖ ≤ C` 于 `[0,t]` | `hasDerivAt_exp_smul_const'` + 中值不等式；不需 `A` 非负 | 中低 |
| `G3` | `S8`：`f ∈ D(T†T)` ⟹ `‖(P_t f − f)/t + T†T f‖ → 0` | `P7` + `G1` + `G2` + `Y5` + `S5` | **中高**：本路线的核心组装 |

`G3` 的证法刻意避开 Bochner 积分：不写 `P_t f − f = −∫₀ᵗ P_τ T†T f dτ`，而是对 `φ(τ) = e^{-τL_s} f − f + τ L_s f` 用中值不等式（`G2`），
导数界靠 `Y5`（`L_s f ≈ T†T f`）、`G1`（`e^{-τL_s} g ≈ P_τ g` 对 `τ ≤ t` 一致）与 `P7`（`P_τ g ≈ g`），再令 `s ↓ 0`。

## 分工（三批）

1. 会话 A：`P1`–`P8`，新模块 `Analysis/Semigroup/SemigroupLaws.lean`，审计 `research/audits/SemigroupLawsAudit.lean`。
2. 会话 B（与 A 并行）：`G2`，纯有界算子，新模块 `Analysis/Semigroup/ExpMeanValue.lean`，审计 `research/audits/ExpMeanValueAudit.lean`。
3. 会话 C（A、B 之后）：`G1`、`G3`，新模块 `Analysis/Semigroup/Generator.lean`，审计 `research/audits/GeneratorAudit.lean`，
   import A、B 的模块。

规则同前：只建新文件、只用 `lake env lean -DwarningAsError=true`、不 `lake build`、不 `verify.py`、不 git、不改既有文件、零 `sorry`。

## 明确没做什么

`S7`–`S8` 证完，半群生成路线（缺口一）即告完成，但 Buser 半仍差 Markov 性（缺口二）、Bakry–Émery Γ 演算（缺口三）、
小时间热估计（缺口四）。`thm:logconcave-cheeger-poincare-comparison` 无进展标记，`tasks.json` 未改（集成时统一登记）。

## 追加：`P1`–`P8`、`G1`–`G3` 全部证出，`S7`、`S8` 关闭；半群生成路线 `S1`–`S8` 完成（同日，三批 Opus 会话约 13、4、8 分钟）

| 编号 | 声明 | 模块 |
| --- | --- | --- |
| `P1` | `eq_semigroupApply_of_tendsto` | `SemigroupLaws.lean` |
| `P2` | `semigroupApply_smul_add`（另有 `semigroupApply_sub` 等推论，及 `semigroupCLM` 打包） | `SemigroupLaws.lean` |
| `P3` | `norm_semigroupApply_le` | `SemigroupLaws.lean` |
| `P4` | `inner_semigroupApply_left` | `SemigroupLaws.lean` |
| `P5` | `semigroupApply_zero` | `SemigroupLaws.lean` |
| `P6` | `semigroupApply_add` | `SemigroupLaws.lean` |
| `P7` | `exists_delta_norm_semigroupApply_sub_self_lt`（定量版 `norm_semigroupApply_sub_self_le`：`‖P_t f − f‖ ≤ t(‖T†T f‖ + 1)`） | `SemigroupLaws.lean` |
| `P8` | `continuousOn_semigroupApply` | `SemigroupLaws.lean` |
| `G1` | `exists_delta_norm_exp_neg_smul_yosida_sub_semigroupApply_lt` | `Generator.lean` |
| `G2` | `norm_exp_neg_smul_sub_add_smul_le`（一般完备实范数空间；`InnerProductSpace` 未用，逐字包装 `route_G2`） | `ExpMeanValue.lean` |
| `G3` = `S8` | `exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt`（定量版 `norm_semigroupApply_sub_self_add_smul_le`） | `Generator.lean` |

审计：`SemigroupLawsAudit.lean` 29 条、`ExpMeanValueAudit.lean` 5 条、`GeneratorAudit.lean` 8 条 `#print axioms`，
**42 条全部只有 `propext, Classical.choice, Quot.sound`，0 条 `sorryAx`**；11 条路线语句逐 token 与路线文件一致（本会话独立重编译并机械比对）。
四个新模块（`Generated`、`SemigroupLaws`、`ExpMeanValue`、`Generator`）已进聚合根，`lake build` 3532 jobs 通过，
十四个半群审计 / 路线文件严格重编译均 exit 0。除 `G2` 的 `InnerProductSpace` 外没有路线假设可以去掉。

### 与草稿不同之处

* **`G3` 草稿的 ε 拆分给不出严格不等式**：按草稿的 ε/3 三分法除以 `t` 后只得 `≤ ε`，而语句要求 `< ε`。实际用 `ε/8 + ε/4 + ε/4 + ε/8 = 3ε/4`，
  终点 `7ε/8 < ε`。路线文件未改。
* `G1` 在 `D(T†T)` 上先证 `≤ ε` 形式（对辅助参数 `r` 取极限只能得非严格），一般 `g` 再由三个严格的 ε/3 恢复严格性。
* `G2` 用不带撇的 `hasDerivAt_exp_smul_const` 后完全不需要交换引理，一次编译通过。

### 半群生成路线（缺口一）完成

`S1`–`S8` 全部是本地零洞 Lean 证明，`Analysis/Semigroup/` 下 14 个模块。对闭且稠定的 `T : H₀ →ₗ.[ℝ] H₁`，
`semigroupApply T hT hd`（`semigroupCLM`）是 `H₀` 上的强连续自伴压缩半群，`P_0 = 1`、`P_{t+u} = P_t P_u`，
生成元在 `D(T†T)` 上是 `−T†T`。**这只是 Buser 纲领四个前置里的第一个**：缺口二（Markov 性）、三（Bakry–Émery Γ 演算）、
四（小时间热估计）原封未动，`thm:logconcave-cheeger-poincare-comparison` 无 `\leanok`，常数 π 未被触及。
`tasks.json` 该节点 `infrastructure.status` 保持 `missing`，第一条 gap 追加「半群构造已完成」的说明，其余三条 gap 不变。

### 摩擦（供下一轮）

`NormedSpace.exp_add_of_commute` 在 `H₀ →L[ℝ] H₀` 上缺 `NormedAlgebra ℚ` 实例，用 `exp_add_of_commute_of_mem_ball (𝕂 := ℝ)` +
`expSeries_radius_eq_top ℝ _`。`abs_add` 不存在，用 `abs_add_le`。`IsSelfAdjoint.smul` 需 `show IsSelfAdjoint (-t) from star_trivial _`。
`push_neg` 在本 pin 已弃用（`-DwarningAsError` 下报错），用 `rw [not_le]`。`div_add_div_same` 不存在。
`field_simp` 独自关掉目标后再 `ring` 会报 "No goals"。
