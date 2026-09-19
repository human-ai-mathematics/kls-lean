# 半群生成路线：`S6`（Yosida 指数的强收敛）路线轮

2026-09-19，紧接 [von Neumann 轮](2026-09-19-von-neumann-route.md)。本轮**只写定义与语句，不证明**；
证明交给两个并行的 Opus 会话，`Y8` 由本会话在集成时组合。不 commit、不推送。

## 对早先路线的一处修正

`SemigroupGenerationRouteStatements.lean` 里 `S6` 的**抽象**写法——对任意只满足非负与交换的族
`L : ℝ → H₀ →L[ℝ] H₀`，`exp(-t • L s) f` 随 `s ↓ 0` 收敛——**是假的**。反例：`L s = c(s) • 1`，
`c` 在两列趋于 `0⁺` 的点上分别取 `0` 和 `1`，则 `exp(-t • L s) f = e^{-t c(s)} f` 无极限。
按惯例路线文件保持字节不变，反例作为 `Y0` 明确陈述并交付证明；修正后的抽象 `S6` 是 `Y7`
（多一个「在稠密集上 Cauchy」的假设），Yosida 近似的 `S6` 是 `Y8`。

## 定义模块（本轮已写并编译）

`formalization/FunctionalInequalities/Analysis/Semigroup/YosidaApproximation.lean`：
`yosida T hT hs := s⁻¹ • (1 - resolventCLM T hT hs)`，即 `L_s`，加 `yosida_apply`、`smul_yosida_apply` 两条 `simp` 级引理。
`-DwarningAsError=true` 通过，olean 已生成。

## 语句文件

`research/audits/YosidaLimitRouteStatements.lean`，只含 `#check`，9 条全部通过类型检查：

| 编号 | 内容 | 输入 | 风险 |
| --- | --- | --- | --- |
| `Y0` | 抽象 `S6` 在 `H₀ = ℝ` 上为假 | 无 | 低中：构造 `c`，证两列子列极限不同 |
| `Y1` | `0 ≤ ⟪L_s f, f⟫` | `norm_resolventCLM_le` | 低 |
| `Y2` | `⟪L_s f, g⟫ = ⟪f, L_s g⟫` | `resolventCLM_symm` | 低 |
| `Y3` | `L_s L_r = L_r L_s` | `R3` | 低 |
| `Y4` | `L_s f = J_s (T†T f)`，`f ∈ D(T†T)` | `V5` | 低 |
| `Y5` | `L_s f → T†T f`，`f ∈ D(T†T)`（ε–δ） | `Y4` + `R2` | 低 |
| `Y6` | `‖e^{-tA} f − e^{-tB} f‖ ≤ t‖Af − Bf‖`，`A, B` 有界非负交换 | `S5`、`hasDerivAt_exp_smul_const`、`Commute.exp_right`、中值不等式 | **中高**：本路线的解析核心 |
| `Y7` | 修正的抽象 `S6`：稠密集上 Cauchy ⟹ 处处收敛 | `Y6` + `S5` + 完备性 | 中：ε/3 论证 |
| `Y8` | Yosida 近似的 `S6` | `Y7` + `Y1` + `Y3` + `V4` + `Y5` | 低：组合 |

所有 `s ↓ 0` 极限用 ε–δ 形式（`resolventCLM`、`yosida` 携带 `0 < s`），族写成 `∀ s, 0 < s → H₀ →L[ℝ] H₀`；
只有 `Y0` 用 `Tendsto` 与 `𝓝[>] 0`，以逐字对应原 `S6`。

## 分工

* 会话 A：`Y0`–`Y5`，新模块 `Analysis/Semigroup/YosidaFamily.lean`，审计 `research/audits/YosidaFamilyAudit.lean`。
* 会话 B：`Y6`–`Y7`（纯有界算子，不 import 任何 `T`），新模块 `Analysis/Semigroup/SemigroupLimit.lean`，
  审计 `research/audits/SemigroupLimitAudit.lean`。
* `Y8` = `Y7 ∘ (Y1, Y3, V4, Y5)`，两会话完成后由本会话组合进 `YosidaFamily.lean` 或独立小模块，并入审计。

规则同前：只建新文件、只用 `lake env lean -DwarningAsError=true`、不 `lake build`、不 `verify.py`、不 git、不改既有文件、零 `sorry`。

## 明确没做什么

`S7`（极限的半群律与强连续）、`S8`（生成元是 `T†T`）未陈述。Markov 性、Γ 演算、小时间热估计、Buser 不等式均不在本轮。
`thm:logconcave-cheeger-poincare-comparison` 无进展标记，`tasks.json` 未改（集成时统一登记）。

## 追加：`Y0`–`Y8` 全部证出，`S6` 关闭（同日；两个并行 Opus 会话约 9 与 11 分钟，`Y8` 由本会话组合）

| 编号 | 声明 | 模块 | 备注 |
| --- | --- | --- | --- |
| `Y0` | `not_forall_exists_tendsto_exp_neg_smul` | `YosidaFamily.lean` | 抽象 `S6` 为假，系数取 `Set.indicator` 于 `{1/(n+1)}`，第二列 `2/(2n+3)` |
| `Y1`–`Y3` | `yosida_nonneg`、`yosida_symm`、`yosida_comp_comm` | `YosidaFamily.lean` | 按草稿 |
| `Y4`、`Y5` | `yosida_apply_eq_resolventCLM_adjointComp`、`exists_delta_norm_yosida_sub_adjointComp_lt` | `YosidaFamily.lean` | **`Dense` 是真用到的**（V5 经 `inner_adjointComp` 依赖伴随的非垃圾值），与路线表的猜测相反 |
| `Y6` | `norm_exp_neg_smul_sub_le` | `SemigroupLimit.lean` | 插值路径取 `exp(τ•(-A))(exp((τ−t)•B) f)`，用不带撇的 `hasDerivAt_exp_smul_const`；中值不等式在本 pin 只要求 `Ico` 上的导数界 |
| `Y7` | `exists_limit_exp_neg_smul` | `SemigroupLimit.lean` | Cauchy 步在 `ε/(t+1)` 处调用假设以容纳 `t = 0` |
| `Y8` | `exists_limit_exp_neg_smul_yosida` | `YosidaLimit.lean` | `Y7 ∘ (Y1, Y3, V4, Y5)`，本会话写，一次通过 |

审计：`YosidaFamilyAudit.lean` 26 条、`SemigroupLimitAudit.lean` 11 条、`YosidaLimitAudit.lean` 4 条 `#print axioms`，
**41 条全部只有 `propext, Classical.choice, Quot.sound`，0 条 `sorryAx`**；9 条路线语句逐 token 与路线文件一致（本会话独立重编译并机械比对）。
四个新模块（`YosidaApproximation`、`YosidaFamily`、`SemigroupLimit`、`YosidaLimit`）已进聚合根，`lake build` 3528 jobs 通过，
十个半群审计客户端严格重编译均 exit 0。**没有任何路线假设可以去掉**，`Y6`、`Y7` 的每个假设都被使用。

### 半群路线现状

`S1`–`S6` 已证。剩 `S7`（极限 `P_t f := lim exp(-t L_s) f` 是强连续的自伴压缩半群：`P_{t+u} = P_t P_u`、`P_0 = 1`、`t ↦ P_t f` 连续、
`‖P_t f‖ ≤ ‖f‖`、对称）与 `S8`（生成元是 `T†T`：`f ∈ D(T†T)` ⟹ `(P_t f − f)/t → −T†T f`）。
下一步要先把 `Y8` 里存在量化的极限 `g` 命名为算子 `P_t`（选择函数或 `limUnder`），再陈述 `S7`、`S8`。

### 摩擦（供下一轮）

`NormedSpace.exp_smul` 是关于 `MulSemiringAction` 共轭的，不是标量；`ℝ →L[ℝ] ℝ` 上 `exp(a•1) x = Real.exp a * x`
用 `NormedSpace.map_exp` 沿代数映射传输。`ContinuousLinearMap.mul_apply`、`smul_apply` 在本 pin 已弃用（`-DwarningAsError` 下即错误），
用 `mul_def` + `comp_apply`、根命名空间 `smul_apply`。`div_le_div_iff` 已去，用 `div_le_div_iff₀`。
`ℝ →L[ℝ] ℝ` 上 `ext f` 触发 `unusedRCasesPattern`，用 `refine ContinuousLinearMap.ext fun f => ?_`。`⟪x, y⟫_ℝ = x * y` 是 `Real.inner_apply`，非 `rfl`。
