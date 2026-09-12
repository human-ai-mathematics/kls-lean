# 2026-09-11 — `thm:one-dimensional-logconcave-poincare`：常数从 12 加强到 4

## 决定

- Blueprint 节点 `thm:one-dimensional-logconcave-poincare` 的陈述由 `C_P^lit(ν) ≤ 12 Var_ν(T)` 改为
  `C_P^lit(ν) ≤ 4 Var_ν(T)`；这是**陈述变更**（加强），不是新节点。Bobkov 的 12 作为推论保留，并保留其
  独立证明（`KLS/LogConcave/Line/Poincare.lean` 不改动）。
- 证据来源：合作者审计 `research/explorations/2026-09-11-poincare-constant-4-audit.md`（用户于 2026-09-11 提供，
  逐步核对无误，见 2026-09-10 决定记录补记一、二对文献状态的核实：4 在 Alonso-Gutiérrez–Bastero p.11 只引不证）。
  本地 Lean 证明按该审计的 x 坐标版本组织，不引入分位数函数。
- 常数 4 在指数律取等，不再有更小的普适常数可断言。
- 不提交、不推送（用户指令）。

## Lean 陈述（formech 风格）

主张（`Solutions.ThmOneDimensionalLogConcavePoincare.certificate`）：对每个 `ν : ProbabilityMeasure ℝ`、
`hν : KLS.LogConcave ν`：

1. `Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (4 * variance id ν)`；
2. `Poincare.LocalSlope.Intrinsic.constant ν ≤ 4 * evariance id ν`。

类型化应用：常数有限；`≤ ENNReal.ofReal (12 * variance id ν)`（由 4 推出）；Dirac 律常数 `≤ 0`；支撑内部非空时
`Poincare.SmoothTest.Holds ν (4 * variance id ν)`。

不主张：更小常数、高维界、Cheeger 不等式、原始能量上的结论、`cor:conditional-fiber-twelve-bound` 的加强
（该推论仍记 `12C`，属于 50 章，另一会话正在编辑，留作后续）。

有限范围：无。零维：仿射支撑为一点时方向空间为 `⊥`，常数为 0（沿用 `Line/Poincare.lean` 的处理）。

## 逐句对齐（Blueprint ↔ Lean）

| Blueprint | Lean | 结论 |
|---|---|---|
| 支撑线 `ρ ≤ A(1−F)+BF`，`A,B ≥ 0` | `d.le_affine_of_supergradient`、`d.affine_pos_of_bound`、`Probability.Line.nonneg_of_affine_pos` | 一致；Lean 用 `x₀ ∈ Ω` 处的支撑指数 `d.exists_supergradient` |
| `q∘F` 1-Lipschitz，`Var_{[0,1]}(q) ≤ σ²` | `d.variance_ge_of_affine_bound` 内部：`Var Ψ(X) ≤ E(Ψ X − Ψ E)² ≤ E(X−E)²`，均值 `E ∈ Ω`（`LogConcave.mean_mem_interior_support`） | 一致；Lean 用均值代替任意锚点 |
| `Var_{[0,1]}(q) ≥ (√A+√B)^{-4}` | `Probability.Line.one_div_le_variance_affineQuantile`（闭形式 `variance_affineQuantile` + `mul_mul_log_sub_sq_le`，后者经 `t ≤ sinh t`） | 一致 |
| 轮廓界 `F(1−F) ≤ σρ` | `d.cdf_mul_one_sub_cdf_le_sd_mul`（ε 扰动 `A+ε, B+ε` 后取极限） | 一致 |
| 截断测试、`∫h² = −∫_a^b f'G̃` | `KLS.clip`、`clipCentered`、`tailIntegral`、`d.integral_sq_clipCentered_eq` | 一致 |
| 基态恒等式与边界项 | `d.groundState_inequality`（在更大区间 `[c,e]` 上）、`d.boundaryTerm_le_of_le`、`d.neg_boundaryTerm_le_of_ge`、`d.integral_sq_div_le`（`F c → 0`、`F e → 1` 的 ε 论证） | Lean 更强：明确给出边界项 `h(a)²F(c) + h(b)²(1−F(e))` |
| `Var(f_ab) ≤ 4σ²∫f'²` | `d.variance_clip_le`（AM–GM `−f'G̃ ≤ G̃²ρ/(8W²) + 2f'²W²/ρ` + 轮廓界） | 一致 |
| 尾项消失 | `d.setIntegral_Iic_sq_sub_le_of_le`、`d.setIntegral_Ioi_sq_sub_le_of_le`（`Hardy.lean` 中中位数版本的推广，锚点 `p` 在中位数同侧、常数仍为 `1/ρ(m)²`）+ `Probability.exists_pos_forall_setIntegral_le`（积分对测度的绝对连续性）+ `exists_cdf_eq` 选 `F a = t` | 一致；审计原稿用 `f(a)²F(a)` 与 `∫_{Iic a} f²` 的双情形（Ω 下有界/无界）论证，Lean 改用锚定 Hardy 界，避免情形分裂 |
| `(1+δ)` 分裂并取极限 | `Probability.add_sq_le_split`、`d.variance_le_four_variance_mul`（`le_of_forall_pos_le_add`） | 一致；审计原稿用 Minkowski，Lean 用无平方根的 δ 分裂 |
| 光滑测试最优值 = 文献最优值 | `LogConcave.smoothTest_constant_eq_localSlope`（已认证） | 一致 |

## 证明中的数学修正

- 第一版计划在 `[a,b]` 上直接截断基态恒等式，边界项符号相反（`Ξ(a) ≥ 0 ≥ Ξ(b)`），不可行；改为在包含
  `[a,b]` 的更大区间 `[c,e] ⊆ Ω` 上积分，并用 `G̃ = h(a)F`（`x ≤ a`）、`G̃ = −h(b)(1−F)`（`x ≥ b`）控制
  `Ξ(c) ≤ h(a)²F(c)`、`−Ξ(e) ≤ h(b)²(1−F(e))`，再令 `F(c) → 0`、`F(e) → 1`。

## 文件

- 新：`Probability/Line/AffineProfile.lean`、`KLS/LogConcave/Line/Profile.lean`、`Line/SharpHardy.lean`、
  `Line/SharpPoincare.lean`。
- 改：`Probability/Line/Cdf.lean`（`exists_cdf_eq` 一般 `t`、`cdf_pos/lt_one_of_mem_interior_support`）、
  `KLS/LogConcave/Line/Hazard.lean`（`le_add_mul_cdf_sub_of_mem`，中位数版本为推论）、
  `KLS/LogConcave/Line/Hardy.lean`（四条半直线/区间 Hardy 引理推广为 `_of_le` 版本，原名保留为 `p = m` 的包装）。
- 证书：`solutions/ThmOneDimensionalLogConcavePoincare.lean` 主张改为 4，新增 9 条公理守卫。
- 登记：ledger 陈述/来源、`tasks.json`（新增证据文件与哈希）、Blueprint `\lean{}` 与陈述/证明、
  `route-composition.yaml` 出版参考、`FunctionalInequalities.lean` 导入、各 README/HANDOFF/verification/naming。

## 后续

- `cor:conditional-fiber-twelve-bound`（50 章）可由 `12C` 加强为 `4C`；待另一会话的 ConditionalFiber 工作完成后处理。
- KLS 1995 原文中常数 4 的位置仍未核对；本地证明已不依赖该出处。
