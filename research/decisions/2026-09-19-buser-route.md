# Buser 半 `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` 的路线探查：障碍定位与分阶段纲领

2026-09-19。Energy 五洞归零后，Owner 指示接着做 Cheeger–Buser 的 Buser 半。本轮是**路线探查**，**没有证明任何定理**，
没有改动任何既有 `.lean`；交付物是障碍的精确定位、Mathlib 与本仓库的如实检索、一个**分阶段纲领**，
以及只含 `#check` 的路线语句文件 `research/audits/BuserRouteStatements.lean`。**命题通过类型检查不是证明。**
直接洞 **0**，证书 **26**，不变。不提交、不推送。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T151845.800831Z/report.json`：10 个门、241 个模块重放、662 条目，快照 `1fc50cd6d74a2b42f74600fc30b5b245316a9d58d53e034f05cd56f2a033606d`。

## 一、结论先行

**Buser 半在 `n ≥ 2` 维不是一轮能做的事，是一个纲领。** 对数凹律的所有已知证明都经过两种基础设施之一，
而两者在 Mathlib 与本仓库里都不存在：

1. **加权热半群 + Bakry–Émery 梯度界**（Ledoux 的论证；De Ponti–Mondino 在 `RCD(0,∞)` 上得到尖锐常数 `π`）。
   需要：半群的存在（Mathlib 没有 Hille–Yosida，没有无界自伴算子谱定理；本仓库有 Cheeger 能量的闭二次型
   `Energy/ClosedQuadratic.lean`、`FormCore.lean`，但没有由它生成半群的工具）；`‖∇P_t f‖² ≤ P_t‖∇f‖²`
   （`CD(0,∞)`，要么靡抛物 PDE 正则性——对数凹律的支撑可能是带边凸体、密度可能不光滑——要么经 Wasserstein 收缩 / EVI 的刻画）；
   然后是 Ledoux 的对偶估计 `‖f − P_t f‖₁ ≤ c√t · μ⁺(A)` 与谱衰减 `‖P_t f − μA‖₂ ≤ e^{−t/C_P}‖f − μA‖₂` 的比较，`t` 取最优。
2. **局部化 / 针分解**（Lovász–Simonovits 对分、Klartag 的针分解）。对分与针极限是初等测度论与凸几何，但很长；
   更要紧的是**转移论证**：针是一维对数凹律，`Q1`–`Q3` 那样的一维估计给 `h(针) ≳ 1/σ(针)`，但把 `σ(针)` 与 `C_P(μ)`
   联系起来没有初等办法（沿固定方向的条件方差只在平均意义下受 `Var⟨x,θ⟩ ≤ ‖Cov‖ ≤ C_P` 控制，逐针不受控；
   而 `h ≳ 1/√‖Cov‖` 是 KLS 猜想本身）。E. Milman 的「凸性下集中蕴含等周」需要半群或 GMT 正则性；Klartag 2017 用针分解重证它时，
   转移一步用的仍是曲率–维数条件下的一维比较，落到 Lean 里同样是整套针分解。

**Mathlib 检索**：无热核/热方程、无 Ornstein–Uhlenbeck、无 Bakry–Émery、无局部化引理、无对数凹性、无 Prékopa–Leindler
（`Analysis/Convex/Intrinsic.lean` 与凸几何相关但无关等周）。有：卷积、`ContDiffBump`、Gaussian 分布、Fourier 变换、方差与 `evariance`。
**本仓库有**：一维对数凹律的 Borell 密度与 hazard 界（`KLS/LogConcave/Line/{Density,Hazard}.lean`：`2ρ(m)F(x) ≤ ρ(x)`、
`2ρ(m)(1−F(x)) ≤ ρ(x)`、中位数存在）、一维 Prékopa–Leindler（`Probability/Line/BrunnMinkowski.lean`）、
一维对数凹 Poincaré 证书（`C_P^lit ≤ 4 Var`）、线性测试下界（`Var ≤ C_P^smooth`）、条件纤维（沿固定方向的一维化，
给的是 Poincaré 型而非等周型结论）、刚证出的 `h_M = h_S`（`lem:relative-perimeter-cheeger-infimum`）与 Cheeger 半。

## 二、分阶段纲领

**阶段一（本轮定义，可立即开工）：一维、显式常数 12。** 在直线上一切材料都已就位：
* `Q1` 一维等周 `h_M(ν) ≥ 2ρ(m)`。经已认证的 `h_M = h_S` 化为光滑域形式 `Q1'`：`ℝ` 的光滑域是边界离散的开集，
  相对周长是 `ρ` 在（支撑内部的）边界点上的和（`ℋ⁰` 计点）；含中位数的分支给 `ρ(a) + ρ(b) ≥ 2ρ(m)(F(a) + 1 − F(b)) ≥ 2ρ(m)(1 − νU)`，
  其余分支给 `ρ(端点) ≥ 2ρ(m)·ν(分支)`，求和。
* `Q2` `ρ(x) ≤ 2ρ(m)`：以 `κ` 记 `log ρ` 从中位数向众数方向的斜率，远侧半质量给 `κ ≤ 2ρ(m)`，近侧半质量给 `ρ(众数) ≤ ρ(m) + κ/2`。
  指数律取等。
* `Q3` 密度 `≤ M` 的律方差 `≥ 1/(12M²)`（不需要对数凹）：均值两侧质量 `p`、`1−p` 各自的二阶矩不小于长 `p/M` 区间上均匀分布的，
  `p³ + (1−p)³ ≥ 1/4`。
* `Q4` 线性测试 `Var(id) ≤ C_P^smooth`（恒等映射是单位梯度能量的光滑测试）；`Q5` 对数凹律二阶矩有限。
* `Q0` 装配：`Ψ² = h_M⁻² ≤ (2ρ(m))⁻² ≤ ρ_max⁻² ≤ 12·Var ≤ 12·C_P^smooth`；`Q0'` 经文献常数识别与 `h_μ = h_M(ν)`
  搬到仿射支撑维数 `≤ 1` 的 `μ`（Dirac 律两侧皆 0）。

常数 **12 不是 π**：阶段一在一维以更差的常数证 Buser 半，对 `n ≥ 2` 什么也不说。Blueprint 节点保留 `π`；若纲领最终以非尖锐常数闭合，
必须**显式**减弱 Blueprint 陈述而不是悄悄替换。

**阶段二（未开始）**：(a) 由 Cheeger 闭二次型构造 Markov 半群（先补 Hille–Yosida 或至少对称收缩半群的谱构造）、证 Bakry–Émery 梯度界、
跑 Ledoux 论证；或 (b) 形式化 Lovász–Simonovits 对分与针极限，再找转移论证。两者估计都在数千行且带 Mathlib 级前置条件。

## 三、义务清单（阶段一）

精确 Lean 语句在 `research/audits/BuserRouteStatements.lean`（7 条引用已证声明，10 条命题：`B0`、`Q0`、`Q0'`、`Q1`、`Q1'`、`Q2`–`Q5`、`D1`）。

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `B0` | **纲领目标**：Buser 半，任意维，常数 `π` | — | 阶段二，未开始 |
| `Q0` | 直线上 `Ψ² ≤ 12 C_P^smooth` | 40 | 低（`Q1`–`Q5` 合成） |
| `Q0'` | 仿射支撑维数 `≤ 1` 的 `μ`：`Ψ_KLS² ≤ 12 C_P^lit` | 120 | 中（一维方向空间与 `ℝ` 的等距搬运） |
| `Q1'` | 光滑域形式的一维等周 | 300 | **中–高**（`ℝ` 上光滑域的边界离散、分支枚举、`ℋ⁰` 计点） |
| `Q1` | `2ρ(m) ≤ h_M` | 20 | 低（`Q1'` + `h_M = h_S`） |
| `Q2` | `ρ ≤ 2ρ(m)` | 120 | 中（支撑线 + 两侧半质量的积分估计） |
| `Q3` | `Var ≥ 1/(12M²)` | 150 | 中（bathtub 重排） |
| `Q4` | `Var(id) ≤ C_P^smooth` | 30 | 低 |
| `Q5` | 对数凹律 `id ∈ L²` | 20 | 低（已有矩结果） |
| `D1` | `π < 12` | 2 | 记账 |

合计约 **800 行**。推荐顺序：`Q5`、`Q4`、`Q3`、`Q2`、`Q1'`、`Q1`、`Q0`、`Q0'`。

## 四、明确没证什么

* `B0` 未证，且本轮不声称任何 `n ≥ 2` 的 Buser 型结论。`thm:logconcave-cheeger-poincare-comparison` 不标 `\leanok`。
* 阶段一的常数是 12，不是 π。无量纲 KLS 仍开。

## 五、验证

路线文件以 `lake env lean -DwarningAsError=true` 通过，17 个 `#check`，0 错误、0 警告；
日志 `build/audit/buser-route/route-statements.log`。回执在紧接的实现轮绑定。

## 附记（2026-09-19，阶段一实现轮之后）

阶段一全部义务 `Q0`、`Q0'`、`Q1`、`Q1'`、`Q2`–`Q5` 证出（`KLS/LogConcave/Line/{Isoperimetry,Buser}.lean`），语句逐字不变。
两处证法与本记录不同：`Q1'` 不需要边界离散与分支枚举（对任意含中位数的开集，`sSup (Iio m \ W)`、`sInf (Ioi m \ W)` 两个边界点即够）；
`Q3` 由 `Line/Variance.lean` 已认证的中位数方差界导出，未写 bathtub 重排。`B0` 与阶段二未动。见 [实现记录](2026-09-19-buser-line-proofs.md)。
