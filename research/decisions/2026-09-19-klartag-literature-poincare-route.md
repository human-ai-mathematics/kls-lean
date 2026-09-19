# Klartag 前端识别的文献 Poincaré 子句：路线探查

2026-09-19。当日第十二轮，前十一轮已提交为 `2a882c8`（未推送）。本轮是**路线探查**，
**没有证明任何定理**，没有改动任何既有 `.lean`；交付物是只含 `#check` 的路线语句文件
`research/audits/KlartagLiteraturePoincareRouteStatements.lean`（4 条义务 + 6 条已证声明引用，共 10 个 `#check`）。
**命题通过类型检查不是证明。** 直接洞仍 **0**，证书仍 **26**，无 WIP 模块。不提交、不推送。

起点 `HEAD = 2a882c89f59faaf23eb59d321a211422f5b24e3e`，领先 `origin/main = f108397` 一个提交；
起点 passed 回执 `build/verification/20260918T165957.183636Z/report.json`：10 个门、243 个模块重放、
26 条本地声明，快照 `4e5cb9cb5ef74a51343cbcf334a7fd5b154555a7e5777567aa62db2da729c8dd`。

## 为什么是这个节点

`atlas.py ready` 在回执刷新后，整张表里只有一个节点既不是 `research`、也不是 `blocked`、也不缺 Mathlib 基础设施：

```
inspect_infrastructure  thm:klartag-density-frontend-identification
blocked                 thm:logconcave-cheeger-poincare-comparison — 依赖它
```

`tasks.json` 记它为 `mathematics: local_argument`、`infrastructure.gaps: []`。它是 Cheeger–Buser 比较节点
当前 `blocked` 的唯一列出依赖。

## 目标与边界

`thm:klartag-density-frontend-identification` 有三条结论。两条等周结论 `h_μ = h_ν^{sm,rel}` 与
`Ψ_KLS(μ) = ψ_ν` 已由 `lem:relative-perimeter-cheeger-infimum` 认证
（`Solutions.LemRelativePerimeterCheegerInfimum.intrinsic`，第 25 个证书）。**未认证的是第三条**，
也是该节点不带 `\leanok` 的唯一原因：`C_P^lit(μ)` 等于使

```
Var_ν(g) ≤ C ∫_V ‖∇g‖² dν
```

对每个局部 Lipschitz 的 `g ∈ L²(ν)`（且 `∫_V ‖∇g‖² dν < ∞`）成立的有限 `C ≥ 0` 的下确界，
`inf ∅ = +∞`，其中 `ν` 是 `V = (affineSupport μ).direction` 上的内蕴律。

内容是检验能量的**梯度**描述。`C_P^lit`（`def:literature-poincare-constant`）是用**局部度量斜率**
`|D f|`（`Energy.LocalSlope.apply`）定义的，不是用 `‖∇g‖`；该子句断言两种描述切出同一个可容许类、
同一个能量，因而同一个最优常数。

**不在范围内**：Buser 半 `Ψ_KLS² ≤ π C_P^lit`（`n ≥ 2` 与常数 π 仍是 imported mathematics，
Mathlib 无 Bakry–Émery 加权热半群、无 Lovász–Simonovits 局部化）；无量纲 KLS。
即便 `Q0` 证出，`thm:logconcave-cheeger-poincare-comparison` **仍不会**标 `\leanok`——
它只是从 `blocked` 里去掉「依赖未认证」这一条。

## 关键发现：这是装配轮，不是分析轮

四个分析步骤**已经全部证出**，在 `Energy/LocalSlope/Gradient.lean`，并已在
`thm:smooth-lipschitz-constant-equivalence` 下认证（该证书的 `#check` 列表里就有这四条）：

| 已证 | 内容 |
| --- | --- |
| `apply_eq_norm_gradient` | 逐点：可微点处斜率等于 `‖∇f(x)‖` |
| `apply_ae_eq_norm_gradient` | Rademacher + `ν ≪ m` ⟹ 局部 Lipschitz 检验的几乎处处恒等 |
| `energy_eq_lintegral_gradient` | 两个扩展能量相等，含 `⊤` |
| `admissible_iff_memLp_gradient` | 既有可容许类**恰好**是 `LocallyLipschitz g ∧ MemLp g 2 ν ∧ MemLp (gradient g) 2 ν` |

缺的只是把这些搬到最优常数上：`Poincare.LocalSlope.Holds` 是用 `Energy.LocalSlope.energy` 写的，
把它改写成梯度形式（`Q1`），再对有效常数取下确界（`Q2`），就得到任意绝对连续律的子句；
`LogConcave.intrinsic_absolutelyContinuous` 为每个有限维对数凹律提供前提，即 `Q0`。

Haar 参考测度沿用 `Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope` 的既定写法：
`m` 是定理的显式参数、带 `[m.IsAddHaarMeasure]`，不是定义的字段，所以**不需要**在 direction 子模上
选定一个测度。这避免了新增定义。

## 义务清单

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `Q1` | `Holds ν C ↔` 梯度形式，`ν ≪ m` | 25 | 低（两条已证引理改写） |
| `Q2` | 下确界相等，任意绝对连续内蕴律 | 20 | 低（`iInf` 沿双射搬运） |
| `Q0` | **目标**：对数凹律的文献 Poincaré 子句 | 10 | 低（代入绝对连续性） |
| `Q3` | 仿射原点无关性 | 0–15 | 低（预计由 `intrinsicMeasure` 的定义直接给出） |

合计约 **55–70 行**。推荐顺序：`Q1`、`Q2`、`Q0`、`Q3`。

`Q3` 是记账项而非分析项：Blueprint 那句「these quantities do not depend on the affine origin `a`」
是关于节点陈述的，而 `Probability.intrinsicMeasure` 本来就不带原点选择。实现轮须**明确记录**
它究竟是由定义直接给出、还是确实需要一条引理——两种结果都要如实写下，不要默认前者。

## 风险

* **唯一实质风险是 `Q1` 的 `iff` 方向性**：`energy_eq_lintegral_gradient` 与
  `admissible_iff_memLp_gradient` 都带 `ν ≪ m` 前提，`Holds` 的量词是对**所有**可容许 `f`，
  所以两边的检验类必须逐字对上。若 `Admissible` 的三个字段与梯度形式的三个前提在 `MemLp` 的
  `AEStronglyMeasurable` 细节上不完全一致，`Q1` 会比估计长。
* 本路线**不**新增任何定义。若实现时发现必须引入 `GradientHolds` 之类的新名字，
  那是对本路线的偏离，须在实现记录里写明理由，并同步 Blueprint 的 `\lean{}` 清单
  （`lake exe checkdecls` 会核对）。
* `Q0` 落地后须更新：Blueprint 该节点加 `\leanok`、`tasks.json` 的 note 与
  `infrastructure.status`、`atlas.py check` 的 evidence 哈希，然后重跑 `research/verify.py`。
  是否新增第 27 个证书由 owner 决定——本子句属于既有节点，不一定要独立证书。

## 验证

路线文件以 `lake env lean -DwarningAsError=true` 通过：**10 个 `#check`，0 错误、0 警告**，
不 import WIP 模块（仓库已无 WIP）。日志
`build/audit/klartag-literature-poincare-route/route-statements.log`。
回执在紧接的实现轮绑定。

## 附记（2026-09-19，实现轮之后）

`Q1`、`Q2`、`Q0` 全部证出（`Poincare/LocalSlope/Gradient.lean`），没有新增定义，路线点名的
`Q1` `iff` 风险没有发生。`Q3` 的结论是**由既有定义直接给出**：`Probability.intrinsicMeasure`
不带原点选择；此外 `Q0` 的陈述里也没有参考测度（Haar 在证明内部构造）。
`thm:klartag-density-frontend-identification` 已标 `\leanok`，
`thm:logconcave-cheeger-poincare-comparison` 由 `blocked` 变为 `inspect_infrastructure`，
但**仍不是**已认证——Buser 半未证。见[实现记录](2026-09-19-klartag-literature-poincare-proofs.md)。
