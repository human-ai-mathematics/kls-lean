# Cheeger 不等式 `C_P^lit ≤ 4Ψ²` 的路线探查：Cheeger–Buser 的 Cheeger 半

2026-09-19。接手 Cheeger 线后的第二条路线（第一条见[两洞路线](2026-09-19-cheeger-infimum-route.md)）。
本轮是**路线探查**，**没有证明任何定理**，没有改动任何既有 `.lean`；交付物是只含 `#check` 的路线语句文件
`research/audits/CheegerInequalityRouteStatements.lean`（9 条命题 + 5 条已证声明引用）。**命题通过类型检查不是证明。**
直接洞仍 **7（0/2/5）**，证书仍 **24**。不提交、不推送。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T132358.171383Z/report.json`：10 个门、234 个模块重放、638 条目，快照 `d9cd7067e18cbebc3408d8e772fc539392533db8be44e91419f2bba370a7226a`。

## 目标与边界

`thm:logconcave-cheeger-poincare-comparison` 的 **Cheeger 半**（`P0`）：对每个有限维对数凹律 `μ`，
`C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`，其中 `C_P^lit` 是 `def:literature-poincare-constant` 的内禀局部斜率 Poincaré 常数
（`Poincare.LocalSlope.Intrinsic.constant`），`Ψ_KLS = h_μ⁻¹`（`Isoperimetry.inverseScale`）；Dirac 律两侧皆 `0`。
**Buser 半** `Ψ_KLS(μ)² ≤ π C_P^lit(μ)`（`B1`）**不在本路线内**：对数凹律的已知证明都用加权热半群的 Bakry–Émery 梯度界
（Ledoux；De Ponti–Mondino 给常数 `π`）或 Lovász–Simonovits 局部化，Mathlib 与本仓库都没有。该节点因此**不会**标 `\leanok`。
Energy 五洞、无量纲 KLS 未触碰。

## 路线

在坐标空间对任意 Borel 概率律 `ν` 与其 Minkowski 常数 `h_M` 工作，最后搬运到对数凹律。中位数存在（`P2`）。
对有界 `C¹` Lipschitz 的 `g`，`Var(g) ≤ ∫ (g−m)²`，拆成 `(g−m)₊²` 与 `(m−g)₊²`。每一个 `v = (g−m)₊²` 是 `C¹`
（`t ↦ max t 0 ^ 2` 是 `C¹`）、Lipschitz、支在质量 ≤ 1/2 的 `{g > m}` 上，于是每个超水平集上平衡量就是质量本身，
层饼公式 + `minkowskiConstant_mul_min_le` + Minkowski coarea 不等式 `lintegral_minkowskiContent_superlevel_le`
给出 **`L¹` Cheeger 不等式** `h_M ∫ v ≤ ∫ ‖∇v‖`（`P3`）；链式法则 `∇v = 2(g−m)₊∇g` 与 Cauchy–Schwarz 给
`h_M² ∫ (g−m)₊² ≤ 4 ∫_{g>m} ‖∇g‖²`（`P4`），两半相加得 `h_M² Var(g) ≤ 4 ∫ ‖∇g‖²`（`P5`）。一般光滑测试用光滑 bump 截断：
截断有界且 Lipschitz，其方差与梯度能量收敛到原测试的（`P6`），于是 `C_P^smooth(ν) ≤ 4/h_M²`（`P1`；`h_M = 0` 时右侧 `⊤`）。
最后由文献常数与内禀律光滑测试常数的识别（`Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope`，
对数凹律有所需的绝对连续性）与 `h_μ = h_M(ν)`（两洞路线的 `K11`）把 `P1` 搬运成 `P0`。

## 义务清单

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `P0` | **目标**：`C_P^lit(μ) ≤ 4Ψ_KLS(μ)²` | 15 | 低（搬运，需 `K11`） |
| `P1` | `C_P^smooth(ν) ≤ 4/h_M²`，任意 Borel 律 | 40 | 低（`Holds` 与 `toReal` 记账） |
| `P2` | 中位数存在 | 60 | 低 |
| `P3` | `L¹` Cheeger：非负、半质量 | 60 | 中（层饼 + 两条 Minkowski 引理） |
| `P4` | 正部平方：`h_M² ∫(g−m)₊² ≤ 4∫_{g>m}‖∇g‖²` | 120 | 中（链式法则、Hölder 的 `ℝ≥0∞` 代数） |
| `P5` | 有界 `C¹` Lipschitz 的 Cheeger 不等式 | 80 | 低–中 |
| `P6` | 截断延拓到全部可容许光滑测试 | 200 | **中–高**（控制收敛、`scaled R` 的 Lipschitz 与梯度） |
| `D1` | `h_M = ⊤ ⟹ C_P^smooth = 0` | 5 | 不是步骤 |
| `B1` | Buser 半，明确范围外 | — | 范围界定 |

合计约 **600 行**。推荐顺序：`P2`、`P3`、`P4`、`P5`、`P6`、`P1`，`P0` 在两洞路线的 `K11` 迁入无洞模块后合成。
`P6` 是唯一可能拖长的项；若截断的收敛论证过重，可退而只对有界 Lipschitz 测试陈述（那就**不是** `P1`），如实记录。

## 验证

路线文件以 `lake env lean -DwarningAsError=true` 通过，14 个 `#check`，0 错误、0 警告，不 import WIP；
日志 `build/audit/cheeger-inequality-route/route-statements.log`。回执在紧接的实现轮绑定。

## 附记（2026-09-19，实现轮之后）

`P1`–`P6`、`D1` 全部证出（`KLS/Geometry/Median.lean`、`KLS/Geometry/CheegerInequality.lean`），`P6` 复用了仓库既有的光滑截断
`Energy.Euclidean.LipschitzApproximation.scaled`；`P0` 在 `K11` 迁入 `CheegerEquality.lean` 后于整合时合成
（`LogConcave.literatureConstant_le_four_mul_inverseScale_sq`）。`B1` 未证。见 [实现记录](2026-09-19-cheeger-line-proofs.md)。
