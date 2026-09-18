# Cheeger 下确界两洞的路线探查：接手学长的 Cheeger 线

2026-09-19。Owner 指示：**学长那个我们接手了**——原属王浩丞的对数凹 Cheeger 线（`KLS/WIP/CheegerInfimum.lean`
的两个洞、`lem:relative-perimeter-cheeger-infimum`、`thm:logconcave-cheeger-poincare-comparison`）由本会话接手。
本轮是**路线探查**，**没有证明任何定理**，没有改动任何既有 `.lean`；交付物是只含 `#check` 的路线语句文件
`research/audits/CheegerInfimumRouteStatements.lean`（14 条义务/迁移目标命题 + 8 条已证声明引用）。
**命题通过类型检查不是证明。** 直接洞仍 **7（0/2/5）**，证书仍 **24**。不提交、不推送。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T132358.171383Z/report.json`（同日实现轮的最终回执）：10 个门、234 个本地模块内核重放、
638 条目，快照 `d9cd7067e18cbebc3408d8e772fc539392533db8be44e91419f2bba370a7226a`。drift 为空。

## 两个洞

`K0` `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`：光滑 Lipschitz `[0,1]` 值 `u`，
`h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`；`K5` `Isoperimetry.smoothConstant_le_minkowskiConstant`：`h_S ≤ h_M`。
连同已证的 `h_M ≤ h_S`（`KLS/Geometry/CheegerInfimum.lean`）给出 `lem:relative-perimeter-cheeger-infimum`（`K10`）
与 `thm:klartag-density-frontend-identification` 的两条等周子句（`K12`、`K13`），并使三条内禀传输脱离 `sorryAx`。

## 路线

**`K0`**：几乎每个 `t` 的严格超水平集是光滑域（`SmoothDomain.ae_exists_superlevel`，光滑 Sard，`K3`），
其边界含于水平集（`frontier_superlevel_subset`），故相对周长 ≤ 密度在水平集上的积分（`K2`）；
乘积形式的下确界界 `h_S · m(ν U) ≤ P_ρ(U)` 对每个光滑域成立，零质量与满质量由 `⊤ · 0 = 0` 收尾（`K1`）；
对 `t` 积分后用密度的加权 `C¹` coarea 公式（`K4`，由已证的 `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
取权 `ofReal ∘ ρ`、`ν = volume.withDensity`）得 `∫ ‖∇u‖ dν`。不需要 `t ↦ ∫_{u=t} ρ` 可测（`lintegral_mono_ae` 不要求）。

**`K5`**：取中间质量、Minkowski 含量有限的 Borel 集 `B`（于是 `ν(closure B) = ν B`）。距离截断 `w_r` 的梯度积分
`≤ (ν(B^r) − ν B)/r`（已证，`K6`），与 `𝟙_B` 的 `L¹` 距离 `≤ ν(B^r) − ν B`（`K7`）；磨光替身（`K9`，WIP 中已证）
满足 `K0`；平衡量对集合 1-Lipschitz：`m(ν B) ≤ ∫₀¹ m(ν{u > t}) dt + ‖u − 𝟙_B‖₁`（`K8`，由已证的
`lintegral_measure_symmDiff_superlevel` 与 `min_measure_le_add_measure_symmDiff`）。**把误差从平衡量里减掉而不是乘进 `h_S`**：
`h_S · (m(ν B) − e_r) ≤ q(r)`，于是不需要 `h_S` 有限；先让磨光指标趋于无穷，再沿 `r → 0⁺` 取 `liminf`——那就是 Minkowski 含量。

## 义务清单

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `K0` | **洞一**：光滑 coarea 界 | 60 | 低（`K1`–`K4` 合成） |
| `K1` | 乘积形式的下确界界，对所有光滑域 | 30 | 低 |
| `K2` | 超水平域的相对周长 ≤ 水平集积分 | 20 | 低 |
| `K3` | 几乎每个超水平集是光滑域 | — | **已证** |
| `K4` | 密度的加权 `C¹` coarea | 20 | 低 |
| `K5` | **洞二**：`h_S ≤ h_M` | 120 | 中（极限次序与 `⊤` 的处理） |
| `K6` | 距离截断的梯度积分 | — | **已证** |
| `K7` | 距离截断到指示函数的 `L¹` 距离 | 30 | 低 |
| `K8` | 平衡量 1-Lipschitz | 30 | 低 |
| `K9` | 磨光替身 | — | WIP 中已证，随迁移搬入 |
| `K10`–`K13` | 等式与三条内禀传输 | — | WIP 中已证（模两洞），随迁移搬入 |

合计约 **300 行**新证明，加上从 WIP 迁入的约 200 行。推荐顺序：`K1`、`K2`、`K4`、`K0`、`K7`、`K8`、`K5`。
证出后按先例迁移：新模块 `KLS/Geometry/CheegerEquality.lean` 承载 WIP 的全部七条公开声明（`pp.all` 逐字节比对），
删除 WIP，注册 `lem:relative-perimeter-cheeger-infimum` 为第 25 个证书。

## 边界

Energy 的五个洞、无量纲 KLS 未触碰。Cheeger–Buser 比较 `thm:logconcave-cheeger-poincare-comparison` 另立路线。
`research/tasks.json` 中 `lem:relative-perimeter-cheeger-infimum` 的 `gaps` 正是 `K0` 与 `K5`；本轮不改它。

## 验证

路线文件以 `lake env lean -DwarningAsError=true` 通过，22 个 `#check`，0 错误、0 警告，不 import WIP；
日志 `build/audit/cheeger-infimum-route/route-statements.log`。本轮不重跑 `verify.py`：同日的实现轮紧接其后，
回执在那一轮绑定。

## 附记（2026-09-19，实现轮之后）

* **`K7` 按字面为假。** `B = ∅` 时 Mathlib 的 `Metric.infDist x ∅ = 0` 使 `distanceCutoff ∅ r ≡ 1`，而
  `Metric.thickening r ∅ = ∅`，命题读作 `1 ≤ 0`。证明会话在审计里用 `EuclideanSpace ℝ (Fin 1)` 上的 Dirac 律
  证明了逐字形式为假（`route_K7_empty_counterexample`），并证明加 `B.Nonempty` 的版本（`route_K7`）；
  `K5` 只对正质量的集合用它，下游不受影响。路线语句文件保持字节不变。
* 其余 `K0`–`K6`、`K8`–`K13` 全部证出或迁入 `KLS/Geometry/CheegerEquality.lean`，七条公开声明 `pp.all` 逐字节相同
  （2223 行 `diff` 为空）。见 [实现记录](2026-09-19-cheeger-line-proofs.md)。
