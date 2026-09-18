# Buser 半阶段一证毕：一维、常数 12

2026-09-19，**实现轮**，紧随同日的 [Buser 路线探查](2026-09-19-buser-route.md)。一个证明会话证出阶段一的全部义务
`Q0`、`Q0'`、`Q1`、`Q1'`、`Q2`–`Q5`（与 `D1`），本会话整合。结果：对直线上的对数凹律 `Ψ² ≤ 12·C_P^smooth(ν)`
（`KLS.LogConcave.inv_minkowskiConstant_sq_le`），并经搬运得到 **仿射支撑维数 `≤ 1` 的每个对数凹律满足
`Ψ_KLS(μ)² ≤ 12·C_P^lit(μ)`**（`LogConcave.inverseScale_sq_le_of_finrank_le_one`）。
**`B0`（任意维、常数 `π`）未证**；Blueprint 节点 `thm:logconcave-cheeger-poincare-comparison` 不标 `\leanok`，只加 `\lean{}` 与说明。
直接洞 **0**，证书 **26**，不变。不提交、不推送。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T151845.800831Z/report.json`：10 个门、241 个模块重放、662 条目，快照 `1fc50cd6d74a2b42f74600fc30b5b245316a9d58d53e034f05cd56f2a033606d`。

## 新模块与兑现

| 模块（行） | 内容 |
| --- | --- |
| `KLS/LogConcave/Line/Isoperimetry.lean`（450，14 条公开声明） | `Q1'` `LineDensity.mul_min_le_relativePerimeter`、`Q1` `LineDensity.two_mul_le_minkowskiConstant`、`Q2` `LineDensity.le_two_mul`、`Q3` `LineDensity.one_div_le_evariance`、`LineDensity.interior_support_nonempty` |
| `KLS/LogConcave/Line/Buser.lean`（371，10 条公开声明） | `Q4` `KLS.evariance_le_smoothTest_constant`；等距搬运 `Isoperimetry.minkowskiConstant_map`、`nonempty_linearIsometryEquiv_real`；退化情形 `exists_support_eq_singleton`、`minkowskiConstant_eq_top_of_interior_empty`；`Q0` `LogConcave.inv_minkowskiConstant_sq_le`；`Q0'` `LogConcave.inverseScale_sq_le_of_finrank_le_one` |
| `research/audits/BuserLineAudit.lean`（195） | `route_Q0`…`route_Q5`、`route_D1` 逐字兑现；边界：`Q0'` 的零维（逆尺度为 0）、`ℝ` 上的 Dirac 律（`h_M = ⊤`）；36 条公理报告全标准 |

`Q5` 用的是已有的 `LogConcave.memLp_id_two`；`D1` 是 `Real.pi_le_four` 加 `linarith`。

## 两处与路线记录不同的证法（语句逐字不变）

* **`Q1'` 不需要边界离散与分支枚举**（路线为此预算 300 行）：`surfaceMeasure ℝ = μH[0]` 把边界积分从下方用**一个**边界点的 `ρ` 控制；
  对含中位数 `m` 的**任意**开集 `W`，`a = sSup (Iio m \ W)`、`b = sInf (Ioi m \ W)` 是边界点且 `Wᶜ ⊆ Iic a ∪ Ici b`，
  hazard 界直接给 `2ρ(m)·ν(Wᶜ) ≤ ρ(a) + ρ(b)`。按中位数在域内 / 在边界 / 在闭包外三分；边界情形只需 `ρ(m)`，因为 `2·min(p, 1−p) ≤ 1`。
  光滑性与 `ν(∂U) = 0` 全程未用。
* **`Q3` 由已认证的中位数方差界导出，不是 bathtub 重排**：路线语句对 `d : LineDensity ν` 量化，而它已带对数凹 Borell 密度，
  于是 `d.logConcave` + `interior_support_nonempty` + `Line/Variance.lean` 的 `one_div_le_variance` + `ρ(m) ≤ M` 即得。
  覆盖非对数凹有界密度的重排证明**没有写**。

## 明确没证什么

`B0`：任意维的 Buser 半、常数 `π`——阶段二（半群 + Bakry–Émery，或局部化 + 转移）未开始。无量纲 KLS 仍开。
指数律上 `Q2` 取等的情形未形式化（仓库没有带 `LineDensity` 的指数律）。

## 验证

默认 `lake build`（3514 个作业）通过。全部 **68** 个审计客户端（`research/audits` 61 个 + `build/audit` 7 个活客户端）以 `-DwarningAsError=true` 重跑，**0 失败**；**903 条公理报告，0 条 `sorryAx`**。`check_ledger.py` **26** 个证书 0 错误；`check_blueprint.py` 88 标签 0 错误；`atlas.py check` 75 节点 26 证书无环；104 项单元测试通过。
根目录 `python3 research/verify.py` 于本轮结束时重跑，最终回执记于 `build/audit/buser-line-proofs/final-snapshot.json`，
快照与工作区逐条重算，drift 为空。详见 `research/explorations/2026-09-19-buser-line-proofs.json`。
