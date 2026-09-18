# 局部 Lipschitz 向量 coarea 的路线探查：向量链的最后一步

2026-09-19。本轮是**路线探查**，紧随同日的 Lipschitz 向量 coarea 路线轮，目标是那一轮划在范围外的
`M2`——此处记为 `N0`：余维 m coarea 公式在**局部 Lipschitz** 假设下成立，无全局常数、无全局模数。
**没有证明任何定理**，没有新增任何库模块，没有修改任何既有 `.lean`。交付物是：
标量 `L13` 的归约在余维 m 下逐步核对、唯一要换的成分（向量 Lipschitz 扩张）及其无需 Kirszbraun 的做法、
带编号的义务清单，以及只含 `#check` 的路线语句文件
`research/audits/LocallyLipschitzVectorCoareaRouteStatements.lean`。
**命题通过类型检查不是证明**；`N0`、`X1`、`X3`–`X5` **没有一条**在本仓库中被证明。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T115012.397782Z/report.json`（Lipschitz 向量 coarea 路线轮的最终回执）：
10 个门、224 个本地模块内核重放、620 条目，快照 `4793a31700897b94edbb049599ccbc7f2b2dc0feb9fbd58af850eeca63ab5352`。起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，本轮未触碰。
尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。定义域不推广到开子集或流形。

## 一、位置

`R9`（`C¹`，已证）→ `L0`（整体 Lipschitz，同日路线，未证）→ `N0`（局部 Lipschitz，本路线）。
标量侧对应 `L11 → L12 → L13`，`L13` 即 `KLS.coarea_of_locallyLipschitz`，已证。`N0` 是 `L0` 与 `R9` 的共同推广：
整体 Lipschitz 与 `C¹` 都蕴含局部 Lipschitz（`C1`、`C2`）。

## 二、标量 `L13` 的归约，逐步核对

`L13` 用半开环带 `A k = ball 0 (k+1) \ ball 0 k` 归约到 `L12`：
(1) `u` 在闭球上 Lipschitz（`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`）；
(2) McShane 扩张 `LipschitzOnWith.extend_real` 给出全局 Lipschitz 的 `v k`，在闭球上等于 `u`；
(3) 片 `S ∩ A k` 含于开球，`u = v k` 于每点邻域，故梯度与水平集在片上一致；
(4) 对 `v k` 用 `L12`；(5) `lintegral_iUnion`、`lintegral_tsum`、`AEMeasurable.tsum` 可数求和。

余维 m 下 (1)、(3)、(4)、(5) 逐字照搬：(1) 与靶无关（`X2`）；(3) 用 `Filter.EventuallyEq.fderiv_eq`
代替 `gradient_eq`，密度 `coareaJacobian (fderiv ℝ u x)` 随之一致（`X4`）；(4) 用 `L0`；(5) 相同（`X3` 记账）。
**只有 (2) 要换**：`extend_real` 是标量的，Kirszbraun 不在 Mathlib。但 `L0` 只要求**存在某个**常数，
所以逐坐标 McShane 就够：经线性等距到 `EuclideanSpace ℝ (Fin m)`、`WithLp.ofLp` 到 sup 范数的 `Fin m → ℝ`，
套 Mathlib 的 `LipschitzOnWith.extend_pi`，再经 `WithLp.toLp`（常数 `√m`）与 `e.symm` 回到 `W`（`X1`）。
这是记账，不是分析，对常数不作任何声称。

`X5` 把这五步写成一条蕴涵：**由 `L0` 推出 `N0`**。于是 `N0 = X5 ∘ L0`，向量链
`C¹ → Lipschitz → 局部 Lipschitz` 在 `L0` 证出的那一刻整体闭合。

## 三、Mathlib 与本仓库有什么

**Mathlib**：`LipschitzOnWith.extend_pi`、`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`、
`Filter.EventuallyEq.fderiv_eq`、`PiLp` 的 Lipschitz 等价、`lintegral_iUnion`/`lintegral_tsum`；
**没有** Kirszbraun、没有 coarea。**本仓库**：`L13`（模板）、`R9`。**缺的**：`X1`、`X3`、`X4`、`X5`、`N0`；`L0` 另有路线。

## 四、义务清单

精确 Lean 语句在 `research/audits/LocallyLipschitzVectorCoareaRouteStatements.lean`（2 条引用已证声明，9 条义务/诊断/一致性），
无声明、无证明、无占位公理，以 `-DwarningAsError=true` 通过。**通过类型检查不是证明。**

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `N0` | **目标**：`coarea_of_contDiff` 的 `ContDiff ℝ 1` 换成 `LocallyLipschitz` | — | `X5` 用于 `L0` |
| `X1` | 向量 Lipschitz 扩张，常数存在量化（逐坐标 McShane，非 Kirszbraun） | 40 | 低（`PiLp` 常数搬运） |
| `X2` | 局部 Lipschitz ⟹ 每个闭球上 Lipschitz | 10 | 低（Mathlib 直接给） |
| `X3` | 半开环带：可测、两两不交、覆盖、含于开球邻域 | 40 | 低（照抄 `L13`） |
| `X4` | 开集上相等 ⟹ 片上 `fderiv` 一致、水平集一致 | 20 | 低 |
| `X5` | 装配：`L0 ⟹ N0`（照抄 `L13`） | 120 | 中 |
| `D1` | 诊断：平面上 `x ↦ ‖x‖² e₀ + ‖x‖ e₁` 局部 Lipschitz、不全局 Lipschitz、在 0 不可微 | 60 | 不是步骤 |
| `C1`, `C2` | 一致性：整体 Lipschitz、`C¹` 都局部 Lipschitz | 5 | 不是步骤 |

合计约 **230 行**（不含 `L0` 自身）。推荐顺序：`X2`、`X3`、`X4`、`X1`、`X5`；`N0` 在 `L0` 之后立即得到。
没有单点判据：所有分析都已在 `L13` 与 `R9` 中完成。

## 五、明确没证什么

* **本轮没有证明任何定理。** `N0`、`X1`–`X5` 均未证；`L0` 仍开。
* 不是 Sard 定理；`X1` 的常数无最优性；定义域不推广。
* Cheeger 两洞归王浩丞，Energy 五洞、尖锐 Sard 未触碰；无量纲 KLS 仍开。

## 六、验证

路线文件以 `lake env lean -DwarningAsError=true` 通过，11 个 `#check`，0 错误、0 警告，
日志 `build/audit/locally-lipschitz-vector-coarea-route/route-statements.log`；本地 import 闭包不含 WIP 文件。
未修改任何库源码、未改聚合导入。根目录 `python3 research/verify.py` 于本轮结束时重跑，最终回执记于
`build/audit/locally-lipschitz-vector-coarea-route/final-snapshot.json`，快照与工作区逐条重算，drift 为空。
详见 `research/explorations/2026-09-19-locally-lipschitz-vector-coarea-route.json`。

## 附记（2026-09-19，实现轮之后）

`X1`–`X5`、`D1`、`C1`、`C2` 全部证出（`Analysis/Lipschitz/{Extension,Annuli,Local}.lean`），`L0` 同日证出，
于是 `N0 = X5 ∘ L0` 即 `Analysis.coarea_of_locallyLipschitz`。见 [实现记录](2026-09-19-coarea-sard-proofs.md)。
