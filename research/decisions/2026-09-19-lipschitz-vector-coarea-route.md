# Lipschitz 向量 coarea 的路线探查：余维 m coarea 从 `C¹` 推到 Lipschitz

2026-09-19。本轮是**路线探查**，紧随同日的尖锐 Sard 路线轮。**没有证明任何定理**，
没有新增任何库模块，没有修改任何既有 `.lean`。交付物是：缺口的精确定位、
标量侧路线在余维 m 下哪一步现成、哪一步缺、Mathlib 与本仓库的如实检索、
带编号的义务清单（每条配精确 Lean 语句、行数与风险），以及只含 `#check` 的路线语句文件
`research/audits/LipschitzVectorCoareaRouteStatements.lean`。
**命题通过类型检查不是证明**；`L0`、`V1`、`V3`–`V5` **没有一条**在本仓库中被证明。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T114131.124380Z/report.json`（尖锐 Sard 路线轮的最终回执）：
10 个门、224 个本地模块内核重放、617 条目，快照 `cfd1dab59526eeca9f0584e76825a1d545bde07dd70c38709b2a0235a649f482`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard（同日已另立路线）、Energy 的五个洞、无量纲 KLS 也都未触碰。
本路线只到**整体 Lipschitz**（`LipschitzWith K u`）；局部 Lipschitz 版本 `M2` 明确不在本路线内。

## 一、缺口

`Analysis/RankDeficient/Coarea.lean` 的 `coarea_of_contDiff`（`R9`）是余维 m coarea 公式，
对临界集无任何假设，但要求 **`C¹`**。Federer 的 coarea 公式对**仅 Lipschitz** 的映射就成立；
标量侧早已走完 `C¹ → Lipschitz → 局部 Lipschitz`
（`KLS/Geometry/{SmoothCoarea,LipschitzCoarea,LocallyLipschitzCoarea}.lean`）。
**向量侧停在 `C¹`**——这就是目标 `L0`：把 `coarea_of_contDiff` 的 `ContDiff ℝ 1 u` 换成
`LipschitzWith K u`，其余逐字不变。密度仍写 `coareaJacobian (fderiv ℝ u x)`：
`fderiv` 在不可微点是垃圾值，而按 Rademacher 那是 Lebesgue 零测集，与标量 `L12` 用 `gradient` 的约定相同。

## 二、标量侧怎么走的，以及余维 m 下哪一步缺

`KLS.coarea_of_lipschitz`（`L12`）分三步：

1. `Analysis.exists_contDiff_pieces`（`L7`）把定义域切成可数个不交可测片，每片上有一个 `C¹`
   函数与 `u` **一阶吻合**（值与导数都相等），补集 Lebesgue 零测；
2. 每片上用 `C¹` 公式，一阶吻合使密度与切片都吻合；
3. 可数可加求和，零测补集由「零测集在几乎每个水平上切片零测」删掉。

余维 m 下**后两步现成**：第 2 步是 `coarea_of_contDiff`；第 3 步是
`Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`——取 `d = k`，其假设
`μH[k + m] N = 0` 在 `k + m = n` 下经 `Analysis.hausdorffMeasure_finrank_eq_smul_volume` 正是
「`N` Lebesgue 零测」（`V2`；约十行的推导，本轮**未落库**，只按类型确认可导出）。
**第 1 步没有**：`L7` 背后整条 jet 与 Whitney 链条（`LipschitzJet.exists_compact_jets`、
`WhitneyJet.exists_contDiff_extension`、`exists_contDiff_pieces`）一律写着 `u : V → ℝ`，
向量层里没有任何东西顶替它们。**`V1`（向量 `C¹` 分片）是唯一真正新的成分。**

## 三、`V1` 怎么办：逐分量，而不是把 Whitney 扩张做成向量靶

取线性等距 `e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)`（`isometryEquivOfFinrankEq` 一线已在仓库中）。
`u` 的每个坐标 `fun y => e (u y) i` 是标量 `K`-Lipschitz 函数（`V4'`），各自套用**已证的** `L7`
得到自己的可数分割；`V3` 取这 `m` 个分割的可数公共加细（`ℕ^m` 可数，仍以 `ℕ` 编号，
补集含于 `m` 个零测集之并）；在公共片上所有坐标同时与各自的 `C¹` 标量代表一阶吻合，
`V4''` 由坐标可微得 `u` 可微，`V4` 把逐坐标吻合升级为 `u` 与 `e.symm ∘ (代表)` 的向量一阶吻合。
于是 `V1` 不需要新的分析，只需要记账加微积分；`V5` 是标量 `L12` 装配的余维 m 逐字翻版，
写成「由 `V1` 的结论推出 `L0`」的蕴涵，使 `L0 = V5 ∘ V1`。

**这是本轮最实质的判断，也是它可能错的地方**：若 `V3` 的公共加细在可测性或不交性上比预想麻烦，
或 `V4` 在 `fderiv` 的分量化上遇到 Mathlib 缺口（`fderiv` 与 `e`、坐标投影的复合），
`V1` 就要退回「把 Whitney 扩张做成向量靶」的重路线。本轮没有验证 `V3`、`V4`。

## 四、Mathlib 与本仓库有什么、缺什么

**Mathlib**：有 Rademacher（`LipschitzWith.ae_differentiableAt`）、`differentiableAt_pi`、
`fderiv_pi` 一线、`LinearIsometryEquiv` 的微分性质；**没有任何 coarea 公式**。
**本仓库**：`L7`（实值）、`coarea_of_contDiff`（`C¹`，余维 m）、余维 m 零切片
`ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`（已是 `V2` 需要的形状）、
无正则性的切片可测性、`isometryEquivOfFinrankEq`。**缺的**：`V1`、`V3`、`V4`、`V4'`、`V4''`、`V5`、`L0`。

## 五、义务清单

精确 Lean 语句在 `research/audits/LipschitzVectorCoareaRouteStatements.lean`，按本表编号排列；
该文件只含 `#check`（5 条引用已证声明，10 条义务/诊断），无声明、无证明、无占位公理，
以 `-DwarningAsError=true` 通过。**通过类型检查不是证明。**

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `L0` | **目标**：`coarea_of_contDiff` 的 `ContDiff ℝ 1` 换成 `LipschitzWith K` | — | 由 `V1`+`V5` 合成 |
| `V1` | 向量 `C¹` 分片（`L7` 的向量版） | 80 | 中（由 `V3`+`V4`+`V4'`+`V4''` 合成） |
| `V2` | Lebesgue 零测补集在几乎每个水平上 `hausdorffNormalized k` 零测 | 15 | 低（已确认可导出） |
| `V3` | 有限多个可数分割的可数公共加细 | 80 | 中（记账） |
| `V4'` | Lipschitz 映射的坐标是 Lipschitz | 15 | 低 |
| `V4''` | 坐标可微 ⟹ 可微 | 20 | 低 |
| `V4` | 逐坐标一阶吻合 ⟹ 向量一阶吻合 | 60 | 中（`fderiv` 分量化） |
| `V5` | 装配：沿分片可数可加（照抄标量 `L12`） | 150 | 中 |
| `M1` | 诊断：Lipschitz 不蕴含 `C¹` | — | 不是步骤 |
| `M2` | 后续：局部 Lipschitz 版本，**明确不属于本路线** | — | 范围界定 |

合计约 **420 行**。推荐顺序：`V4'`、`V4''`、`V4`、`V3`、`V1`、`V2`、`V5`、`L0`。
没有单点判据：`V3`、`V4` 都是可绕开的记账；真正的分析（`L7`、`R9`、零切片）都已证。

## 六、明确没证什么

* **本轮没有证明任何定理。** `L0`、`V1`–`V5` 均未证；`V2` 未落库。
* 局部 Lipschitz 版本 `M2` 不在本路线内；向量值 Sard、临界值测度、Whitney 反例都不在本路线内。
* Cheeger 两洞归王浩丞，Energy 五洞、尖锐 Sard 未触碰；无量纲 KLS 仍开。

## 七、验证

`research/audits/LipschitzVectorCoareaRouteStatements.lean` 以 `lake env lean -DwarningAsError=true` 通过，
15 个 `#check`，0 错误、0 警告，日志 `build/audit/lipschitz-vector-coarea-route/route-statements.log`；
本地 import 闭包不含 WIP 文件。未修改任何库源码、未改聚合导入。
根目录 `python3 research/verify.py` 于本轮结束时重跑，最终回执记于
`build/audit/lipschitz-vector-coarea-route/final-snapshot.json`，快照与工作区逐条重算，drift 为空。
详见 `research/explorations/2026-09-19-lipschitz-vector-coarea-route.json`。

## 附记（2026-09-19，实现轮之后）

`L0`、`V1`–`V5`、`V4'`、`V4''`、`M1` 全部证出（`Analysis/Lipschitz/{Componentwise,Refinement,VectorPieces,VectorCoarea}.lean`），
`L0 = V5 ∘ V1` 如路线所计划；`V3` 用的是单射 `(Fin m → ℕ) ↪ ℕ` 而非等价（`m = 0` 时 `Fin 0 → ℕ` 是单点）。
范围外的 `M2` 也随局部 Lipschitz 路线一并证出（`N0 = X5 ∘ L0`）。见 [实现记录](2026-09-19-coarea-sard-proofs.md)。
