# 非线性面积公式路线探查

2026-09-16。本轮只做路线探查：**没有证明新定理，没有修改任何 `.lean` 库源码**，
不迁洞、不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。
新增文件只有本决定、一个**只含 `#check`** 的语句文件和证据 JSON。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T132852.139911Z/report.json`：10 个门、202 个本地模块内核重放、
518 条目，快照 `8b8056f523c6324ccac139eb21d90c844d27d3ecb068625966e8c2f3c970bc52`。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮未触碰。

## 判断与建议

**目标 A0**（单射 C¹ 参数化的 Federer 面积公式）**在当前库上不是一轮能完成的**，
而且走教科书的一般路线会撞上一处确切障碍。**建议改走图路线 B1**，
即先证余维 m 的**图**面积公式，再由局部图化归到一般情形。

理由是仓库已经用图路线走通过余维一，工具链齐备，而一般路线缺的正是 Mathlib 不提供的那块。

## 障碍定位（一般路线甲）

教科书路线是：用 `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 把定义域分成
可数片，每片上 `g` 与某个固定线性 `A` 相差 ε，再对 `A` 两侧夹逼。分片引理在 Mathlib
**存在且形状正好**，还保证每个 `A n` 确实是某点的微分。

**确切障碍在夹逼的下界。** Mathlib 的 `ApproximatesLinearOn.antilipschitz` 签名要求线性模型
是 `f' : E ≃L[𝕜] F`，即**连续线性等价**，也就是**同维**。降维时 `fderiv g y : H →L V` 单射
但不是等价，该引理**用不上**。可用的替代是
`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`，但它只给
`∃ K, AntilipschitzWith K f`，常数由 `Classical.choose` 取得，**不具备**夹逼所需的
「常数随 ε 趋于 `normDet A` 的倒数」这种定量控制。补齐这一步要自己做
「经值域分解 `A = incl ∘ A₀`、把 `g` 投到 `range A` 上、再控制正交分量」的论证，
这正是 A3，估计 250–500 行，风险高。

Mathlib **没有**任何降维的面积公式（全库检索 “area formula” 无命中），
也**没有** `normDet` 的连续性，所以被积函数的可测性 A1 也是真义务。

## 为什么图路线更可行

图映射 `y ↦ ι y + κ (γ y)` 有两条一般情形没有的好性质：

1. **天然单射**，不需要 `InjOn` 假设，也不需要处理重数；
2. **有显式左逆**：参数投影 `ιᵀ` 满足 `ιᵀ ∘ graphMap = id`，
   于是 A3 缺的那个定量下界可以直接算出来，不必经 `Classical.choose`。

体积因子本轮之前已经备好：`Analysis.normDet_graphMapLinear` 给出
`√det (1 + Aᵀ A)`，且 `Analysis.normDet_graphLinear` 已证它在余维一退回仓库原有的
`graphJacobian`。纤维测度的归一化记账由 `KLS.hausdorffNormalized_fiber` 给出。

**成本锚点**：仓库证余维一图面积公式用了 `Analysis/AreaFormula.lean` **957 行**，
配套 `Analysis/ImplicitGraph.lean` **859 行**。余维 m 的类比不会更便宜。

## 所需引理清单

行数为**新增 Lean 证明的大致行数**，不含重用模块，不是完成承诺。
精确 Lean 语句全部在 `research/audits/AreaFormulaRouteStatements.lean`，
该文件**只有 `#check`**，无声明、无证明、无占位公理，以 `-DwarningAsError=true` 编译通过。

| 编号 | 内容 | Mathlib 是否已有 | 估计行数 | 风险 |
|---|---|---|---:|---|
| A0 | 目标：单射 C¹ 参数化的面积公式 | **无** | — | — |
| A1 | `normDet` 连续，故被积函数可测 | **无**（`measurable_fderiv` 有） | 60–120 | 中 |
| A2 | 像一侧的可数可加性（需 `InjOn` 与像的可测性） | 无 | 80–160 | 中 |
| A3 | 对**单射**线性模型的两侧夹逼 | **无**；`ApproximatesLinearOn.antilipschitz` 要求同维等价，用不上 | 250–500 | **高** |
| A4 | 微分非单射部分的像零测 | 无 | 100–200 | 中 |
| A5 | 局部面积公式拼成整体 | 无 | 80–160 | 中 |
| B1 | **余维 m 图面积公式**（推荐主攻） | 无；余维一版本仓库已证，可作模板 | 600–1000 | 高 |
| B2 | B1 的 `hausdorffNormalized` 归一化版本 | 无；常数消去模式本轮已有 | 20–40 | 低 |

走 B 路线仍需 A1、A2、A5；A3、A4 则可望避开或大幅简化——图映射的左逆显式，
且图映射的微分恒为单射，所以 A4 在 B 路线下不出现。

## 分阶段建议

1. **A1 + B2 的准备**：`normDet` 连续性与可测性，纯代数/拓扑，先行且低风险。
2. **B1 主攻**：照 `Analysis/AreaFormula.lean` 的结构做余维 m 版本，预计 2–3 轮。
3. **A5 + A2**：局部到整体的拼接与像侧可加性。
4. 之后才回到余维 m coarea 的正则情形。

**不建议**现在去补 A3。它是一般路线的关键缺口，但 B 路线可以绕开；
若将来确实需要一般单射 C¹ 映射的面积公式，再单独立项。

## 本轮明确没有做的事

* **没有证明任何定理**，也没有把上述任何一条标为已完成。
* 没有修改任何 `.lean` 库源码；`research/audits/AreaFormulaRouteStatements.lean` 是
  **只含 `#check`** 的新文件，不是证明。
* 没有迁洞，没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 验证

* `research/audits/AreaFormulaRouteStatements.lean` 以 `-DwarningAsError=true` 编译通过，
  九条命题全部通过类型检查；新增结果的公理审计为空（**本轮没有新增结果**），
  不是「已证面积公式」。
* 重跑全部 29 个审计客户端（`research/audits` 22 个，`build/audit` 7 个），全部严格通过，
  未作任何修改。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-area-formula-route.json`，最终核对另存
  `build/audit/area-formula-route/final-snapshot.json`。
