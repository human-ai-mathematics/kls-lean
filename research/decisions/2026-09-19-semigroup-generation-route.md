# 由闭能量形式生成压缩半群：路线探查（Buser 缺口一）

2026-09-19，当日第十五轮。本轮是**路线探查**，**没有证明任何定理**，没有改动任何既有 `.lean`；
交付物是只含 `#check` 的路线语句文件 `research/audits/SemigroupGenerationRouteStatements.lean`
（8 条义务 `S1`–`S8` + 6 条已证声明引用）。**命题通过类型检查不是证明。**
直接洞仍 **0**，证书仍 **26**。不提交、不推送。

起点 `HEAD = origin/main = 7986adf`。

## 先说范围：这不是「把 Buser 缺口填上」

填满[评估](2026-09-19-buser-infrastructure-assessment.md)里的五条缺口是一个**数千行、跨多次会话**的纲领，
本轮只覆盖**缺口一**的路线，而且只到路线层。缺口三（Bakry–Émery Γ 演算）才是真正的数学重头，
本轮完全没有触及。`thm:logconcave-cheeger-poincare-comparison` **不会**因本轮得到 `\leanok`，
常数 π 没有被接近，`B0` 仍未排期。

## 对上一轮评估的更正

上一轮我把缺口一写成「没有办法从闭形式过渡到 `P_t = exp(-tL)`」。**这句话对定理成立、对可行性过头了**，
已在 `tasks.json` 中改写。事实是：生成定理确实不存在（无 `C0Semigroup`、无 Hille–Yosida、
无无界自伴算子的泛函演算），**但经典 Yosida 构造所需的零件都在**：

| 零件 | 位置 |
| --- | --- |
| Lax–Milgram（有界强制形式的预解） | `Analysis/InnerProductSpace/LaxMilgram.lean` |
| Riesz 表示 | `Analysis/InnerProductSpace/Dual.lean` |
| 有界元的 `exp` | `Analysis/Normed/Algebra/Exponential.lean` |
| 无界稠定算子的伴随与闭性 | `Analysis/InnerProductSpace/LinearPMap.lean` |

关键一点：能量形式在 `L²` 上无界，但 Lax–Milgram 是**在形式定义域上**用的——在 `D(T)` 配图范数上，
`B_s(u,v) = ⟪u,v⟫ + s⟪Tu,Tv⟫` 既有界又强制。所以无界性不构成障碍。

本仓库的形式那一侧也已经是现成的：能量以稠定可闭算子 `T : H₀ →ₗ.[ℝ] H₁` 呈现
（`Energy/Relaxation/LinearPMap.lean`、`WeightedGradient.lean`、`ClosedForm.lean`），
`E(f) = ‖T f‖²` 即闭形式。

## 目标

给定实 Hilbert 空间之间稠定**闭**算子 `T`，构造 `L = T*T` 生成的自伴压缩强连续半群 `P_t = exp(-tT*T)`
及其生成元定律。**全部是一般 Hilbert 空间内容**，不含测度、不含对数凹、不含 KLS——
这是刻意的：缺口一是 Buser 纲领里唯一可以独立向 Mathlib 上游贡献的部分。

## 义务清单

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `S1` | `T` 闭 ⟹ `T.graph` 完备（形式定义域是 Hilbert 空间） | 40 | 低（`IsClosed` 按定义即图闭） |
| `S2` | 移位形式在图范数下有界且强制 | 80 | 低 |
| `S3` | 预解存在唯一：弱方程的解 `J_s f` | 250 | 中（Lax–Milgram 的装配与 Riesz 搬运） |
| `S4` | `J_s` 是自伴压缩、非负 | 120 | 低（弱方程取 `v = u`） |
| `S5` | Yosida 近似 `L_s` 有界非负自伴，`exp(-tL_s)` 压缩 | 200 | 中（`NormedSpace.exp` 的谱界记账） |
| `S6` | `exp(-tL_s)` 随 `s ↓ 0` 强收敛 | 500 | **高**（本路线的分析核心，Mathlib 无先例） |
| `S7` | 极限是自伴压缩强连续半群 | 300 | 中 |
| `S8` | 生成元是 `T*T`，且回收形式恒等式 | 300 | 中–高 |

合计约 **1800 行**。推荐顺序：`S1`、`S2`、`S4`、`S3`、`S5`、`S7`、`S6`、`S8`。
`S6` 是唯一可能失控的一项。

## 与 Klartag 轮的结构差异（重要）

Klartag 那轮**不新增任何定义**，所以路线命题可以逐字用既有词汇写出、日后由审计逐字消解。
**本轮做不到**：形式定义域的 Hilbert 结构、`J_s`、`L_s`、`P_t` 都是新对象。
因此 `S3`、`S6`、`S7`、`S8` 是**对假设数据陈述的**（「给定满足这些性质的 `P`，则……」），
而不是对既有名字的断言。实现轮**一定会引入新定义**，这不是对路线的偏离，是路线的既定形状；
新定义的命名与归属须在实现记录里写明。

`S1`、`S2`、`S4`、`S5` 则是完全精确的、可逐字消解的。

## 明确没做什么

* `S1`–`S8` 一条未证。
* 缺口二（Markov 性）、三（Bakry–Émery Γ）、四（小时间热估计）、五（局部化）未触及。
  **即使 `S1`–`S8` 全部证出，Buser 半仍然证不出来**——半群只是四个前置里的第一个。
* 没有新增证书，没有改 Blueprint，没有任何节点状态变化。

## 验证

路线文件以 `lake env lean -DwarningAsError=true` 通过：**14 个 `#check`，0 错误、0 警告**。
无一条命题以 `→ True` 收尾，也无恒真式——首版曾把 `S1` 写成恒等式、`S6`/`S8` 以 `→ True` 收尾，
那样的命题钉不住任何义务，已改写为完备性、极限存在性与形式恒等式。
日志 `build/audit/semigroup-generation-route/route-statements.log`。回执在紧接的实现轮绑定。

## 附记（2026-09-19，部分实现轮之后）

`S1`–`S4` 证出（`Analysis/Semigroup/{Form,Resolvent}.lean`），`S5`–`S8` 未动。
三处与本记录不同：`S1` 实际是一行（`IsClosed` 按定义即图闭 + `IsClosed.completeSpace_coe`），
估的 40 行偏高；`S2` **不需要 `0 < s`**；`S3` **不需要 `Dense (T.domain)`**，
且证法不是本记录设想的 Lax–Milgram 装配，而是按 `√s` 重标度后取**正交投影**——
这绕开了本记录点名的 `innerSL` 星线性摩擦点，`S2` 在 `S3` 的证明里因此没有被用到。
见[实现记录](2026-09-19-semigroup-form-proofs.md)。
