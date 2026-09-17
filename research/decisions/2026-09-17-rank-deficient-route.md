# 秩亏部分的路线探查：余维 m coarea 仅存的结构性缺口

2026-09-17。本轮是**路线探查**，**没有证明任何定理**，没有新增任何库模块，
没有修改任何既有 `.lean`。交付物是：障碍的精确定位、Mathlib 与本仓库的如实检索、
带编号的义务清单（每条配精确 Lean 语句、行数与风险），以及只含 `#check` 的路线语句文件
`research/audits/RankDeficientRouteStatements.lean`。
**命题通过类型检查不是证明**；下面 15 条命题**没有一条**在本仓库中被证明。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260917T040643.447621Z/report.json`：10 个门、215 个本地模块内核重放、
570 条目，快照
`269225e023675a7cac5a1f69eae2980bcf7d9e96bd073111871dfe6b8e9e9efb`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。
本轮也**没有**扩展到任何 Sard 定理。

## 一、障碍的精确定位

记 `n = finrank V`、`m = finrank W`、`k + m = n`。coarea 的临界集是
`Σ = {x | fderiv ℝ u x 不满射}`，按秩分层 `Σ_r = {x | rank (Du x) = r}`，`0 ≤ r ≤ m − 1`。
上一轮证的是 `Σ_0 = {Du = 0}` 那一层。

**已证方法为什么恰好只覆盖 `r = 0`。** 逼近分片
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 的逼近线性映射是导数的取值；
在 `Σ_0` 上它为零，线性部分整个脱落，于是 `u` 在每片上真的是 `ε`-Lipschitz，
Eilenberg 界的常数 `ε^m` 随 `ε → 0` 趋于零。`r ≥ 1` 时导数不为零，
**在像空间的 `r` 个方向上 `u` 完全不是小 Lipschitz 的**，这一步直接失效。

**「沿存活方向投影」给出的是错误量纲。** 设 `Q` 是 `W` 到 `(range Du)ᗮ`（维数 `m − r`）
的正交投影，则 `Q ∘ u` 在分片上确实是 `ε`-Lipschitz 的。把已证的 Eilenberg 界
`exists_measurable_majorant_vector` 用在它上面，形状是

```
∫⁻ τ, μH[d] (S ∩ {Q ∘ u = τ}) dτ ≤ C · ε^(m−r) · μH[d + (m−r)] S
```

于是对 Lebesgue 正测度的 `S`，右端有限**逼迫** `d + (m − r) = n`，即 `d = k + r`：
结论是 `μH[k + r]` 零测，而不是要的 `μH[k]` 零测。**方向是反的**——
`μH[k+r]` 零测的集合完全可以有无穷的 `μH[k]`。这正是路线语句 `N1` 写下的东西。

反过来，如果坚持取 `d = k`，右端就是 `μH[k + (m−r)] S = μH[n − r] S`，
而 `r ≥ 1` 时只要 `S` 有正 Lebesgue 测度，这个量就是 `∞`（路线语句 `N2`），
界完全空洞。**所以单次切片无论怎么选量纲都不成立，必须迭代切片。**

## 二、修好量纲的路线：先沿 r 个「好」方向切

在 `Σ_r` 的一点取 `W₁ = range (Du x₀)`（维数 `r`），`P`、`Q` 分别是 `W` 到 `W₁`、`W₁ᗮ`
的正交投影。则在该点附近 `v := P ∘ u` 是到 `W₁` 的**淹没**，
**已证的**正则 coarea 公式 `coarea_of_contDiffOn_of_coareaJacobian_ne_zero` 对它适用。

线性代数的关键（义务 `R2`）：`P ∘ Du x` 满射到 `W₁` 且 `rank (Du x) = r` 时，
`P` 在 `range (Du x)` 上单，于是 `ker (P ∘ Du x) = ker (Du x)`——
**在层上，微分沿正则部分的纤维方向恰好为零**。所以 `Q ∘ u` 限制在纤维上导数为零。

于是把 Eilenberg 界用在**纤维内部**：取 `d = k`，靶空间 `W₁ᗮ` 维数 `m − r`，
`d + (m − r) = k + m − r = n − r`，**正是纤维有限测度的那个维数**（义务 `R5`）。
量纲对上了。最后用靶空间正交分解上的 Fubini 把「几乎每个 `s`、几乎每个 `τ`」
合成「几乎每个 `t`」（义务 `R6`）。

这是**迭代切片**：先按 `v` 在余维 `r` 切，再在每个纤维里按 `Q ∘ u` 在余维 `m − r` 切。

一个本轮才看清的技术点：纤维的**弦不是切向量**。`a, b` 同在 `v` 的一个纤维里只给出
`‖P A (b−a)‖ ≤ ‖P‖ ε ‖b−a‖`，要把它变成 `‖A (b−a)‖` 小，需要 `P ∘ A` 的右逆的范数界
（义务 `R3`），且该界必须在邻域上**一致**，因为 `ε → 0` 的每个尺度用的是不同的分片。
合起来就是义务 `R4`：`Q ∘ f` 在 `P ∘ f` 的每个纤维上是 `c·ε`-Lipschitz 的，
`c` 只依赖 `‖A‖、‖P‖、‖Q‖` 与右逆界，不依赖 `ε`。
**`R4` 是本路线的新分析内容，也是路线成立与否的单点判据。**

## 三、Mathlib 与本仓库有什么、缺什么（如实检索）

**Mathlib 没有的**：
* **没有任何 coarea 公式**（全库检索 `coarea` 零命中）；
* **没有常秩定理**（`constantRank`/`ConstantRank` 只出现在 `RingTheory` 的交换代数语境，
  与浸没/淹没的常秩定理无关）；
* **没有 Federer 面积/上面积公式的退化部分**；
* 没有 Morse–Sard；`HausdorffDimension.lean` 里叫「Sard 的特例」的两条
  （`ContDiffOn.dense_compl_image_of_dimH_lt_finrank`、
  `ContDiff.dense_compl_range_of_finrank_lt_finrank`）只给像的补集**稠密**，不给零测。

**Mathlib 有的、本路线要用的**：
* `isOpen_setOfPred_nat_le_rank`：`{f : E →L[𝕜] F | r ≤ rank f}` 是开集——秩的下半连续性，
  直接给出 `R1` 的分层可测性；
* `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 与 `ApproximatesLinearOn` 一线：
  只给「逼近 + 可数不交可测分片」，**不给**任何秩结构；
  `ApproximatesLinearOn.antilipschitz` 要求线性模型是**等价**，秩亏时不适用。
  它能给的恰好就是 `R4` 的输入，不多不少；
* `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`：**同维数**的 Sard 引理
  （`E → E`，微分不可逆处的像零测）——这正好给出 `R10`；
* `Submodule.orthogonalDecomposition : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ)`、
  `LinearIsometryEquiv.measurePreserving`、`WithLp.volume_preserving_ofLp`——`R6` 的全部零件；
* `hausdorffMeasure_of_lt_dimH`——`N2` 的零件。

**本仓库有的**：余维 m Eilenberg 界（`VectorHausdorffSlicing.lean`）、
正则 coarea 公式（`VectorRegularCoarea.lean`）、无正则性的切片可测性
（`VectorSliceMeasurable.lean`）、导数为零部分的临界切片（`VectorCriticalSlice.lean`）、
`coareaJacobian` 与伴随一线（`CoareaJacobian.lean`，含 `ker_adjoint`、
`coareaJacobian_ne_zero_iff`）、`isometryEquivOfFinrankEq`（`VectorFiberIntegral.lean`）。

**缺的**：下面 `R1`–`R10` 全部，一条都没有。

## 四、义务清单

精确 Lean 语句在 `research/audits/RankDeficientRouteStatements.lean`，
按本表编号排列；该文件只含 `#check`，无声明、无证明、无占位公理，
以 `-DwarningAsError=true` 通过。**通过类型检查不是证明。**

| 编号 | 内容 | 估计行数 | 风险 |
| --- | --- | --- | --- |
| `R0` | **目标**：秩亏临界集在几乎每个水平上的 `μH[k]` 零测 | — | 由 `R1`–`R8` 合成 |
| `R1` | 秩分层可测；临界集是 `r < m` 各层的有限并 | 60 | 低 |
| `R2` | 核引理：层上微分沿纤维方向为零（纯线性代数） | 40 | 低 |
| `R3` | 满射的近似右逆：逐点 + 邻域上一致 | 50 + 120 | 低 / 中 |
| `R4` | **纤维上的小 Lipschitz 估计**（新分析内容） | 120 | 中 |
| `R5` | 正则部分的纤维有有限 `ℋ^{n−r}` 测度 | 150 | 中 |
| `R6` | 靶空间正交分解上的 Fubini | 150 | 中 |
| `R7` | **每层的局部切片**（`R1`–`R6` 的装配） | 450–600 | 高 |
| `R8` | 局部零测切片补到整体（第二可数 + 可数交） | 90 | 低 / 中 |
| `R9` | 消费者：**无二分假设**的余维 m coarea 公式 | 60 | 低 |
| `R10` | 同维退化情形 `n = m`（独立旁证） | 80 | **低，便宜** |
| `N1` | 障碍的陈述：小 Lipschitz 法给出的**错误指数** | 120 | 低 / 中 |
| `N2` | 障碍的定量：指数降不下来，右端是 `∞` | 40 | 低 |

全程序约 **1500 行**。

各条的理由与风险来源：

* **`R1`**（低）。Mathlib 的 `isOpen_setOfPred_nat_le_rank` 给 `{r ≤ rank}` 开，
  层是两个开集之差。分解式要「满射 ⟺ rank = m」，有限维下直接。
* **`R2`**（低）。`P` 在 `range L` 上满射且两边维数相同 ⟹ 单射 ⟹ 两个核相等。
* **`R3`**（逐点低、一致中）。逐点用 `CoareaJacobian.lean` 已有的伴随伪逆
  `L*(L L*)⁻¹`。一致版要 `x ↦ (Du (Du)*)⁻¹` 的连续性，即可逆算子上取逆的连续性；
  Mathlib 有，但要在 `coareaJacobian ≠ 0` 的开集上做紧邻域上的一致界，属于常规但琐碎。
* **`R4`**（中）。估计链本身两行数学：`‖P A z‖ ≤ ‖P‖ε‖z‖` ⟹ 由 `R3` 取 `w`，
  `‖z − w‖ ≤ C‖P‖ε‖z‖` ⟹ 由 `R2` 得 `A w = 0` ⟹ `‖A z‖ ≤ ‖A‖C‖P‖ε‖z‖` ⟹
  `‖Q f b − Q f a‖ ≤ ‖Q‖(1 + ‖A‖C‖P‖)ε‖b−a‖`。风险全在 `ℝ≥0` 算术与
  `LipschitzOnWith`/`ApproximatesLinearOn` 的接口，不在数学。
* **`R5`**（中）。已证 coarea 取权 `1`：相对紧片上被积函数连续有界，总积分有限，
  故几乎每个水平的纤维测度有限。还要一条 `hausdorffNormalized` 与原始 `μH` 的**有限性**
  互推（现有的只有零测互推 `hausdorffNormalized_eq_zero_iff`），是新的小引理。
* **`R6`**（中）。零件齐全，风险在实例管道：`WithLp 2 (W₁ × W₂)` 上的
  `MeasurableSpace`/`BorelSpace`/`volume` 实例是否与 `Measure.prod` 对齐，
  以及子空间类型上的 `volume` 实例。建议**用抽象的 `W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)` 陈述**
  （路线文件里就是这样写的），把子空间实例的麻烦留在调用处。
* **`R7`**（高）。本轮唯一的重活。注意两处易错：
  （i）**只能从层上的点出发**取邻域——在秩更低的点附近没有固定的 `r` 维 `P` 可用，
  哪怕层的点任意靠近；这对 `R8` 够用，因为只需覆盖被切的集合；
  （ii）逼近分片要对 **`u` 本身**做，一套分片同时供 `P ∘ u` 与 `Q ∘ u` 使用，
  且逼近线性映射 `A n = Du y` 的 `y` 落在层上，`R2` 才能用；
  （iii）`c` 必须在片之间一致，所以 `R3` 的一致版是硬需求，不是方便。
* **`R8`**（低/中）。`VectorRegularCoarea.lean` 里已经用过
  `TopologicalSpace.isOpen_iUnion_countable`，照抄即可。
* **`R9`**（低）。把已证的 `coarea_of_contDiff_of_critical_eq_zeroDeriv` 的证明逐字搬过来，
  `hcrit` 换成 `R0`。其中的 `0 < finrank ℝ W` 是**从已证语句原样继承**，不是新增假设。
* **`R10`**（低，**便宜**）。`n = m` 时 `k = 0`，`μH[0]` 零测就是**空集**，
  所以命题是「几乎没有水平是临界值」。Mathlib 的同维 Sard 引理直接给出，
  沿本仓库的 `isometryEquivOfFinrankEq` 搬运即可。**本轮没有证它**——
  见下面「为什么本轮什么也没证」。
* **`N1`/`N2`**（低/中）。两条都是可证的**诊断**语句，用来把障碍钉死在纸面上，
  不是通往 `R0` 的步骤。`N1` 的两个边条件都是真的：`S` 要可测才能把各片的控制函数加起来，
  `0 < finrank W₂` 才让 Eilenberg 常数 `ε^(dim W₂)` 趋零——`r = m` 时无方向可投，命题为假。

## 五、建议的主攻顺序，与不建议现在做的部分

**建议顺序**：

1. `R2`（核引理）。最小、最便宜，而且它是整个设计的几何心脏；它一旦成立，
   「纤维方向上导数为零」就从直觉变成事实。
2. `R1`（分层）。小，且没有它连 `R7` 的语句都写不出来。
3. `R3`（两个版本一起做）。
4. `R4`。**这是不归点**：`R2 + R3` 就位后 `R4` 是自足的，
   如果 `R4` 做不出来或常数不一致，整条路线就是错的，应当在投入 `R7` 之前先知道。
5. `R5` 与 `R6`（彼此独立，可并行）。
6. `R7`，然后 `R8`、`R9`。

**不建议现在做的**：

* **不要先做 `R7`**。它依赖上面全部五条，先做只会得到一个到处是 `sorry` 的骨架。
* **不要把 `R10` 当成进展**。它便宜、可以作为审计旁证单独证，
  但它**不在通往 `R0` 的路上**：`n = m` 时 `r` 仍要跑遍 `r < m` 的所有中间秩，
  同维 Sard 引理不给中间层任何信息。把它说成「秩亏部分证了一部分」是虚报。
* **不要碰 Sard**。本路线给的是临界**切片**零测，对临界**值**集合的测度什么也不说；
  仅仅 `C¹` 的映射其临界值集合完全可以有正测度。这是两个问题。
* **不要试图一次做完 Federer 的退化 coarea**，也不要顺手扩到 `C¹` Morse–Sard。
* 不要碰对数凹 Cheeger–Buser 线（王浩丞）、尖锐有限正则 Sard、Energy 的五个洞。

## 六、为什么本轮什么也没证

`R10` 确实便宜。但把它证进库里要新增一个库模块，而新模块必须进
`formalization/FunctionalInequalities.lean` 的聚合 import 才会被默认 `lake build` 覆盖，
那就要**修改既有 `.lean`**——本轮明令不做。因此本轮把 `R10` **如实标注为便宜但未证**，
而不是为了「有产出」去违反边界。**本轮没有证明任何定理。**

## 七、路线语句文件复核

本轮重跑 `research/audits/AreaFormulaRouteStatements.lean`，**未发现新的错误**，
文件继续**保持原字节**。已记录的两处仍是 `B1` 的归一化错配与已被证伪的 `A0`。

一条**本轮新增的观察**（不是新错误）：`A5`（局部化）两端用的是与 `A0` 相同的
`μH` 配 Lebesgue 的错配。但 `A5` 是一个**蕴含式**，其证明只用到两端关于集合的可数可加性，
与归一化常数无关，所以 `A5` 本身**没有被证伪**，仍是一条真命题；
只是它的结论正是按字面为假的 `A0`，因而它的前提在该归一化下不可满足。
如实记下，不改文件。

## 八、验证

* 新客户端 `research/audits/RankDeficientRouteStatements.lean`（309 行，15 条 `#check`）
  以 `-DwarningAsError=true` 通过，**无声明、无证明、无 `sorry`、无 `axiom`、无占位**。
  其本地 import 闭包 **28 个模块，无 WIP**。
* 因为本轮没有新证的声明，**没有新的公理报告**；既有客户端的公理报告未变：
  558 条标准三公理报告，12 条 `sorryAx` 报告，全部落在四个**故意**报告未决 WIP 结果的客户端里
  （`LevelSetMeasurableAudit`、`IsoperimetryCoareaAudit`、`LipschitzCoareaMigrationAudit`、
  `build/audit/SuperlevelSardScope`），与语义对齐节记录的 12 条一致。
* 重跑全部 **41 个既有审计客户端**（`research/audits` 34 个、`build/audit` 7 个）
  加新客户端共 **42 个**，全部以 `-DwarningAsError=true` 严格通过，0 失败。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；
  证据 JSON 为 `research/explorations/2026-09-17-rank-deficient-route.json`，
  最终核对另存 `build/audit/rank-deficient-route/final-snapshot.json`。
* **没有提交、没有推送**，真实 Git index 未改动。

---

## 附记（2026-09-17，同日稍后补记，正文未改写）

上面第六节「为什么本轮什么也没证」给出的理由**是错的**，如实更正于此，原文保留不动。

`research/verify.py` 的构建与内核重放范围由 `replay_sources` 从**源码树**计算，
`build_replay_inputs` 的注释原文是
"Build the exact replay scope, including modules outside default import closures"；
现有的 `Analysis/Vector*.lean` 诸模块同样不在 `formalization/FunctionalInequalities.lean`
的聚合 import 里，一样被重放门覆盖。
因此**新增 `Analysis/` 模块并不需要修改聚合 import**，上面据此作出的「不能证」的推断不成立。

据此，同日的后续一轮证明了义务 `R1` 与 `R2`，未修改任何既有 `.lean`；
见 `research/decisions/2026-09-17-rank-stratification.md`。
`R10` 至今**仍未证**，本附记不改变这一点，也不改变本轮「没有证明任何定理」的记录。
