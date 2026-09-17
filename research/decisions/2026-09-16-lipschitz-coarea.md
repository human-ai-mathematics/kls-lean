# L6a、L7、L12：Lipschitz 加权 coarea 完成

2026-09-16。起点 HEAD 与 origin/main 均为
`dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`，本轮不提交、不推送、不改变真实 Git index。
起点回执 `20260915T181325.091264Z` 通过，486 条目，快照
`01eaccf7af20c08a011382e6c204b98c2613daa1e93f919da50c039cbee53e1c`，与起点源码一致。
全部既有 Lean 文件、历史决定和旧审计客户端保持原字节。

## 精确成果

* **L6a**：`Analysis.LipschitzJet.exists_compact_jets`，在
  `Analysis/LipschitzJet.lean`。有限维实范数空间、任意加法 Haar 测度、任意全局 Lipschitz
  实函数，有可数紧片覆盖几乎处处的点；每片上函数可微、环境导数字段连续、一阶余项一致。
* **L7**：`Analysis.exists_contDiff_pieces`，在 `Analysis/LipschitzC1Pieces.lean`。
  在有限维实内积空间中，有可数两两不交可测片，覆盖几乎处处的点；每片有一个全局 C¹
  代表，并且原函数在片上可微，代表的值与**环境导数**都逐点等于原函数的值与环境导数。
* **L12**：`KLS.coarea_of_lipschitz`，在 `KLS/Geometry/LipschitzCoarea.lean`。
  任意全局 Lipschitz 实函数 u、可测 S、可测 `g : V → ℝ≥0∞`，给出切片积分的
  `AEMeasurable` **及**原路线的完整带权 coarea 等式。

没有加入 C¹、正维、有界域、有限体积、有限权重、可积性、正则值或 `SFinite surfaceMeasure`
假设；空集、零维和权重恒为 ∞ 均在原语句范围内。surfaceMeasure 的原有归一化完全不变。
公开定理不额外列出有限维已蕴涵的 CompleteSpace；新客户端的 `original_L6a`、
`original_L7`、`original_L12` 和 `original_T2` **逐字保留原路线命题文本**，并给出证明。
这些不是 `#check` 或新公理。

## L6a 的实现：直接一致化环境余项

不需要另建一般 Lusin 定理，也没有误用 Lusin–Souslin。取固定可数稠密向量序列 q_i，定义

`goodSet u ε δ = {x | ∀i, ‖q_i‖<δ → ‖u(x+q_i)-u(x)-Du(x)q_i‖≤ε‖q_i‖}`。

1. `measurable_fderiv_apply_const` 与 u 连续给出 goodSet 可测；它只量化可数序列。
2. 对固定 x，向量变量上的条件为闭条件（开球条件蕴涵闭不等式），由稠密性推广到所有 h。
3. 在可微点，每个 ε>0 都有某个半径 `1/(m+1)` 满足该条件；半径递减时 goodSet 递增。
4. 对有限测度可测 A 中的可微点、每个精度 `1/(n+1)`，从递增覆盖选一个统一半径，
   丢弃测度小于 d_n 的例外，预先选 `∑d_n<ε/2`。交遍所有精度后，再用紧内正则性，
   丢弃小于 ε/2 的测度，得到紧集 C⊆A，且 `μ(A\C)<ε`。
5. A 取可微点集与空间紧覆盖的交，ε 取 `1/(k+1)`，把 (m,k) 重新编码为自然数。
   Rademacher 给可微点集补集零测；任意小的丢失测度给最终可数紧片的余集零测。

这个方法得到更强的估计：base point x 在 C 上，而增量终点 x+h 可以在 C 外。
因此导数连续性可直接推出：比较 x 与 y 处同一小增量 h 的两个余项，再用全局 Lipschitz
界控制 `u(x+h)-u(y+h)` 和 `u(x)-u(y)`。在 `δ/2≤‖h‖<δ` 的球壳上得算子范数界；
`ContinuousLinearMap.opNorm_le_of_shell` 给片上导数字段一致连续。
这一步不要求片有内点，也不从片上的函数值相等推导环境导数相等。

## L7 与 L12 的拼接

L7 对每个紧 jet 应用已证明的 L6，再取 `disjointed` 差分片。差分片仍可测、位于原紧片，
其并集不变，故精确值与导数等式和几乎处处覆盖均保留。

L12 令 P_j=S∩第 j 片。L11 用于第 j 个 C¹ 代表；值相等识别切片，环境导数相等识别梯度。
两侧分别使用可测不交可数并的 lintegral 可加性；L11 给每片切片积分的 AEMeasurable，
允许交换外积分和可数和。原函数补集上剩余的体积零测部分，由 **L2 零测切片定理**处理，
不能只靠 Rademacher。两边均用限制测度的 a.e. 集合相等移除余集，因此不需要控制无限权重。
L12 的总体切片 AEMeasurable 也直接由既有 L5 提供。

## 审计

`research/audits/LipschitzCoareaAudit.lean` 独立导入新无洞模块，证明原始 L6a、L7、L12、
T2 四条命题，并逐字节比对原始决定中的命题文本。15 条新公理报告只有
`propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。
边界客户端包括：实数范数函数（同时证明它在 0 不可微）、无界全空间上的任意权重、
常数函数配恒 ∞ 权重（外切片积分为 0）、零维空间。

三个新模块和客户端严格编译；23 个审计客户端（research/audits 16 个，已有 build/audit 7 个）
全部重跑。三个 WIP 逐个重编译仍是 **2/2/5**。旧客户端有意报告仍存在的原始 WIP 洞；
新客户端的 T2 证明与旧名字仍有 sorryAx 是不同的声明，不混为一谈。
全部命令、日志哈希、原语句比较、来源保持检查在
`research/explorations/2026-09-16-lipschitz-coarea.json`。最终默认构建、完整 verification、
198 个本地模块内核重放和精确源码绑定以
`build/audit/lipschitz-coarea/final-snapshot.json` 所指回执为准。

## 当前边界与下一步

**L6a、L7、L12 已完成。Lipschitz 加权 coarea 的数学证明已完成。** 原始 T2 命题已由新客户端
作为 L12 的 S=univ 特例证明，但旧的
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 仍留在
`KLS/WIP/AnalyticPrerequisites.lean` 中。本轮止于用户指定的 L12，没有迁移或改写旧入口。

**下一步是独立迁出 T2**：迁出前后机器比较 `pp.all` 签名，包括 CompleteSpace 和参数顺序，
接到 L12 的全空间特例；随后重跑旧消费者公理审计，才能把直接洞计数从 9 降到 8。
当前源码直接洞仍 **9（2/2/5）**，证书 **24**，perimeter infrastructure **missing**。
尖锐有限正则性 Sard、两个 Cheeger 比较、Energy 的 5 个洞和维数无关 KLS 仍开放。
本轮不增加 Blueprint leanok 或证书，不把 coarea 完成误标为 KLS 完成。
