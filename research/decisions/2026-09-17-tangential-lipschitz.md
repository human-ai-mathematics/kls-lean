# 纤维上的小 Lipschitz 估计：秩亏路线的 R4（不归点）

2026-09-17。本轮**证明新定理**：秩亏路线义务清单上的 **`R4`**——上一轮标记的**不归点**。
连同 `R1`、`R2`、`R3`，十三条编号里已兑现 **四条**。
**只证了 `R4`**；`R0`、`R5`–`R10`、`N1`、`N2` 仍未证，
**余维 m coarea 的秩亏部分仍然开着**。本轮**没有证明任何 coarea 公式、任何切片定理、任何 Sard 定理**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260917T054703.943157Z/report.json`：10 个门、217 个本地模块内核重放、
581 条目，快照
`3b4bf8210086a351b6cef33b7a2be98ff069fbe0f0f5a07c8ad57e230be74425`，起点工作区 drift 为空。

## 并发会话在本轮中途提交了工作区——如实记录

本轮写完 Lean 之后、收尾之前，**并发会话把整个工作区提交了**：
`HEAD = origin/main` 由 `34b9269…` 变为
`e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`
（`feat: complete scalar coarea and advance vector coarea foundations [skip ci]`，138 个文件）。
该提交**吸收了本会话前四轮的全部成果**（含 `RankStratification.lean`、`RightInverseBound.lean`
及其审计与记录），因此那几轮的「未提交」状态已经不再成立——**是合作者提交的，不是本会话**。

该提交还做了一次「submission review」，改动了**两个我此前写的文件**：

* `research/audits/RankDeficientRouteStatements.lean`：在文件头加了一段状态说明
  （`R1`/`R2` 与 `R3` 两版已证，`R0`、`R4`–`R10`、`N1`、`N2` 仍开），并注明
  **下面的命题一条未改**。文件仍然只含 `#check`，仍无声明、无证明、无占位公理。
* `research/audits/RightInverseBoundAudit.lean`：`constant_map` 的文档串措辞澄清。

**这两处不是本轮所为，本轮也没有回退它们。** 因此本轮不能再说该路线语句文件「保持原字节」——
准确的说法是：**本轮未改动它**，它相对当前 `HEAD` 干净。
本轮的验证与哈希核对全部在新的 `HEAD = e7c4403…` 之上重做。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 「不归点」到底意味着什么——先把话说准

上一轮把 `R4` 标为不归点，理由是：`R2 + R3` 就位后 `R4` 是自足的，
**它若做不出来或常数不一致，整条路线就是错的**。
现在 `R4` **证出来了，常数也确实与 `ε` 无关**。

这只说明**路线没有在它的关键分析步骤上被证伪**。
它**不**说明 `R0` 成立，也**不**说明剩下的 `R5`–`R8` 能做出来：
量纲已经对上、估计已经成立，但把它接成切片零测性还需要
纤维的有限 `ℋ^{n−r}` 测度（`R5`）、靶空间正交分解上的 Fubini（`R6`）、
以及真正的重活——逐层局部装配（`R7`，估计 450–600 行，高风险）。
**本轮没有证明秩亏部分的任何一寸。**

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/TangentialLipschitz.lean`
（137 行，本地 import 闭包 **3 个模块**、无 WIP；依赖同轮的
`Analysis/RankStratification.lean` 与 `Analysis/RightInverseBound.lean`）。

* **`norm_comp_apply_sub_le_of_approximatesLinearOn`**：同一纤维里两点的弦
  `b − a` 满足 `‖P (A (b − a))‖ ≤ ‖P‖ ε ‖b − a‖`。
  **这是纤维假设唯一用到的地方，也是与导数为零情形的分水岭**：
  弦**不在**核里，只是离核不超过 `‖P‖ ε ‖b − a‖`。
* **`exists_lipschitzOnWith_of_ker_bound`**（`R4`）：
  若线性模型 `A` 在 `ker (P ∘ A)` 上死掉（`R2` 的结论），
  且被 `P ∘ A` 几乎零化的向量以常数 `C` 靠近该核（`R3` 的结论），
  则对每个纤维，`Q ∘ f` 在 `S ∩ {P ∘ f = s}` 上是 `c ε`-Lipschitz 的，
  **`c = ‖Q‖ (1 + ‖A‖ C ‖P‖)` 只依赖线性数据，不依赖 `ε`、不依赖 `f`、不依赖 `S`、不依赖纤维**。

  估计链：由上一条得弦几乎在核里 ⟹ 由 `R3` 换成真正的核元素 `w`，`‖(b−a) − w‖ ≤ C‖P(A(b−a))‖`
  ⟹ 由 `R2` 得 `A w = 0`，故 `‖A (b−a)‖ ≤ ‖A‖ C ‖P‖ ε ‖b−a‖`
  ⟹ 回代逼近不等式界住 `‖f b − f a‖`，再作用 `Q`。

  **与 `ε` 无关是全部要点**：Eilenberg 论证里 `ε → 0` 的每个尺度用不同的逼近分片，
  随分片增长的常数毫无用处。这一点直接体现在语句形状 `∃ c, ∀ ε, …` 上。

* **`exists_lipschitzOnWith_fibre`**：`R2 + R3 + R4` 在秩层上的合成——
  `P ∘ A` 满射且 `finrank W₁ = rank A` 时两个假设自动成立。
  **这是三条已证义务的推论，不是新义务，尤其不是 `R7`**：
  它不涉及测度、Hausdorff 维数、切片，也不构造逼近分片。

`R4` 本身**不用内积、不用测度、不用完备性、不用有限维**；`f` 任意、`S` 任意。

## `R2` 的假设是必需的——给出反例，不是断言

`ker_hypothesis_necessary`：取 `A =` 平面上的恒等、`P =` 第一坐标、`Q =` 第二坐标。

* `R3` 的假设**成立**（`P ∘ A` 满射到 `ℝ`）；
* `R2` 的假设**不成立**（第二个基向量被 `P ∘ A` 零化而不被 `A` 零化）；
* `R4` 的结论**不成立**：取 `ε = 0`、`f = A`，结论会逼出第二坐标沿第二坐标轴为常值，而它不是。

所以 `R4` 不是关于逼近本身的陈述，它恰恰断言线性模型沿纤维方向死掉。

## `R3` 的假设**没有**被断言为必需

`R3` 提供的是**常数**，不是限制：有限维下它的结论对每个线性映射都成立
（本轮**没有**证这一点，也没有用到）。另一端由
`zero_model_recovers_vanishing_derivative` 记下：秩零层 `A = 0` 时两个假设都以 `C = 0` 成立，
常数塌成 `‖Q‖`，`R4` 恰好退回已证的导数为零情形——那里 `f` 自己就是 `ε`-Lipschitz 的。
**`R4` 在 `r = 0` 层没有添加任何东西。**

## 边界情形

空集；`ε = 0` 配真实线性模型；零维投影靶空间 `W₂`（`Q = 0`，一切 `0`-Lipschitz）；
秩零模型 `A = 0`。

## 本轮没有做的事

* **没有证明 `R0`**：秩亏部分一寸未动。
* **没有证明 `R5`**（纤维的有限 `ℋ^{n−r}` 测度）、**`R6`**（靶空间分解上的 Fubini）、
  **`R7`**（逐层局部装配，高风险重活）、`R8`–`R10`、`N1`、`N2`。
* **没有证明任何 coarea 公式**，也没有改进已证的余维 m coarea 的适用范围。
* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言。
* 没有修改任何既有 `.lean`（包括 `FunctionalInequalities.lean`、
  `RankDeficientRouteStatements.lean` 与 `AreaFormulaRouteStatements.lean`，
  后两者本轮未被本会话改动——前者由并发会话在提交中加了状态说明，见上）；
  没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一步

按原顺序是 **`R5` 与 `R6`**（彼此独立，可并行，各约 150 行、中风险），
然后是 `R7`。`R7` 仍是唯一的高风险项。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/TangentialLipschitzAudit.lean` 的 **10 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`。
* 重跑全部 **44 个既有审计客户端**加新客户端共 **45 个**，全部严格通过，0 失败；
  公理报告 604 条，其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-tangential-lipschitz.json`，
  最终核对另存 `build/audit/tangential-lipschitz/final-snapshot.json`。
