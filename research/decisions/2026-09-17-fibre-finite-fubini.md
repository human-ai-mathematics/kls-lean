# 纤维有限性与靶空间 Fubini：秩亏路线的 R5 与 R6

2026-09-17。本轮**证明新定理**：秩亏路线义务清单上的 **`R5`** 与 **`R6`**，按建议顺序的第五步
（两条彼此独立，可并行）。连同 `R1`–`R4`，十三条编号里已兑现 **六条**。
**只证了 `R5` 与 `R6`**；`R0`、`R7`–`R10`、`N1`、`N2` 仍未证，
**余维 m coarea 的秩亏部分仍然开着**。
本轮**没有在新情形下证明任何 coarea 公式、没有证明任何关于临界集的切片定理、没有证明任何 Sard 定理**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；起点 passed 回执
`build/verification/20260917T063346.288828Z/report.json`：10 个门、218 个本地模块内核重放、
586 条目，快照
`48d51f94be3b32ff9459acee074af1301a84518c7eb05cc2104187f1d0e28c3e`。
起点工作区 drift 为空；起点未提交项恰为上一轮（`R4`）的成果。本轮**并发会话未再改动工作区**。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## `R5`：正则部分的纤维有有限测度

新模块 `formalization/FunctionalInequalities/Analysis/RegularFibreFinite.lean`
（103 行，本地 import 闭包 22 个模块、无 WIP）。

**用途。** 路线把 Eilenberg 界用在**纤维内部**，取 `d = k`、靶空间维数 `m − r`，
于是 `d + (m − r) = n − r`。要让这个界说出东西，纤维必须携带**有限**的 `ℋ^{n−r}` 测度——
否则右端是 `∞`、估计空洞，正是 `N2` 对一步法记下的那种失效。

* **`hausdorffNormalized_ne_top_iff`**：归一化常数正且有限，故归一化测度有限 ⟺ 原始测度有限。
  这是已证的 `hausdorffNormalized_eq_zero_iff` 的同伴引理。
* **`ae_hausdorffMeasure_fibre_ne_top`**（`R5`）：`v` 在开集 `O` 上 `C¹` 且处处正则、
  `S` 可测、`closure S` 紧且含于 `O`，则**几乎每个水平**上
  `μH[n−r] (S ∩ v⁻¹(s)) ≠ ⊤`。

**这是已证的正则 coarea 公式的推论，不是新分析**：取权 `1`，
`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` 说纤维测度的积分等于 `∫ coareaJacobian`，
而后者在相对紧片上有限（被积函数在开集上连续、在紧闭包上有界，且 `volume S < ∞`）。
积分有限的函数几乎处处有限。

**相对紧性是真假设，给出反例而不是断言。** 审计的 `relative_compactness_necessary`：
平面上的第一坐标泛函处处是淹没，取 `S = univ`，则除紧性外的假设全部成立，
但每个纤维都是整条直线、`ℋ^1` 测度为 `∞`，结论在**每个**水平上都失败（不只是零测集上）。

**对正则集之外什么也没说**：`R5` 假设微分在整个 `O` 上满射，`v` 的临界集在它的射程之外——
这正是路线还需要其余义务的原因。

## `R6`：靶空间正交分解上的 Fubini

新模块 `formalization/FunctionalInequalities/Analysis/TargetSplitFubini.lean`
（91 行，**仅依赖 Mathlib**，本地 import 闭包 **1 个模块**、无 WIP）。

**用途。** 两次切片产生的是「几乎每个 `s ∈ W₁`、几乎每个 `τ ∈ W₁ᗮ`」，
而结论要的是「几乎每个 `t ∈ W`」。`R6` 把两层接起来。

* **`measurableSet_splitPreimage`**：分解下的原像可测。
* **`measure_eq_zero_of_ae_slice_eq_zero`**（`R6`）：若 `N` 的几乎每个第一坐标切片零测，则 `N` 零测。

**是装配工作，但仓库里此前没有。** Mathlib 的
`LinearIsometryEquiv.measurePreserving`、`WithLp.volume_preserving_toLp`、`Measure.prod_apply`
全部齐备，本模块只把它们接起来。分解以抽象的等距 `W ≃ₗᵢ WithLp 2 (W₁ × W₂)` 给出，
由调用方提供；审计的 `orthogonal_decomposition` 用
`Submodule.orthogonalDecomposition` 实例化它——**实例能解出来，所以抽象陈述可直接使用**，
这正是路线沿微分的像做分解时要用的形式。

审计还记下了**反方向**（零测集的切片几乎处处零测），以免把 `R6` 当成容易的一半：
路线要的是本模块证的那个方向，两者出自同一套乘积测度机器。

## 本轮没有做的事

* **没有证明 `R0`**：秩亏部分一寸未动。
* **没有证明 `R7`**（逐层局部装配，估计 450–600 行，**唯一的高风险项**）、
  `R8`–`R10`、`N1`、`N2`。
* **没有在新情形下证明任何 coarea 公式**：`R5` 是已证正则公式的推论，
  已证公式的适用范围没有扩大一分。
* **没有证明任何 Sard 定理**；对临界**值**集合的测度什么也没断言。
* 没有修改任何既有 `.lean`（包括 `FunctionalInequalities.lean`、
  `RankDeficientRouteStatements.lean` 与 `AreaFormulaRouteStatements.lean`）；
  没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一步

只剩 **`R7`**（逐层局部装配）挡在 `R0` 前面，之后是 `R8`（局部补整体）与 `R9`（消费者）。
`R7` 仍是唯一的高风险项：它要把逼近分片对 `u` 本身做一次、同时供 `P ∘ u` 与 `Q ∘ u` 使用，
只能从层上的点出发取邻域，并且常数必须在片之间一致。

## 验证

* 两个新模块与两个新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* 两个客户端共 **14 条公理报告**（`R5` 8 条、`R6` 6 条），只用
  `propext`、`Classical.choice`、`Quot.sound`。
* 重跑全部 **45 个既有审计客户端**加两个新客户端共 **47 个**，全部严格通过，0 失败；
  公理报告 618 条，其中 12 条 `sorryAx` 仍全部落在四个**故意**报告未决 WIP 结果的客户端里。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 **24** 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-fibre-finite-fubini.json`，
  最终核对另存 `build/audit/fibre-finite-fubini/final-snapshot.json`。
