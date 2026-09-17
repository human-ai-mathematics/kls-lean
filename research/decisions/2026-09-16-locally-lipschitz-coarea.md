# L13：局部 Lipschitz 加权 coarea

2026-09-16。本轮**证明一个新定理** `KLS.coarea_of_locallyLipschitz`，把标量加权 coarea
从「全局 Lipschitz」放宽到「**局部 Lipschitz**」。不迁洞，不提交、不推送，
不改写历史决定。直接洞仍 **8（1/2/5）**，证书仍 **24**，
perimeter infrastructure 仍 **missing**。

起始 HEAD 与 `origin/main` 均为 `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`；起始 passed 回执为
`build/verification/20260916T074938.349555Z/report.json`：10 个门、198 个本地模块内核重放、
495 条目，快照 `115a7e19375062d43882a1ff2caa16b5ca52b0791af25734aacfff66ac61735c`。

## 边界：Cheeger 线不在本轮范围

`KLS/WIP/CheegerInfimum.lean` 的两个洞
（`Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le` 与
`Isoperimetry.smoothConstant_le_minkowskiConstant`），以及等周常数几种定义的对齐与
Cheeger↔Poincaré 双向比较，已于本日交给合作者**王浩丞**。本轮不碰这条线，
只推进通用 coarea 与 `Analysis`/`Geometry` 分析基础。

## 精确成果

`KLS/Geometry/LocallyLipschitzCoarea.lean`：

```lean
theorem FunctionalInequalities.KLS.coarea_of_locallyLipschitz
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hu : LocallyLipschitz u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ)
```

**这是 L11 与 L12 的共同推广。** `LipschitzWith K u → LocallyLipschitz u` 还原 L12，
`ContDiff ℝ 1 u → LocallyLipschitz u` 还原 L11（`ContDiff.locallyLipschitz`），
所以既不需要 Lipschitz 常数，也不需要 C¹。两条原定理的语句、证明与位置**全部不变**，
没有用 L13 重述它们，也没有新增 alias。

**推广是严格的。** 客户端给出 `x ↦ x² + ‖x‖` 并在同一文件里证明：它局部 Lipschitz、
**对任何常数都不是全局 Lipschitz**（取 `x = K+1` 与 `dist_le_mul` 矛盾）、
**在 0 处不可微**（否则 `‖·‖ = witness - x²` 在 0 可微，与
`not_differentiableAt_norm_zero` 矛盾）。因此它同时落在 L11 和 L12 之外，而 L13 覆盖它。

没有加入有界、有限体积、有限权重、可积性、正则值或 `SFinite surfaceMeasure` 假设；
`S` 是任意可测集，权重可以恒为 ∞，零维在语句范围内，surfaceMeasure 归一化不变。

## 证明：半开环带归约

`V` 有限维故 proper，闭球紧。

1. `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact` 给出 `u` 在
   `closedBall 0 (k+1)` 上的 Lipschitz 常数；McShane 延拓 `LipschitzOnWith.extend_real`
   把它换成**全局** Lipschitz 的 `v k`，且 `EqOn u (v k) (closedBall 0 (k+1))`。
2. 取半开环带 `A k = ball 0 (k+1) \ ball 0 k`。它们两两不交、可测，且
   `x ∈ A ⌊‖x‖⌋₊`，故覆盖全空间。令 `P k = S ∩ A k`。
3. 关键是 `P k ⊆ ball 0 (k+1)` 用的是**开**球：开球是每点的邻域，`u` 与 `v k` 在其上相等，
   所以 `EventuallyEq.gradient_eq` 给出逐点 `gradient u x = gradient (v k) x`，
   而不是只在某个稀疏集上相等。同一理由使 `P k ∩ {v k = t} = P k ∩ {u = t}`。
4. 对每个 `P k` 用 L12，再用不交可数并的 `lintegral_iUnion` 和 `lintegral_tsum` 拼接；
   交换外积分与可数和所需的逐片 `AEMeasurable` 正是 L12 的第一个分量。
5. 总体切片可测性同样由分解得到：对每个 `t`，
   `∫⁻ y in S ∩ {u=t}, g` 是可数不交片上积分之和（`{u=t}` 由 `u` 连续而可测），
   再用 `AEMeasurable.tsum`。这里**没有**对无界的 `S` 假设全局 `LipschitzOnWith`，
   因此不能直接引用 L5，必须走这条可数分解。

## 审计

`research/audits/LocallyLipschitzCoareaAudit.lean` 只导入新的无洞模块，不导入任何 WIP。
10 条公理报告全部只用 `propext`、`Classical.choice`、`Quot.sound`：
逐字复述并以具名参数兑现的 `original_L13`；**不提** `coarea_of_lipschitz` 而从 L13 还原
L12 的 `recovers_L12`；**不提** `coarea_of_contDiff` 而从 L13 还原 L11 的 `recovers_L11`；
见证函数的三条性质与它的 coarea 等式；恒 ∞ 权重；零维。

新模块的本地 import 闭包共 30 个模块，其中**没有任何 WIP 模块**。

## 本轮没有做的事

* 没有碰 `KLS/WIP/CheegerInfimum.lean` 的两个洞（已交给王浩丞）。
* 没有迁移任何洞，直接洞仍 **8（1/2/5）**；没有证明尖锐 `C^(finrank)` `Analysis.sard`、
  Energy 的五个洞或维数无关 KLS。
* 没有扩大证书或 Blueprint `leanok` 范围；没有把 coarea 推广误标为 KLS 进展。
* 没有把 L13 说成向量值 coarea：目标仍是实值 `u : V → ℝ`，没有 coarea Jacobian。
* **没有提交、没有推送**，真实 Git index 未改动。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* 重跑全部 25 个审计客户端（`research/audits` 18 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 文件逐个实际编译，直接洞分别 **1/2/5，总数 8**，与上一轮一致。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-locally-lipschitz-coarea.json`，最终核对另存
  `build/audit/locally-lipschitz-coarea/final-snapshot.json`。

---

**后续指针（2026-09-16，同日稍后；正文未改）**：本轮之后的仓库语义对齐轮把
`lem:relative-perimeter-smoothing` 的 infrastructure 由 `missing` 改为 `available`，
并把真正缺失的 Cheeger 基础设施移到 `lem:relative-perimeter-cheeger-infimum`
（仍 `missing`，2 个缺口）。因此上文「perimeter infrastructure 仍 **missing**」是本轮运行时的
准确记录，当日稍后即被取代。按不改写历史决定的惯例，正文保留原样，只在此处加指针。
该对齐轮不证明新定理、不改数学语句、不新增证书，并明确包含本轮的 L13。
见[语义对齐决定](2026-09-16-semantic-alignment.md)。
