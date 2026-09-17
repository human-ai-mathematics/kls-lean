# 余维 m coarea 正则情形的纤维 Jacobian 恒等式

2026-09-16。本轮**证明新定理**，交付余维 m coarea 正则情形的一个**可审计子块**：
**两侧密度的匹配**（线性形式与 C¹ 形式）以及**正交分裂的保测性**。
**没有证明任何 coarea 公式。** 不迁洞，不提交、不推送。
直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T150413.981186Z/report.json`：10 个门、206 个本地模块内核重放、
537 条目，快照
`95ebf9f762031e9b1d6eb46b0d239bc4ea979b0c3d8a8fc7ef87cfe18a8ea756`。

## 边界

对数凹 Cheeger–Buser 线（等周常数定义的对齐直到与 Poincaré 常数的双向比较，
含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，本轮未触碰。
尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 为什么这一轮不是完整的正则情形

标量 `L9`（`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`）的证明链有四段：

1. **图化**：`ImplicitGraph.lean`（859 行）+ `RegularChart.lean`（164 行），把 `u` 的近旁水平集
   同时参数化成一族图，水平值本身是坐标；
2. **保测分裂**：`SubgraphDivergence.lean`（859 行）里的 `splitHomeomorph` 与
   `measurePreserving_splitHomeomorph`，把 `V` 换成 `H × ℝ`；
3. **纤维方向换元**：`FiberIntegral.lean` + Mathlib 的一维 Jacobian 定理；
4. **逐点密度匹配**：`abs_deriv_mul_norm_gradient`，把 `|∂ψ/∂t| · ‖∇u‖` 换成图面积密度；
   之后是可数覆盖与不交拼接。

余维 m 版本的第 1 段需要**带参数的隐函数定理取值在 m 维空间**，第 3 段需要 m 维换元，
两者都不是一轮能写完的；照上面的行数锚点，第 1、2 段本身就在一千七百行量级。
所以本轮**不去做半个链条**，而是把其中**唯一纯粹是新数学、且与图化机器无关**的一段
——第 4 段的逐点密度匹配——连同第 2 段的**线性/测度骨架**一并做到完。
这两块都不依赖尚不存在的图化机器，任何后续实现都必须用到它们。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/CoareaGraphJacobian.lean`
（本地 import 闭包 9 个模块，**无 WIP**）。

### 线性代数

* **`det_id_add_comp_comm`**：Weinstein–Aronszajn 恒等式的**线性映射形式**
  `det (1 + X ∘ Y) = det (1 + Y ∘ X)`，两边的 `1` 在**不同的空间**上。
  Mathlib 只有矩阵版本 `Matrix.det_one_add_mul_comm`。
  这一条正是「靶空间上的 Gram 行列式换成参数空间上的 Gram 行列式」，
  也就是 coarea Jacobian 换成 area Jacobian 的那一步。
* **`normDet_adjoint`**：维数相等时 `normDet Aᵀ = normDet A`，退化情形一并覆盖。
* **`coareaJacobian_eq_normDet`**：维数相等时 coarea Jacobian 就是 area Jacobian。

### 分裂

* **`IsVectorGraphSplitting`**：`IsGraphSplitting` 的余维 m 类比，法方向是整个空间 `K`
  而不是一个单位向量；两条公理是正交与张成。
* **`isVectorGraphSplitting_orthogonal`**：任意子空间与其正交补给出一个分裂。
* **`finrank_orthogonal_ker_eq`**：`L` 满射时 `finrank (ker L)ᗮ = finrank W`，
  即**正则点上余维假设自动成立**。
* **`IsVectorGraphSplitting.comp_adjoint`**：`L ∘ Lᵀ = P ∘ Pᵀ + Q ∘ Qᵀ`（张成假设用在这里）。
* **`splitVectorIsometry`、`measurePreserving_split`**：
  `(y, z) ↦ ι y + κ z` 是 `H × K` 到 `V` 的**保 Lebesgue 测度**映射，
  经 `WithLp 2` 的线性等距实现，无常数残留。这是后续 Tonelli 的骨架。

### 纤维 Jacobian 恒等式

* **`coareaJacobian_eq_normDet_mul_normDet_graphMapLinear`**（线性形式）：
  在分裂下，若斜率 `A` 使图落在 `ker L` 内（方程 `(L ∘ κ) ∘ A = -(L ∘ ι)`），且
  `finrank K = finrank W`，则
  `coareaJacobian L = normDet (L ∘ κ) * normDet (graphMapLinear ι κ A)`。
* **`normDet_fderiv_mul_coareaJacobian`**（C¹ 形式，标量 `abs_deriv_mul_norm_gradient` 的类比）：
  沿 C¹ 水平族 `u (ι y + κ (ψ (y, t))) = t`，
  `normDet (Dₜψ) * coareaJacobian (fderiv ℝ u x) = normDet (graphMapLinear ι κ (D_yψ))`。
  隐函数微分同时给出斜率方程与 `(L ∘ κ) ∘ Dₜψ = 1`。
  `u` 只要求在该点可微；无有限性、无有界性、无正则值假设。

### m = 1 退回已证结果

* **`graphMapLinear_eq_graphLinear`**、**`normDet_graphMapLinear_eq_graphJacobian`**：
  一维法方向下新的图模型就是仓库原有的 `graphLinear`，体积因子就是已证的 `graphJacobian`。
* **`abs_deriv_mul_norm_gradient_of_vectorGraphSplitting`**：
  `m = 1` 时上面的 C¹ 恒等式**逐字**就是标量的
  `|∂ψ/∂t| · ‖∇u‖ = graphJacobian (∇_y ψ)`。
  与 `Analysis.coareaJacobian_fderiv` 一起，确认新密度在 `m = 1` 时退回 `‖gradient u x‖`。

## 余维假设 `finrank K = finrank W` 是必要的，不是方便

审计客户端不是断言而是**给出反例**：
`fails_without_codimension` 证明只要 `finrank W < finrank K` 且 `L` 满射，
等式右端恒为 `0`（法向体积因子的秩不足）而左端不为 `0`；
`necessity` 把它落实到具体数据——`ℝ²` 的零子空间作参数空间、其正交补（整个平面）作法方向、
`ℝ` 作靶空间——正交、张成与斜率方程都成立，唯独余维假设不成立，恒等式随之不成立。

## 路线语句文件的第二处错误：`A0` 按字面为假，如实报告并更正

上一轮在 `B1` 上发现的归一化错配，**`A0` 里一模一样**：
`research/audits/AreaFormulaRouteStatements.lean` 的 `A0`（路线的目标，Federer 面积公式）
把左边的**原始** `μH[finrank H]` 与右边的 **Lebesgue** 测度配在一起。
审计客户端的 `route_A0_false` **把这条语句证伪**：取平面上的恒等映射与闭单位球，
左端是原始 `μH[2]`，右端是 Lebesgue 测度，两者差 `2² / ω₂ = 4 / π`
（`unitBallVolume_two` 证 `ω₂ = π`，`normalization_constant_ne_one` 证 `4/π ≠ 1`）。
正确的配对仍是原始配原始，或 `hausdorffNormalized` 配 Lebesgue，与 `B1` 的更正一致。

`A5` 写了同样的错配，但**假设与结论两侧一致**，常数相消，
所以 `A5` 不因此为假；只是它的假设不是真正的局部面积公式，
按字面无法与 `A0` 的本意接起来。`A1`、`A2`、`A3`、`A4`、`B2` 的测度配对一致，不受影响。

按不改写历史证据的惯例，`research/audits/AreaFormulaRouteStatements.lean` **保持原字节**，
更正记在本决定与 `research/audits/CoareaGraphJacobianAudit.lean` 中。

## 本轮没有做的事

* **没有证明任何 coarea 公式**，余维 m 的正则情形**没有完成**。
* 没有做带参数的隐函数图化（余维 m 的 `ImplicitGraph`/`RegularChart`），
  没有做纤维方向的 m 维换元，没有做局部到整体的拼接。
* 没有碰临界部分、尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias。
* **没有提交、没有推送**，真实 Git index 未改动。

## 剩余工作（余维 m 正则情形）

1. 余维 m 的局部图化：带参数隐函数定理给出 `ψ : H × W → K` 与其开定义域，
   使 `u (ι y + κ ψ(y,t)) = t`；标量对应物是 `exists_regularChart` 与 `levelChart_inverse`。
2. 纤维方向的 m 维换元：对固定 `y`，`t ↦ ψ(y,t)` 的像上做 Mathlib 的
   `lintegral_image_eq_lintegral_abs_det_fderiv_mul`，本轮的 `measurePreserving_split` 提供
   `V ≅ H × K` 的 Tonelli 骨架。
3. 把 1、2 与本轮的 `normDet_fderiv_mul_coareaJacobian` 和已证的 `B2`
   `hausdorffNormalized_image_vectorGraphMap` 接起来，得到局部形式；
4. 可数覆盖 + 不交拼接，得到 `coarea_of_contDiffOn_of_coareaJacobian_ne_zero`；
   还需要余维 m 的加权切片可测性（标量对应物 `OpenSliceMeasurable.lean`）。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/CoareaGraphJacobianAudit.lean` 的 **30 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；
  含零维参数空间、全空间水平族（无有限性）、正则点数据、余维假设的反例，
  以及路线语句 `A0` 的证伪。
* 重跑全部 **34 个审计客户端**（`research/audits` 27 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-coarea-graph-jacobian.json`，最终核对另存
  `build/audit/coarea-graph-jacobian/final-snapshot.json`。
