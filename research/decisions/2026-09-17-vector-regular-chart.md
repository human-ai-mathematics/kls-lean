# 余维 m 的带参数隐函数图化

2026-09-17。本轮**证明新定理**，完成余维 m coarea 正则情形的**第二个子块**：
**带参数的隐函数图化**——把正则点附近 `u : V → W` 的**整族**纤维同时写成同一个 C¹ 映射的图，
水平值本身是参数。**仍然没有证明任何 coarea 公式。**
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T160637.697547Z/report.json`：10 个门、207 个本地模块内核重放、
541 条目，快照
`3310e7e26c2c35e83d9cbb93b0bc21c51f65adf4279d8af3fd5f275fd7868dfc`。
起点工作区 drift 为空，并发会话未改动工作区。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，
本轮未触碰。尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。

## 精确成果

新模块 `formalization/FunctionalInequalities/Analysis/VectorRegularChart.lean`
（355 行，本地 import 闭包 16 个模块，**无 WIP**）。它是 `RegularChart.lean` 的余维 m 类比。

### 与标量情形的一处真差别

标量的 chart 是 `x ↦ graphRetract ι x + u x • e`，仍然映到 `V`，因为法方向是 `V` 里的一条直线，
`u x ∈ ℝ` 可以乘上去。余维 m 的 `u x ∈ W` **不在 `V` 里**，所以本轮的 chart 改为映到**乘积**

`Φ x = (ιᵀ x, u x) : H × W`，

从而完全不需要把法方向 `K` 与靶空间 `W` 等同起来，也不需要在 `V` 内选一个 `W` 的拷贝。
仓库的 `exists_contDiffOn_localInverse` 本来就是对两个不同空间叙述的，直接可用。

* **`flattenVectorEquiv`**：`Φ` 在正则点的导数是连续线性等价。
  假设是「参数因子是核方向」`L ∘ ι = 0` 与「法因子被 `Q = L ∘ κ` 双射地送到靶空间」。
  **逆是显式写出来的**：`(y, w) ↦ ι y + κ (Q⁻¹ w)`，不靠维数计数，
  所以退化情形不需要另外讨论。
* **`exists_vectorRegularChart`**：`O` 上 C¹ 的 `u` 在正则点附近给出 `D : V ≃ H × W` 的开局部同胚，
  两侧都 C¹，`D.source ⊆ O`；**`O` 外不需要也不断言任何正则性**。
* **`vectorLevelChart_inverse`**：逆 chart 恰好是每一水平上的图，而且那张图取到该水平：
  `D.symm (y, t) = ι y + κ (ψ (y, t))` 且 `u (D.symm (y, t)) = t`，两者在**同一个联合开定义域**上。
* **`exists_levelGraphFamily`**：把上面打包成实际可消费的形式——
  开集 `Ω ⊆ H × W`、**全局 C¹** 的 `ψ : H × W → K`、开邻域 `N ⊆ O` 含 `x₀`，满足
  `∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2`，图映射把 `Ω` **双射**到 `N`。
  `ψ` 的全局 C¹ 性由 `exists_contDiff_one_eqOn_ball` 在 chart 目标内的小球上取代表元得到，
  与标量文件同法。
* **`comp_ker_subtypeₗᵢ_eq_zero`、`bijective_comp_orthogonal_subtypeₗᵢ`、
  `exists_levelGraphFamily_of_coareaJacobian_ne_zero`**：
  正则点上假设**自动成立**——参数空间取微分的核，法因子取其正交补，
  余维 `finrank Pᗮ = finrank W` 由上一轮的 `finrank_orthogonal_ker_eq` 给出。
  入口假设只有 `coareaJacobian (fderiv ℝ u x₀) ≠ 0`。

### 与已证件的两个接口

* **`slice_eq_image_vectorGraphMap`**：`N ∩ {u = t}` **恰好**是 `y ↦ ψ (y, t)` 在参数切片上的图。
* **`hausdorffNormalized_slice_of_levelGraphFamily`**：于是已证的 `B2`
  （`hausdorffNormalized_image_vectorGraphMap`）直接算出这张纤维的归一化 `(n-m)` 维测度，
  等于图面积密度对参数切片的 Lebesgue 积分。**这是权重为一的情形**；
  一般 coarea 需要的**加权**版本（`setLIntegral_image_graphMap` 的余维 m 类比）**没有证**。
* **`normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily`**：本族逐字满足上一轮
  `normDet_fderiv_mul_coareaJacobian` 的假设，所以在整个 chart 上两侧密度匹配。

## m = 1 退回已证的标量形状

审计客户端里：`lineIsometry` 把单位向量 `e` 张成的直线做成 `ℝ →ₗᵢ[ℝ] V`，
`graphProj_lineIsometry` 证 `graphProj = ⟪e, ·⟫`，
`isVectorGraphSplitting_of_isGraphSplitting` 证**标量的 `IsGraphSplitting` 就是一维法因子的
`IsVectorGraphSplitting`**。于是 `codimension_one_levelGraphFamily` 从**标量的原假设**
（`IsGraphSplitting ι e` 与 `gradient u x₀ = c • e`，`c ≠ 0`）出发，
产出 `u (ι p.1 + ψ p • e) = p.2` 的族——
这正是已证的 `Analysis.setLIntegral_coarea_graph_family` 所消费的 `hlevel` 形状。

## 本轮没有做的事

* **没有证明任何 coarea 公式**；余维 m 正则情形**仍未完成**。
* 没有做纤维方向的 **m 维换元**（环境一侧），
  没有做**加权**的余维 m 面积公式（纤维一侧），
  没有做局部到整体的可数拼接，没有做余维 m 的加权切片可测性。
* 没有迁洞；没有扩大证书或 Blueprint `leanok` 范围；没有新增兼容 alias；没有削弱已证结论。
* 没有增加不必要的假设：没有有界、有限体积、可积性、正则值、SFinite。
* **没有提交、没有推送**，真实 Git index 未改动。

## 路线语句复核

本轮重跑但**未发现新的**路线语句错误。已记录的两处仍然只有
上一轮的 `B1`（2026-09-16 `vector-graph-area` 决定）与
上一轮的 `A0`（2026-09-16 `coarea-graph-jacobian` 决定，`route_A0_false` 已证伪）；
`A5` 两侧错配一致故不为假，`A1`–`A4`、`B2` 不受影响。
`research/audits/AreaFormulaRouteStatements.lean` 继续**保持原字节**。

## 剩余工作（余维 m 正则情形）

1. **环境一侧**：对固定 `y`，`t ↦ ψ (y, t)` 的像上做 m 维换元
   （Mathlib 的 `lintegral_image_eq_lintegral_abs_det_fderiv_mul`），
   骨架是上一轮的 `measurePreserving_split`（`V ≅ H × K` 保 Lebesgue 测度）；
2. **纤维一侧**：加权的余维 m 图面积公式，`setLIntegral_image_graphMap` 的类比；
3. 用本轮的 `normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily` 把两侧密度对上，Tonelli 拼成
   局部 coarea 等式（标量对应物 `setLIntegral_coarea_graph_family`）；
4. 可数覆盖 + 不交拼接，加上余维 m 的加权切片可测性（标量对应物 `OpenSliceMeasurable.lean`），
   得到 `coarea_of_contDiffOn_of_coareaJacobian_ne_zero`。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`、无 `axiom`、无占位。
* `research/audits/VectorRegularChartAudit.lean` 的 **25 条公理报告**只用
  `propext`、`Classical.choice`、`Quot.sound`；
  含零维参数空间、**零维靶空间**（此时每点都正则）、全空间（无有限性）、
  以及 m = 1 退回标量形状的完整链条。
* 重跑全部 **35 个审计客户端**（`research/audits` 28 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**，不变；`research/check_ledger.py` 报 24 个证书。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-17-vector-regular-chart.json`，最终核对另存
  `build/audit/vector-regular-chart/final-snapshot.json`。
