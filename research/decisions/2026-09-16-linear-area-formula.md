# 余维 m 纲领第 1 步：归一化线性面积公式与仿射纤维

2026-09-16。本轮**证明新引理**，把 Mathlib 的线性面积公式搬到本仓库的归一化约定下，
并由此识别线性映射纤维上的测度。**本轮不证明任何 coarea 公式，也不证明 C¹ 面积公式**，
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；
起点 passed 回执 `build/verification/20260916T122340.295044Z/report.json`：10 个门、
200 个本地模块内核重放、510 条目，快照
`c0e5cd2924db9e48eb1746067c434f410556f4907d36622c3c8664b4ac86c570`。

## 边界

对数凹 Cheeger–Buser 线（等周常数几种定义的对齐直到与 Poincaré 常数的双向比较，含
`KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，本轮刻意未触碰。

## 为什么需要这一步

Mathlib 的 `LinearMap.hausdorffMeasure_image` 用的是**原始** `μH`；本仓库一切测度都是
`KLS.hausdorffNormalized`，即经典的 `ω_d (diam/2)^d` 归一化。两者差一个常数因子，
而余维 m coarea 公式右端的纤维积分必须是**没有残余常数**的，否则整条公式会带一个
依赖维数的错误因子。本轮就是把这件事做干净。

## 精确成果

`KLS/Geometry/LinearAreaFormula.lean`（本地 import 闭包 8 个模块，**无 WIP**）：

* `hausdorffNormalized_image_linearMap`：
  `hausdorffNormalized V k (L '' s) = ofReal (normDet L) * hausdorffNormalized H k s`，
  `k = finrank ℝ H`。两侧同乘同一归一化常数，故常数消掉，**norm determinant 就是精确的
  体积因子**。
* `adjoint_apply_linearIsometry`：线性等距嵌入的伴随是左逆。
* `normDet_linearIsometry`：线性等距嵌入的 norm determinant 为 **1**。
* `hausdorffNormalized_image_linearIsometry`：等距像保持归一化 k 维测度。
* **`hausdorffNormalized_image_affine`**：平移过的等距切片，其归一化 k 维 Hausdorff 测度
  **精确等于**参数空间上的 Lebesgue 测度，两边都没有残余常数。
* **`hausdorffNormalized_fiber`**：线性映射的纤维是核的平移，按核的维数去量，
  恰好是核上的 Lebesgue 测度。

后两条是余维 m coarea 公式的纤维记账：`L` 满射时核的维数是 `n - m`，
公式右端的内层积分正是在这些纤维上取的。

## 复用而非重造

平移不变性 `Analysis.hausdorffNormalized_image_add_left`、顶维恒等式
`KLS.hausdorffNormalized_finrank_eq_volume` 都是仓库**已证**的结果，本轮直接使用，
没有重证。Mathlib 的 `LinearMap.hausdorffMeasure_image` 同样直接使用。
`normDet_linearIsometry` 由 `normDet_sq` 与等距的伴随左逆性质推出，不走矩阵。

## 本轮没有做的事

* **没有证明任何 coarea 公式**；向量值 coarea 等式仍未证明。
* **没有证明 C¹ 面积公式**：本轮全部关于线性映射与仿射子空间。非线性的局部面积公式
  （Federer 面积公式）仍未证明，也没有列为已达成。
* 没有迁洞：直接洞仍 **8（1/2/5）**；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 纲领的下一步

1. **非线性局部面积公式**：C¹ 参数化的像的 k 维测度等于 `normDet (fderiv)` 的积分。
   仓库已有 C¹ **图**的版本（`Analysis.hausdorffNormalized_image_graphMap`）与
   `RegularChart`/`ImplicitGraph`/`LocalInverse`；一般情形宜经局部图化归到它。
2. 余维 m 正则情形（L9 的类比）：在 `coareaJacobian ≠ 0` 的开集上做纤维图族。
3. 余维 m 临界部分（L10 的类比）与拼接。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/LinearAreaFormulaAudit.lean` 的 14 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`；含顶维一致性（退回已证的
  `hausdorffNormalized_finrank_eq_volume`）、零维参数空间、退化零映射、
  以及满射时 `finrank (ker L) = n - m` 的维数记账。
* 重跑全部 27 个审计客户端（`research/audits` 20 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-linear-area-formula.json`，最终核对另存
  `build/audit/linear-area-formula/final-snapshot.json`。
