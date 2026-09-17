# 余维 m coarea 的线性代数层：coarea Jacobian

2026-09-16。本轮**证明新引理**，建立 `Analysis.coareaJacobian` 及其基本理论，作为
**向量值（余维 m）coarea 纲领的第一轮**。**本轮不证明任何 coarea 公式**，不迁洞，
不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`，`origin/main` 同；
起点 passed 回执 `build/verification/20260916T120611.840573Z/report.json`：10 个门、
199 个本地模块内核重放、506 条目，快照
`edbda70a4b2d1c0fa48ceabdaa0a88c1d5daa66cc6dcff34e9e14a017aff9762`。

注意起点 HEAD **不再是** `dcc158d`：并发会话提交了 `34b9269 docs: add KLS literature map
through July 2026`（纯文档，未推送）。本轮不碰它的内容。

## 边界

对数凹 Cheeger–Buser 线（等周常数几种定义的对齐直到与 Poincaré 常数的双向比较，含
`KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，本轮刻意未触碰。

## 关键发现：Mathlib 已有矩形体积因子

`Mathlib/Analysis/InnerProductSpace/NormDet.lean` 已经给出
`LinearMap.normDet f = √det(fᵀ ∘ f)`（"norm determinant"），并且已证
`normDet_sq`、`normDet_nonneg`、`normDet_eq_prod_singularValues`、
`normDet_eq_zero_iff_ker_ne_bot`，以及**它就是 Hausdorff 测度的体积因子**
（`LinearMap.hausdorffMeasure_image`）。

`normDet` 是**面积**公式的 Jacobian（从有限维空间出发的映射）。coarea Jacobian 是它的伴随
对偶：`coareaJacobian L = normDet Lᵀ`。本轮据此定义，而**不是**重新推导行列式理论。
这意味着余维 m 纲领的线性代数层基本不用自己造。

## 精确成果

`Analysis/CoareaJacobian.lean`（**只依赖 Mathlib**，本地 import 闭包只有它自己）：

```lean
def coareaJacobian (L : V →L[ℝ] W) : ℝ :=
  LinearMap.normDet (LinearMap.adjoint (L : V →ₗ[ℝ] W))
```

* `coareaJacobian_nonneg`。
* `coareaJacobian_sq`：`J² = det (L ∘ₗ Lᵀ)`，行列式在**目标**上，所以是 `m × m` 的 Gram
  行列式，不是 `n × n` 的。这是定义性质。
* `adjoint_one`：实值泛函的伴随把 `1` 送到 Riesz 代表元。
* `coareaJacobian_eq_norm_toDual_symm`：实值泛函的 coarea Jacobian 是其 Riesz 代表元的范数。
* **`coareaJacobian_fderiv`**：`coareaJacobian (fderiv ℝ u x) = ‖gradient u x‖`。
* `ker_adjoint`：`ker Lᵀ = (range L)ᗮ`。
* `coareaJacobian_eq_zero_iff` / `coareaJacobian_ne_zero_iff`：
  **`J ≠ 0 ↔ L 满射`**。这是余维 m 公式要分裂的正则集，`W = ℝ` 时退化为梯度非零。

## 为什么 `coareaJacobian_fderiv` 是本轮的重点

它说明**已经证明并审计过的标量理论就是本密度的 `m = 1` 情形**：L11/L12/L13 的被积函数
`‖gradient u x‖` 逐点等于新定义的 coarea Jacobian。因此后续余维 m 的工作不需要改写、
重述或削弱任何既有结论，标量链条原样保留。这条兼容性是证出来的，不是宣称的。

## 本轮没有做的事

* **没有证明任何 coarea 公式**，向量值 coarea 等式仍未证明，也没有列为已达成。
* 没有做降维映射的面积公式、余维 m 的 L1–L12、也没有余维 m 的隐函数正规形。
* 没有迁洞：直接洞仍 **8（1/2/5）**；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一步（纲领内，未承诺时间）

1. 降维映射的面积公式：把 `LinearMap.hausdorffMeasure_image` 提升到 C¹ 映射的局部版本。
2. 余维 m 的正则情形（L9 的类比）：在 `J ≠ 0` 的开集上用带参数隐函数定理做纤维图族。
3. 余维 m 的临界部分（L10 的类比）与拼接。
标量情形走完 L1–L13 用了约十轮；本纲领不承诺更快。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/CoareaJacobianAudit.lean` 的 17 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`；含恒等映射、零映射、subsingleton 目标
  和 `EuclideanSpace ℝ (Fin 2)` 上的正交投影等边界客户端。
* 重跑全部 26 个审计客户端（`research/audits` 19 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，与上一轮一致。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-coarea-jacobian.json`，最终核对另存
  `build/audit/coarea-jacobian/final-snapshot.json`。
