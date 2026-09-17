# 余维 m 纲领第 2 步（线性层）：任意余维的图 Jacobian

2026-09-16。本轮**证明新引理**，给出任意余维图映射的体积因子，并把仓库已证的余维一
`graphJacobian` 与 Mathlib 的 `normDet` 对接。**本轮不证明面积公式，也不证明任何 coarea
公式**，不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；
起点 passed 回执 `build/verification/20260916T124243.885687Z/report.json`：10 个门、
201 个本地模块内核重放、514 条目，快照
`a4ae471ae89cf4112376538ba0e54b7be6baaae2e3b96bfee329c87190998cc1`。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮刻意未触碰。

## 查清的事实：仓库的面积公式只覆盖余维一

`Analysis/AreaFormula.lean` 的图映射是 `y ↦ ι y + g y • e`，**`g` 是实值**；线性模型是
`graphLinear ι e a v = ι v + ⟪a, v⟫ • e`，体积因子 `graphJacobian a = √(1 + ‖a‖²)`。
这是**余维一**。余维 m 的纤维需要 `K` 值斜率（`dim K = m`），仓库没有。
所以上一轮设想的「把一般 C¹ 面积公式局部化归到已有图公式」只在 m = 1 成立；
一般 m 必须先有余维 m 的图模型。本轮就补这一层。

## 精确成果

`Analysis/GraphJacobian.lean`（本地 import 闭包 6 个模块，**无 WIP**）：

* `graphMapLinear ι κ A = ι + κ ∘ A`：斜率 `A : H →L[ℝ] K`、两个正交值域等距嵌入下的
  线性图映射，`K = ℝ` 时即 `graphLinear`。
* **`adjoint_comp_graphMapLinear`**：图映射的 Gram 算子是 `1 + Aᵀ A`，**在参数空间 H 上**。
  两个等距各贡献恒等，交叉项因值域正交而为零。
* `normDet_graphMapLinear_sq`：`normDet² = det (1 + Aᵀ A)`（无平方根，不需要正性论证）。
* **`normDet_graphMapLinear`**：`normDet = √det (1 + Aᵀ A)`。这是**任意余维**的体积因子，
  是参数空间上的行列式，**与环境嵌入无关**。
* **`normDet_graphLinear`**：`normDet (graphLinear ι e a) = graphJacobian a`。

## 余维一的对接为什么重要

最后一条把仓库自己的 `graphJacobian` 与 Mathlib 的 `normDet` 认成同一个数，
从而**已证的余维一面积公式就是一般体积因子在 m = 1 的情形**，两套框架一致。
证明不走行列式：仓库已证的线性余维一面积公式与 Mathlib 的线性面积公式描述同一个映射的
伸缩因子，而线性映射的体积因子唯一（存在正测度有限的集合），两者相等。
这样绕开了秩一行列式引理。

## 本轮没有做的事

* **没有证明面积公式**：全部关于线性映射。非线性的 Federer 面积公式仍未证明。
* **没有证明任何 coarea 公式**。
* 没有迁洞：直接洞仍 **8（1/2/5）**；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一步的确切目标已钉住

`research/audits/GraphJacobianAudit.lean` 末尾用 `#check` 记录了下一轮要证的命题
（**只是命题类型检查，不是证明**，与 `WeightedCoareaRouteStatements.lean` 同一惯例）：

```lean
∀ {H V} [...] {g : H → V} {s : Set H}, ContDiff ℝ 1 g → Set.InjOn g s → MeasurableSet s →
  μH[finrank ℝ H] (g '' s) = ∫⁻ y in s, ENNReal.ofReal (normDet (fderiv ℝ g y))
```

即单射 C¹ 参数化的 Federer 面积公式。它仍然未证明，本轮不把它计作已达成。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/GraphJacobianAudit.lean` 的 11 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`；含平坦图、余维零（subsingleton 目标）、
  零维参数空间等边界客户端。
* 重跑全部 28 个审计客户端（`research/audits` 21 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-graph-jacobian.json`，最终核对另存
  `build/audit/graph-jacobian/final-snapshot.json`。
