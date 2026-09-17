# 面积公式路线 A1：体积因子的连续性与被积函数可测性

2026-09-16。本轮**证明新引理**，完成上一轮路线探查列出的义务 **A1**。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。
**没有证明面积公式，也没有证明任何 coarea 公式。**

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T134934.350358Z/report.json`：10 个门、202 个本地模块内核重放、
521 条目。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮未触碰。

## 为什么 A1 是真义务

Mathlib 有 `LinearMap.normDet` 的完整代数理论，但**没有它对算子的连续性**。
没有这一条，面积公式右端的 `∫⁻ y in s, ofReal (normDet (fderiv ℝ g y))` 连「被积函数可测」
都不成立，等式无从谈起。上一轮路线探查把它列为 A1，风险中、估 60–120 行。

## 精确成果

`Analysis/NormDetContinuity.lean`（本地 import 闭包 2 个模块，**无 WIP**）：

* `normDet_eq_sqrt_det`：`normDet A = √det (Aᵀ ∘L A)`，连续线性映射形式。
* `continuous_adjoint_comp`：`A ↦ Aᵀ ∘L A` 连续（伴随是线性等距，复合是有界双线性）。
* **`continuous_normDet`**：`A ↦ normDet A` 连续。链条是
  伴随连续 → 复合连续 → `ContinuousLinearMap.continuous_det` → `Real.continuous_sqrt`。
* **`measurable_normDet_fderiv`**：`y ↦ normDet (fderiv ℝ g y)` 可测。
* `continuous_coareaJacobian`、`measurable_coareaJacobian_fderiv`：coarea 一侧同理。

## 比路线要求的更强：不需要可微假设

路线里 A1 的可测性写作 `ContDiff ℝ 1 g → Measurable (...)`。实际证出来**不需要任何假设**：
`measurable_fderiv` 对任意函数成立（不可微处 `fderiv` 取零），所以
`measurable_normDet_fderiv (g : H → V)` 对**任意** `g` 成立，路线形式只是丢掉假设的推论。
客户端里对一个处处不可微的函数也记录了这一点。

## 与已证标量理论的一致性

客户端 `scalar_integrand_measurable` 由 `measurable_coareaJacobian_fderiv` 与上上轮的
`coareaJacobian_fderiv` 推出 `x ↦ ‖gradient u x‖` 可测——正是已证 L11/L12/L13 的被积函数。
新的可测性层与标量层是同一件事，不是另起炉灶。

## 路线进度

义务 A1 **已完成**，`research/audits/AreaFormulaRouteStatements.lean` 中 A1 的两条 `#check`
已由 `research/audits/NormDetContinuityAudit.lean` 逐字复述并兑现。
该路线语句文件本身**保持原字节**，作为上一轮的 dated 证据不改写。

仍然开放：**A2**（像侧可数可加性）、**A3**（对单射线性模型的两侧夹逼，一般路线的高风险缺口）、
**A4**（退化部分零测）、**A5**（局部到整体）、**B1**（余维 m 图面积公式，推荐主攻，
估 600–1000 行、2–3 轮）、**B2**（B1 的归一化版本）。下一轮按建议开 **B1**。

## 本轮没有做的事

* **没有证明面积公式**，也没有证明任何 coarea 公式。
* 没有碰 A2–A5、B1、B2；没有迁洞；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/NormDetContinuityAudit.lean` 的 13 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`。
* 重跑全部 30 个审计客户端（`research/audits` 23 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-normdet-continuity.json`，最终核对另存
  `build/audit/normdet-continuity/final-snapshot.json`。
