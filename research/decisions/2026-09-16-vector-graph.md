# B1 第一部分：向量值图的 C¹ 基础设施

2026-09-16。本轮**证明新引理**，按余维一文件的结构做余维 m 图面积公式（义务 **B1**）的
**第二、三阶段**。**面积公式本身仍未证明。** 不迁洞，不提交、不推送。
直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T140115.179862Z/report.json`：10 个门、203 个本地模块内核重放、
525 条目。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮未触碰。

## 照搬的结构

`Analysis/AreaFormula.lean`（余维一，957 行）分五个阶段：线性模型 → C¹ 图映射 →
线性逼近 → 两侧估计 → 面积公式。本轮做**第二、三阶段**的余维 m 版本。

## 精确成果

`Analysis/VectorGraph.lean`（本地 import 闭包 8 个模块，**无 WIP**）：

* `vectorGraphMap ι κ γ = fun y => ι y + κ (γ y)`：`K` 值斜率的图映射。
* `graphProj_apply_of_perp`、**`graphProj_vectorGraphMap`**：参数收缩 `ιᵀ` 从图上任一点
  还原参数。**这正是一般路线 A3 缺的那个显式左逆**，而且对**任意**斜率成立。
* **`vectorGraphMap_injective`**：单射，**不需要任何关于 `γ` 的假设**，
  所以没有 `InjOn` 前提，也不必处理重数。
* **`hasFDerivAt_vectorGraphMap`**：导数就是上一轮的 `graphMapLinear ι κ (fderiv ℝ γ y)`，
  所以上一轮算出的体积因子逐点就是对的那个。
* **`approximatesLinearOn_vectorGraphMap`**：导数在球上变化不超过 ε 时，图映射与中心处的
  线性图映射 ε-接近。余维 m 的估计**比余维一更干净**：第二个因子是等距，范数直接消掉，
  不必像余维一那样绕 `innerSL`／梯度。
* `image_vectorGraphMap_eq`、`measurableSet_image_vectorGraphMap`：像是闭条件与收缩原像的交，
  故可测。
* **`hausdorffMeasure_image_graphMapLinear`**：**B1 的线性情形**。
  它直接由 Mathlib 的线性面积公式与上一轮的 `normDet_graphMapLinear` 得到，
  **不需要**余维一文件里那套 shear／dilate 论证（那部分约 160 行）。
* `measurable_vectorGraphJacobian`：沿 `C¹` 斜率的体积因子可测，**消费上一轮的 A1**，
  所以 B1 右端确实是一个 lintegral。

## 本轮没有做的事

* **没有证明面积公式**：余维一文件的第四、五阶段（两侧估计与取极限，约 450 行）
  是 B1 的剩余部分，本轮未做。
* 没有碰路线义务 A2–A5、B2。
* 没有迁洞；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一轮

B1 的第四、五阶段：以 `approximatesLinearOn_vectorGraphMap` 为输入做两侧 Hausdorff 估计
（上界用 Lipschitz 像界，下界用左逆 `ιᵀ` 给出的反 Lipschitz 界——这里正是显式左逆兑现价值的
地方），再按余维一文件的方式取 ε → 0 并拼接可数分片。预计 1–2 轮。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/VectorGraphAudit.lean` 的 20 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`；含余维零、常斜率平坦图、零维参数空间。
* 重跑全部 31 个审计客户端（`research/audits` 24 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-vector-graph.json`，最终核对另存
  `build/audit/vector-graph/final-snapshot.json`。
