# B1 第四阶段：向量值图的两侧夹逼估计

2026-09-16。本轮**证明新引理**，完成余维 m 图面积公式（义务 **B1**）的**第四阶段**，
外加第五阶段所需的逼近分片。**面积公式本身仍未证明。**
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`；起点 passed 回执
`build/verification/20260916T143055.790878Z/report.json`：10 个门、204 个本地模块内核重放、
529 条目。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮未触碰。

## 精确成果

`Analysis/VectorGraphSandwich.lean`（本地 import 闭包 9 个模块，**无 WIP**）：

* **`norm_add_sq_of_perp`**：`‖ι y + κ z‖² = ‖y‖² + ‖z‖²`。两个嵌入值域正交，
  所以跨因子的勾股关系成立。这是本轮所有估计的共同来源。
* `norm_sub_vectorGraphMap_sq`、**`norm_sub_le_norm_sub_vectorGraphMap`**：
  图映射**从不把点拉近**。这正是一般路线要从它没有的逆映射里去取的下界输入。
* `norm_le_norm_graphMapLinear`、`injective_graphMapLinear`：线性模型同样扩张、单射。
* **`hausdorffMeasure_image_vectorGraphMap_le`**（上界）与
  **`le_hausdorffMeasure_image_vectorGraphMap`**（下界）：与线性模型 ε-接近的图映射，
  其像的 k 维测度与线性像在 `(1+ε)^k` 因子内两侧夹住。
* **`exists_approximating_partition_vectorGraph`**：H 的可数可测分片，每片上图映射被
  某个线性图映射 ε-逼近且导数与该斜率 ε-接近。这是第五阶段的输入。

## 复用而非重造

两个方向都归结到同一条通用比较 `Analysis.hausdorffMeasure_image_le_of_norm_le`——
它是余维一文件里已证的、**与图无关**的引理，本轮直接复用，没有重证。
线性情形的面积公式则由 Mathlib 的线性面积公式给出。

## 本轮没有做的事

* **没有证明面积公式**：第五阶段（`ε → 0` 的极限与可数分片拼接，余维一文件里约 280 行）
  未做。客户端里的 `exact_at_zero` 只是把两侧估计在 `ε = 0` 处夹死，
  **那是夹逼退化正确，不是面积公式**。
* 没有碰路线义务 A2–A5、B2。
* 没有迁洞；没有碰尖锐 Sard、两条 Cheeger 比较、Energy 的五个洞。
* 没有扩大证书或 Blueprint `leanok` 范围。
* **没有提交、没有推送**，真实 Git index 未改动。

## 下一轮：B1 的最后一步

以本轮的分片与两侧估计为输入，按余维一文件的 `graphMap_estimates`（132 行）与最终装配
（148 行）的方式取 `ε → 0`。需要的极限引理 `tendsto_aux`、`tendsto_aux'` 在余维一文件里
已是**与图无关**的通用引理，应可直接复用，所以余下工作量估计小于余维一的 280 行。

## 验证

* 新模块与新客户端均以 `-DwarningAsError=true` 编译通过，无 `sorry`。
* `research/audits/VectorGraphSandwichAudit.lean` 的 15 条公理报告只用
  `propext`、`Classical.choice`、`Quot.sound`。
* 重跑全部 32 个审计客户端（`research/audits` 25 个，`build/audit` 7 个），全部严格通过。
* 三个 WIP 逐个编译，直接洞 **1/2/5，总数 8**，不变。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 通过；证据 JSON 为
  `research/explorations/2026-09-16-vector-graph-sandwich.json`，最终核对另存
  `build/audit/vector-graph-sandwich/final-snapshot.json`。
