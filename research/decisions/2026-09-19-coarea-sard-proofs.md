# 尖锐 Sard 证毕、Lipschitz 与局部 Lipschitz 向量 coarea 证毕：三条同日路线一并兑现

2026-09-19，**实现轮**，紧随同日三轮路线探查。三个证明会话（各对应一条路线）在互不相交的新文件上并行工作，
本会话负责整合。结果：

* **尖锐有限正则 Sard**：`Analysis.sard` 证出（`Analysis/Sard/Sharp.lean`，Morse 路线），与推论
  `Analysis.ae_forall_fderiv_ne_zero` 一起以**逐字节相同的 `pp.all` 签名**从 `KLS/WIP/AnalyticPrerequisites.lean`
  迁入，该 WIP 文件清空并删除（原文冻结于 `build/audit/sharp-sard-proofs/AnalyticPrerequisites.before.lean`，
  前后 `pp.all` 打印各存一份并 `diff` 为空）。
* **Lipschitz 向量 coarea**：`Analysis.coarea_of_lipschitz`（`L0`）证出，`L0 = V5 ∘ V1`。
* **局部 Lipschitz 向量 coarea**：`Analysis.coarea_of_locallyLipschitz`（`N0`）证出，`N0 = X5 ∘ L0`。
  向量 coarea 链 `C¹ → Lipschitz → 局部 Lipschitz` 与标量侧齐平。

直接洞由 **8（1/2/5）降为 7（0/2/5）**；证书仍 **24**（这些是 `Analysis/` 层结论，不是 ledger 节点）。
不提交、不推送，真实 Git index 未改动。

起点 `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`；起点 passed 回执
`build/verification/20260918T122459.920890Z/report.json`（局部 Lipschitz 路线轮的最终回执）：
10 个门、224 个本地模块内核重放、623 条目，快照 `dc29c5d9cec95e192d4543b47bada4b3bc5bf40bee3d8366f2540e51e1154818`。起点 drift 为空。

## 边界

对数凹 Cheeger–Buser 线（含 `KLS/WIP/CheegerInfimum.lean` 剩下的两个洞）归合作者**王浩丞**，未触碰
（该文件字节不变；`KLS/WIP/` 目录现只剩它）。Energy 的五个洞、无量纲 KLS 未触碰。
不新增证书、不扩大 Blueprint `leanok` 范围、不新增兼容 alias、不重述既有定理、不削弱已证结论。

## 三个证明会话的规则与产出

规则：只新建文件、不改既有文件；不 `lake build`、不 `verify.py`、不改 Git 状态；只用
`lake env lean -DwarningAsError=true` 检查；不 import WIP；不用 `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`；
每条路线命题在审计客户端里**逐字复述**并 discharge。三个会话都遵守了（整合时逐项核对 `git status`）。

| 路线 | 新库模块（行） | 审计客户端（行） | 兑现 |
| --- | --- | --- | --- |
| 尖锐 Sard | `Analysis/Sard/Chart.lean` 220、`Disk.lean` 188、`MorseVanishing.lean` 337、`Sharp.lean` 125（+13 迁入） | `SharpSardAudit.lean` 240 | `M1`、`M1'`、`M3`–`M6`、`D1`；**`M2` 按字面为假**，见下 |
| Lipschitz 向量 coarea | `Analysis/Lipschitz/Componentwise.lean` 88、`Refinement.lean` 77、`VectorPieces.lean` 75、`VectorCoarea.lean` 158 | `LipschitzVectorCoareaAudit.lean` 294 | `L0`、`V1`–`V5`、`V4'`、`V4''`、`M1`；整合时加 `route_M2` |
| 局部 Lipschitz 向量 coarea | `Analysis/Lipschitz/Extension.lean` 61、`Annuli.lean` 63、`Local.lean` 158（+18 整合 `N0`） | `LocallyLipschitzVectorCoareaAudit.lean` 223 | `X1`–`X5`、`D1`、`C1`、`C2`；整合时加 `route_N0` |

**`M2` 按字面为假。** 尖锐 Sard 路线的中值步骤 `M2` 只在曲线上控制 `fderiv f`，结论却按弦长度量；
证明会话给出笔算反例（`C¹` 螺线 `t ↦ (t³cos(1/t), t³sin(1/t))`，`S` 取无穷多个尺度上的交点），
路线记录里「不需要反 Lipschitz 常数」的判断是错的。加上盘的反 Lipschitz 界之后的版本
`route_M2_antilipschitz` 已证，而 Morse 分解的每个盘都带这个界，`M3`–`M6` 因此不受影响。
反例未形式化；路线语句文件保持字节不变，修正记在路线记录的附记里。

**其余实现细节。** `M1` 要求全局 `C^k` 的 `θ`，而 `ContDiffAt.to_localInverse` 只给局部逆，
于是补了有限阶的 bump 延拓 `MorseSard.exists_contDiff_eventuallyEq_nat`。`V3` 用单射 `(Fin m → ℕ) ↪ ℕ`
而非等价（`m = 0` 时 `Fin 0 → ℕ` 是单点）。`M1` 的反例需要宇宙多态见证
`EuclideanSpace ℝ (ULift (Fin 1))`。`X1` 是逐坐标 McShane（`LipschitzOnWith.extend_pi` 经 `PiLp` 搬运，
常数 `√m · K`），不是 Kirszbraun，对常数不作声称。`X5` 的库形式省去了从未用到的维数关系，
审计里的逐字版本保留并丢弃它。

## 整合动作

1. 清理 `.lake` 中无对应源码的 213 组孤儿构建产物（旧构建残留，曾遮蔽同名新模块）。
2. `Sharp.lean` 追加 `ae_forall_fderiv_ne_zero`（原文照搬）；`Local.lean` 追加 `coarea_of_locallyLipschitz`
   （`X5` 用于 `L0`）；两个 coarea 审计客户端追加 `route_N0` / `route_M2`。
3. 删除 `KLS/WIP/AnalyticPrerequisites.lean`；五个曾 import 它的客户端
   （`research/audits` 的 `LipschitzCoareaMigrationAudit`、`LevelSetMeasurableAudit`、`IsoperimetryCoareaAudit`；
   `build/audit` 的 `LevelSetMeasurableAudit`、`AreaFormulaImportReview`）改为 import `Analysis.Sard.Sharp`，加日期附记。
   后两者是历史客户端，不在 7 个活客户端之列；`build/audit/LevelSetMeasurableAudit.lean` 在本轮之前就已过期
   （它引用早已迁走的 `T2` 原位置），本轮只改其 import，不修其内容。
4. 聚合导入加入 `Analysis.Lipschitz.VectorCoarea`、`Analysis.Lipschitz.Local`、`Analysis.Sard.Sharp`，
   并补一段说明；五处库模块 docstring 里「尖锐 Sard 仍是直接洞」的现在时表述改为指向 `Sharp.lean`
   （`Analysis/Sard/Smooth`、`Analysis/Divergence`、`KLS/Geometry/RegularSuperlevel`、`LevelSetMeasurable`、`IsoperimetryCoarea`）。
5. 默认 `lake build`（3492 个作业）通过；`pp.all` 前后 `diff` 为空；`check_ledger.py` 24 个证书 0 错误。

## 明确没证什么

* 向量值靶的 Sard（`C^(n−m+1)`）、临界值的 Hausdorff 测度、Whitney 的 `C^(n−1)` 反例：未证。
* `M2` 的反例：未形式化。`X1` 的常数：无最优性。定义域：仍是整个空间。
* Cheeger 两洞归王浩丞，Energy 五洞未触碰；无量纲 KLS 仍开。不迁其它洞、不新增证书。

## 验证

默认 `lake build`（3492 个作业）通过。全部 **58** 个审计客户端（`research/audits` 51 个 + `build/audit` 7 个活客户端）以 `-DwarningAsError=true` 重跑，**0 失败**；**732 条公理报告，5 条 `sorryAx`**，全部是 `IsoperimetryCoareaAudit` 与 `LipschitzCoareaMigrationAudit` 故意报告的 `KLS/WIP/CheegerInfimum.lean` 两个洞。剩余两个 WIP 模块逐个编译，`sorry` 警告 `2 + 5 = 7`，直接洞 **7（0/2/5）**。`pp.all` 前后 `diff` 为空。`check_ledger.py` **24** 个证书 0 错误。根目录 `python3 research/verify.py` 于本轮结束时重跑，最终回执记于 `build/audit/coarea-sard-proofs/final-snapshot.json`，快照与工作区逐条重算，drift 为空。
详见 `research/explorations/2026-09-19-coarea-sard-proofs.json` 与 `build/audit/coarea-sard-proofs/`。
