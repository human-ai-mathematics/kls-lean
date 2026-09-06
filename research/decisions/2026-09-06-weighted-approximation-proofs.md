# 加权光滑逼近：四条陈述的语义核对与证明完成

日期：2026-09-06。本记录接续
[statement 交接](2026-09-06-weighted-approximation-statements.md)。任务是核对
`lem:covariance-test-core-density` 四条 Lean 陈述的语义，并在语义正确的前提下完成证明。
本记录不改变 ledger 状态、Blueprint 标签、路线状态或 `tasks.json` 分类；节点仍为
`drafted / checked_by: null`，晋升属于后续验收步骤。

## 语义核对结论

四条陈述的签名与交接批次逐字一致（自动比对通过），未削弱任何结论，未增加任何输入假设。
对照 Blueprint Appendix A 的核对要点：

- `gradient` 是 Mathlib 的 Hilbert 梯度，不可微处为零。`ν ≪ m` 与 Rademacher 定理保证局部
  Lipschitz 函数在 `ν`-a.e. 点可微，因此 `MemLp (fun x ↦ B (gradient g x)) 2 ν` 忠实表达
  `B∇g ∈ L²(ν;V)`。
- 主陈述只要求 `B∇g` 平方可积，`B` 允许零算子和奇异算子；证明中确实没有用到 `∇g ∈ L²`。
- 零维空间包含在量化范围内；证明对 `finrank = 0` 不作特殊处理。
- 步骤 2 与步骤 4 把原函数及原梯度的 `MemLp` 作为结论，由全局 Lipschitz、有界性与概率
  测度推出，与交接记录一致。
- 步骤 4 保留任意闭区间 `[a, b]` 与同一 Lipschitz 常数 `K`；`a = 0, b = 1` 给出 Blueprint 的
  保值域版本。

## 证明结构

模块 `formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean`
现在没有 `sorry`。辅助引理均在同一命名空间中，可复用的有：

- `lipschitzOnWith_of_locallyLipschitz_of_isCompact`：局部 Lipschitz 实函数在紧集上全局 Lipschitz
  （有限子覆盖加 Lebesgue 数引理）。
- `ae_differentiableAt_of_locallyLipschitz`：局部 Lipschitz 函数关于 Haar 测度 a.e. 可微
  （闭球穷竭加 McShane 延拓，归约到 Mathlib 的 `LipschitzWith.ae_differentiableAt`）。
- `tendsto_eLpNorm_zero_of_dominated`：`0 < p < ∞` 时 `eLpNorm` 的控制收敛定理。
- `gradient_scaled_mul`：截断与可微点处函数乘积的梯度公式。

分析部分：固定 bump `bump`（半径 1 处为一，半径 2 外为零）缩放得到截断 `scaled R` 与
归一化核 `kernel m R`；`mollify m R g = g ⋆ kernel m R` 光滑、保持 Lipschitz 常数、保持
上下界与紧支撑，并且 `‖mollify − g‖ ≤ 2 K R`。梯度逐点收敛不经过弱导数或 Lebesgue
微分定理：在可微点用仿射模型 `g x + L (· − x)` 比较，仿射函数的卷积导数恒等式
`integral_affine_smul_fderiv_kernel` 由 Mathlib 的卷积导数公式与导数唯一性得到，余项由
`C₀ m`（核导数质量的尺度无关常数）控制。截断步骤用 `‖g‖` 与 `‖B∇g‖ + ‖B‖ M ‖g‖` 作为
控制函数；主定理对步骤 1、2 作对角选取。

## 本地检查记录

Git HEAD：`70ca1c19c4d207a31716c2e589c0b096521a5490`，工作树含此前未提交修改。

| 检查 | 实际结果 |
| --- | --- |
| `lake build`（在 formalization 下） | 通过，3253 jobs；本模块与 solutions 入口均无 warning |
| `solutions/LemCovarianceTestCoreDensity.lean` 中四条 `#print axioms` 的 `#guard_msgs` | 通过，传递公理恰为 `propext`、`Classical.choice`、`Quot.sound` |
| `grep -w sorry\|admit` 于本模块与入口文件 | 无匹配 |
| `python3 research/check_ledger.py` | 通过，7 节点 |
| `python3 research/check_blueprint.py` | 通过，86 标签、4 条活动路线 |
| `python3 research/atlas.py check` | 通过，73 节点、6 证书、无环 |
| `python3 -m unittest discover -s research/tests` | 97 项通过 |
| `python3 research/statement_snapshot.py check` | 通过，26 个声明与 golden 一致 |

没有运行 `verify.py`、leanchecker 重放、隔离重建或远端 CI；没有 commit/push。

## 后续步骤（未在本记录中执行）

1. 按 ledger 契约为节点建立 `certificate` 并将 `lem:covariance-test-core-density` 由
   `drafted` 晋升为 `proved / checked_by: lean`，需要人工验收。
2. 更新 `tasks.json` 中该节点的 `note` 与 `infrastructure.status`（当前仍记为 missing 与
   "proof placeholders"），并为 Blueprint 节点补 `\lean{}` / `\leanok` 锚点。
3. 运行 `verify.py` 生成绑定当前源码快照的验证收据。
