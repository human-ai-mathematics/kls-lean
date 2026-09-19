# 半群路线：`T` 具体化为加权梯度——对数凹律的热半群

2026-09-19，紧接 [`S7`/`S8` 轮](2026-09-19-generated-semigroup-route.md)。本轮由本会话直接写完（全是一行 `exact` 的转移，无数学内容），不需要证明会话。不 commit、不推送。

## 结果

新模块 `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup.lean`，命名空间 `FunctionalInequalities.KLS.LogConcave`：

| 声明 | 内容 |
| --- | --- |
| `closedWeightedOperator hν m B hi` | `T̄ := (hν.weightedOperator m B hi).closure`，`L²(ν) →ₗ.[ℝ] L²(ν; V)` |
| `closedWeightedOperator_isClosed`、`dense_domain_closedWeightedOperator` | `T̄` 闭（`IsClosable.closure_isClosed`）、稠定（`le_closure` 传稠密性） |
| `heatSemigroup hν m B hi ht` | `P_t = exp(−t T̄†T̄) : L²(ν) →L[ℝ] L²(ν)`，即 `semigroupCLM T̄ … ht` |
| `norm_heatSemigroup_apply_le`、`inner_heatSemigroup_left`、`heatSemigroup_zero_apply`、`heatSemigroup_add_apply`、`continuousOn_heatSemigroup` | 压缩、对称、`P_0 = 1`、半群律、`[0,∞)` 上强连续 |
| `heatSemigroup_generator` | `f ∈ D(T̄†T̄)` ⟹ `(P_t f − f)/t → −T̄†T̄ f` |
| `inner_adjointComp_self_eq` | `⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`，经 `weighted_relaxation_of_mem` 即 `‖B∇g‖²` 的序列松弛：**半群的 Dirichlet 形式就是仓库的闭能量** |
| `intrinsicHeatSemigroup hμ m B ht` | 任意对数凹 `μ` 的内蕴律上的热半群（`hμ.intrinsicMeasure` 全维） |

审计 `research/audits/HeatSemigroupAudit.lean`：13 条 `#print axioms` 全部标准，0 `sorryAx`。模块已进聚合根，`lake build` 3533 jobs 通过。

## 这意味着什么、不意味着什么

`tasks.json` 里 `thm:logconcave-cheeger-poincare-comparison` 的**缺口一**（由闭能量形式生成对称压缩半群）至此对具体算子也关闭了：
对全维对数凹 `ν`（以及任意对数凹 `μ` 的内蕴律），`P_t` 是 `L²(ν)` 上的强连续自伴压缩半群，生成元 `−T̄†T̄`，Dirichlet 形式是 `‖B∇·‖²` 的闭包。
`infrastructure.status` 仍 `missing`：缺口二（Markov 性）、三（Bakry–Émery Γ）、四（小时间热估计）原封未动，节点无 `\leanok`，常数 π 未被触及。

## 一个小摩擦

`heatSemigroup` 是 `def` 而非 `abbrev`，所以转移引理里 `semigroupApply_le _ _ _` 的下划线无法由统一推出 `hd`，
必须显式写 `(hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi) (hν.dense_domain_closedWeightedOperator m B hi)`。

## 下一步

缺口二：Markov 性。交接提示词见 [2026-09-19-markov-handoff-prompt.md](2026-09-19-markov-handoff-prompt.md)。
