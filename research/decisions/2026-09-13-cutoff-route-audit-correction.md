# 距离截断路线与状态勘误

日期：2026-09-13。勘误对象为
[单向 Cheeger 比较记录](2026-09-13-cheeger-infimum-one-sided.md)；保留该历史记录原文，
以下内容及当前 HANDOFF、状态文档取代其中对应的状态与后续路线描述。

## 已核验的状态

`minkowskiConstant_le_smoothConstant` 已证，标准三公理，无传递 `sorryAx`。
`smoothConstant_le_minkowskiConstant` 仍是直接 hole；
`minkowskiConstant_eq_smoothConstant` 已有 `le_antisymm` 证明体，但通过反方向继承 `sorryAx`。
`SmoothDomain.ae_exists_superlevel` 仍是直接 hole，并非已填体；
`Analysis.ae_forall_fderiv_ne_zero` 才是已填体而通过 Sard 继承 `sorryAx`。
直接 hole 总数仍为 13（3／5／5），正式证书仍为 24。

## 距离截断的简化路线

独立客户端 `build/audit/CutoffRouteReview.lean` 已以 `-DwarningAsError=true` 核验：
`IsLocalMax.fderiv_eq_zero`、`IsLocalMin.fderiv_eq_zero` 均无需可微性假设；
`norm_fderiv_le_of_lipschitz` 同样给出逐点界。
原因是 Mathlib 在不可微点将 `fderiv` 和 `gradient` 定义为零。

对非空 B，截断在 closure B 上取全局最大值 1，在增厚外取全局最小值 0，
故这些点的梯度直接为零，包括两个端点水平集；环带内用已有 Lipschitz 上界。
随后可用 `lintegral_mono` 对环带示性函数积分，再用 `measure_sdiff` 和
`Metric.closure_subset_thickening` 得到所需测度差。
这条路线无需 Rademacher、Lebesgue 密度定理或 `hac`，也不需要证明一般水平集梯度结论。
空集单独处理：`Metric.infDist_empty` 使截断恒为 **1**，梯度和目标右端均为零。

本次只核验路线所需的核心 API；`lintegral_enorm_gradient_distanceCutoff_le` 仍未证明。
下一轮保留该目标原声明中的 m、Haar 及 hac 参数，不擅自改动公共接口。
此处关于不可微点的约定不构成一般奇异律比较结果。

本次仅更正文档，不改 Lean 生产源码、不提交、不推送；完整验证以修订后的
`build/verification/latest.json` 为准。
