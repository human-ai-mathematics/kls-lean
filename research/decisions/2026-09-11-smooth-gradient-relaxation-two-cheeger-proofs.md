# 2026-09-11 — `thm:smooth-gradient-relaxation-two-cheeger`：填证明（WIP 模块）

承接 `2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md` 的 26 条 sorry 义务清单。

## 决定

- 在 `formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean` 内完成 21 条义务（#1–#12、#14–#21、#25、#26）。
  未动任何 theorem/def 的陈述（类型），未加 import，未加新的 private 辅助引理以外的声明。
- 保留 5 条 `sorry`，即奇异测度下的开放比较（AGS 2013 Density 型）及其推论：
  `LocalSlope.relaxation_eq_asymptoticLipschitz`（#13）、`Cheeger.energy_eq_ofAsymptoticLipschitz`（#15）、
  `SmoothGradient.relaxation_eq_localSlope`（#22）、`SmoothGradient.relaxation_eq_two_mul_cheeger`（#23）、
  `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger`（#24）。
  注意：#23、#24 本身是纯粹的代数/传输改写，之所以保留 sorry 只是因为它们经 `Functional.ext`/`two_mul_energy`
  归约到 #22；一旦 #22 有证明，二者各是三行。
- 统一清理 `unusedSectionVars`：14 处顶层声明新加 `omit ... in`（文件内合计 20 处）（必须放在 docstring **之前**，否则
  `unexpected token 'omit'; expected 'lemma'`）。该 linter 是逐轮报告的——修掉一批后下一轮才暴露下一批，
  共需 4 轮编译才收敛。
- 模块 docstring 原句"Every proof body is `sorry`"已失真，改为列出仅存的 5 条开放义务。
- 未注册、未提交、未推送；未改动任何共享文件。

## 逐条结果

| # | 名称（省略 `FunctionalInequalities.Energy`） | 状态 | 关键 API |
|---|---|---|---|
| 1 | `AsymptoticLipschitz.apply_const` | 完成 | `iInf_le_of_le`、`le_antisymm _ bot_le` |
| 2 | `AsymptoticLipschitz.apply_eq_zero_of_subsingleton` | 完成 | `Subsingleton.elim` + #1 |
| 3 | `AsymptoticLipschitz.apply_le_of_lipschitzWith` | 完成 | `ENNReal.ofReal_coe_nnreal`、`div_le_iff₀`、`LipschitzWith.dist_le_mul` |
| 4 | `LocalSlope.apply_le_asymptoticLipschitz` | 完成 | `iInf_mono`、`iSup_mono`、`le_iSup₂_of_le x`（取 `z = x`） |
| 5 | `LocalSlope.energy_le_asymptoticLipschitz` | 完成 | `lintegral_mono`、`ENNReal.pow_le_pow_left` |
| 6 | `LocalSlope.Admissible.of_asymptoticLipschitz` | 完成 | `ne_top_of_le_ne_top` + #5 |
| 7 | `LocalSlope.coe_preEnergy_energy` | 完成 | `ENNReal.coe_toNNReal` |
| 8 | `LocalSlope.lowerSemicontinuous_relaxation` | 完成 | `PreEnergy.lowerSemicontinuous_sequentialRelaxation` |
| 9 | `LocalSlope.relaxation_toLp_le` | 完成 | `PreEnergy.sequentialRelaxation_toAmbient_le` + #7 |
| 10 | `LocalSlope.le_relaxation_of_lowerSemicontinuous` | 完成 | `PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous` + #7 |
| 11 | `LocalSlope.relaxation_eq_zero_of_subsingleton` | 完成 | `nonempty_of_isProbabilityMeasure`、`memLp_const`、`Lp.ext`、`MemLp.coeFn_toLp` + #9 |
| 12 | `LocalSlope.relaxation_le_asymptoticLipschitz` | 完成 | `PreEnergy.sequentialRelaxation_comp_le` + #6 + `ENNReal.toNNReal_mono` + #5 |
| 13 | `LocalSlope.relaxation_eq_asymptoticLipschitz` | **有意保留（开放比较）** | — |
| 14 | `Cheeger.two_mul_energy` | 完成 | `ENNReal.mul_div_cancel'` |
| 15 | `Cheeger.energy_eq_ofAsymptoticLipschitz` | **有意保留（开放比较）** | — |
| 16 | `Cheeger.energy_eq_zero_of_subsingleton` | 完成 | #11 + `ENNReal.zero_div` |
| 17 | `SmoothGradient.Test.localSlope_admissible` | 完成 | `ContDiff.locallyLipschitz`、`Test.memLp_two` + #18 |
| 18 | `SmoothGradient.Test.localSlope_energy` | 完成 | `LocalSlope.apply_eq_norm_gradient`（逐点，无测度假设）、`ENNReal.ofReal_pow`、`ofReal_integral_eq_lintegral_ofReal`、`Test.coe_energy` |
| 19 | `SmoothGradient.localSlope_relaxation_le` | 完成 | `PreEnergy.sequentialRelaxation_comp_le` + #17 + #18 + `ENNReal.toNNReal_coe` |
| 20 | `SmoothGradient.relaxation_le_localSlope_of_absolutelyContinuous` | 完成 | `sequentialRelaxation_le_of_recovery_sequences`、`LocalSlope.admissible_iff_memLp_gradient`、`LipschitzApproximation.exists_smooth_weighted_L2`（`B = ContinuousLinearMap.id`）、`Lp.tendsto_Lp_iff_tendsto_eLpNorm''`、`L2.norm_toLp_sq`、`LocalSlope.energy_eq_integral_gradient`、`Tendsto.liminf_eq` |
| 21 | `SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous` | 完成 | `Functional.ext` + `le_antisymm` #20 #19 |
| 22 | `SmoothGradient.relaxation_eq_localSlope` | **有意保留（开放比较）** | — |
| 23 | `SmoothGradient.relaxation_eq_two_mul_cheeger` | **有意保留**（归约到 #22） | — |
| 24 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger` | **有意保留**（归约到 #23） | — |
| 25 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous` | 完成 | `Intrinsic.energy_apply`（两侧）+ #21 + #14 |
| 26 | `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | 完成 | #25 + `LogConcave.intrinsic_absolutelyContinuous Measure.addHaar` |

## 验证

- `lake env lean FunctionalInequalities/Energy/WIP/Cheeger.lean`：无 error，警告恰为 5 条
  `declaration uses 'sorry'`（行 322、366、521、527、541），无 `unusedSectionVars` 等其他警告。
- `lake env lean -DwarningAsError=true FunctionalInequalities/Energy/WIP/Cheeger.lean`：输出恰为同样 5 行
  （sorry 警告被提升为 error），无其他诊断。
- 对 25 条已完成的顶层声明逐个 `#print axioms`：全部为 `[propext, Classical.choice, Quot.sound]`，
  无 `sorryAx`。审计块编译后已从文件移除。

## 缺少的基础设施（不变）

奇异律下 `Lip_a` 松弛 ≤ 斜率松弛（AGS 2013 Density 的核心）仍无仓库输入，Mathlib `db584cd6` 也没有
Hopf–Lax 半群 / weak upper gradient / 度量 Sobolev 空间。可行的欧氏绕道（磨光给出
`SmoothGradient.relaxation ≤ AsymptoticLipschitz.relaxation`，配合 #19 得
`LocalSlope ≤ Smooth ≤ Lip_a`）仍差最后一步，故 #13、#22 保持开放。
