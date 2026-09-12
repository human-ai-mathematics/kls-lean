# 2026-09-11 — 交给证明会话的提示词：填 `KLS/WIP/RelativePerimeter.lean` 与 `Energy/WIP/Cheeger.lean` 的 sorry

以下两段提示词可直接复制给另一个模型/会话。第一段是本日 `lem:relative-perimeter-smoothing` 骨架的义务；
第二段是同日 `thm:smooth-gradient-relaxation-two-cheeger` 骨架中可用现有输入证明的义务。

---

## 提示词 A：`lem:relative-perimeter-smoothing`

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交 db584cd6d46c92f209a44c0f1c829460d327499d；
Lake 根目录 formalization/）。

任务：填写 formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean 中的 sorry。该文件是
Blueprint 节点 lem:relative-perimeter-smoothing（formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex，
"Relative perimeter without carrier-boundary charges" 一节）的陈述骨架；设计与逐句对齐见
research/decisions/2026-09-11-relative-perimeter-smoothing-statement.md。先读这两个文件和目标 .lean 的模块文档。

规则：
1. 不改任何 theorem/def 的陈述（类型）。若某条陈述你确认为假或不可证，不要改它：在报告里说明反例/障碍并保留 sorry。
   允许在同文件加 private 辅助引理，允许加 import。
2. 命名遵守 research/naming.md（短名不重复命名空间；辅助引理 private）。
3. 只在这个 WIP 文件内工作。不要把它加进 formalization/FunctionalInequalities.lean、lakefile 的 Solutions 根、
   research/a-series/ledger.yaml、research/check_blueprint.py、research/tasks.json、Blueprint \lean{}/\leanok。
   不 git commit、不 git push。决定/探索记录只追加（新建 research/decisions/2026-09-1X-relative-perimeter-smoothing-proofs.md）。
4. 编译命令（在 formalization/ 下）：
     lake env lean FunctionalInequalities/KLS/WIP/RelativePerimeter.lean
   目标：无错误；填完的声明不再出现 "declaration uses 'sorry'"；无 unusedSectionVars 等其他警告
   （不用的 section 变量加 `omit ... in`，需要的加 `include ... in`）。全部完成后用
     lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/RelativePerimeter.lean
   并对每个填完的顶层定理运行 #print axioms，只允许 propext / Classical.choice / Quot.sound。
5. 语法提示：`∞`（ContDiff 阶）需要 `open scoped ContDiff`；`push_neg` 已废弃，用 `push Not` 或 `not_le.mp`；
   `μH[d]` 是 `open MeasureTheory` 下的 scoped 记法；Hausdorff 测度缩放引理要求 `0 ≤ d`，`finrank = 0` 时另行处理
   （边界为空）。

按下面顺序做，先易后难；做不动的留 sorry 并写明卡点。

第一层（纯 Mathlib，应全部完成）
- SmoothDomain.empty / SmoothDomain.univ 的 exists_defining：`frontier_empty`、`frontier_univ`，前提为空，`simp`。
- SmoothDomain.measurableSet：`U.isOpen.measurableSet`。
- relativePerimeter_eq_zero_of_frontier_eq_empty：`h ▸ Set.empty_inter`，`Measure.restrict_empty`，`lintegral_zero_measure`。
- SmoothDomain.frontier_inter_eq：⊆：y ∈ frontier ∩ W，若 φ y < 0 则 y ∈ U ∩ W 开集，与 y ∉ interior 矛盾；
  若 φ y > 0 则邻域上 φ > 0（连续），与 y ∈ closure U 矛盾。⊇：φ y = 0，fderiv ≠ 0 给方向 v 使 fderiv φ y v < 0
  （取 v = −(fderiv φ y).symm 方向或用 `ContinuousLinearMap.exists_ne_zero`），沿 y + t v 用 `HasFDerivAt` 的
  一阶展开（`hasFDerivAt_iff_isLittleO` 或 `HasFDerivAt.lim`）得到小 t>0 时 φ < 0（∈ U）、t<0 时 φ > 0（∉ U），
  故 y ∈ closure U 且 y ∉ interior U。
- SmoothDomain.homothety 的 isOpen / exists_defining：位似 `AffineMap.homothety a c`（c ≠ 0）是同胚：
  `AffineEquiv.homothetyUnitsMulHom a (Units.mk0 c hc)` 给 AffineEquiv，连续性 `AffineMap.homothety_continuous`
  （或写成 `x ↦ c • (x − a) + a` 用 `Homeomorph.smulOfNeZero`、`Homeomorph.addRight`）。开集像：`Homeomorph.isOpenMap`。
  定义函数：取 W' = h '' W，φ' = φ ∘ h.symm（`ContDiff.comp` 与仿射映射的 `contDiff`），fderiv 用链式法则
  `fderiv_comp` 与 `(h.symm)` 的导数可逆。
- SmoothDomain.indicator_homothety：`Set.indicator_apply`，x ∈ h '' U ↔ h⁻¹ x ∈ U（`AffineEquiv.image_eq_preimage`
  或 `Set.mem_image_equiv`），`AffineMap.homothety` 的逆是比例 c⁻¹ 的位似（`AffineMap.homothety_mul`、`homothety_one`）。
- IsBorellDensity.le_rpow_mul_of_combination：由 `h.logConcave x b s hs₀ hs₁`（注意字段的参数顺序与 t•x + (1−t)•y 形式）
  得 ρ x ^ s * ρ b ^ (1−s) ≤ ρ y。若 ρ x = 0 平凡。否则 ρ x ^ s ≤ ρ y / b₀^{1−s}，两边 1/s 次方：
  `Real.rpow_le_rpow`、`Real.rpow_natCast`、`Real.rpow_mul`、`Real.div_rpow`，再 ρ y^{1/s} = ρ y · ρ y^{(1−s)/s}
  ≤ ρ y · M^{(1−s)/s}（`Real.rpow_le_rpow_left_iff`/`Real.rpow_le_rpow`，用 hM y）。所有底数非负（`h.nonneg`）。
- RelativePerimeter.tendsto_indicator_homothety：`tendsto_lintegral_of_dominated_convergence` 以常数 1 为控制
  （`ν` 有限），逐点：x ∈ U 时 `AffineMap.homothety a c x → x`（c → 1，`Continuous.tendsto`，
  `AffineMap.homothety_apply`，`one_smul`），开集 ⇒ 最终在 U，差为 0；x ∉ closure U 同理最终不在 U；
  frontier 用 `hfr` 排除（`ae` 形式：`compl_mem_ae_iff.mpr hfr`）。

第二层（用现有仓库输入 + Mathlib，应能完成）
- SmoothDomain.hausdorff_frontier_homothety：同胚保边界 `Homeomorph.image_frontier`（Topology/Homeomorph/Defs.lean:315），再 `MeasureTheory.Measure.hausdorffMeasure_homothety_image (hd : 0 ≤ d) a hc s`
  （Mathlib/MeasureTheory/Measure/Hausdorff.lean:1051，形如 `μH[d] (homothety x c '' s) = ‖c‖₊ ^ d • μH[d] s`）。
  d = finrank − 1 < 0 当且仅当 finrank = 0：此时 `Subsingleton V`（`Module.finrank_zero_iff`），frontier 为空，两边 0。
- IsBorellDensity.exists_le：(i) 内部支撑非空：`h.convex_pos` 给 {ρ>0} 凸；ν 是概率且 ν = m.withDensity ρ，
  故 m {ρ>0} > 0；凸集 Haar 正测 ⇒ 内部非空（`Convex.interior_nonempty_iff_affineSpan_eq_top` 与
  `MeasureTheory.Measure.addHaar_affineSubspace`（真仿射子空间零测））。(ii) 取 a ∈ interior ν.support、
  closedBall a r ⊆ interior（`Metric.isOpen_iff`），`h.exists_bounds_of_isCompact (isCompact_closedBall a r)` 给 b₀>0。
  (iii) 对任意 x：z ∈ ball ((a+x)/2) (r/2) 写成 z = (1/2)•x + (1/2)•b，b ∈ ball a r，
  `h.logConcave x b (1/2)` 给 ρ z ≥ √(ρ x · b₀)；积分：1 = ν univ ≥ ν(ball) = ∫_{ball} ρ dm ≥ √(ρ x b₀) m(ball(·, r/2))
  （`withDensity_apply`、`setLIntegral_mono`、`Metric.measure_ball_pos`（`IsAddHaarMeasure` 蕴含 `IsOpenPosMeasure`）），解出 ρ x ≤ 1/(b₀ m(ball 0 (r/2))²)。
- SmoothDomain.mollifiedIndicator_contDiff_lipschitz_mem_Icc：把 `mollifiedIndicator` 认成卷积
  `(φ.normed m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] 𝟙_U`（`MeasureTheory.convolution` 定义展开为 ∫ f (x − y) g y，
  注意 Mathlib 约定是 `∫ t, L (f t) (g (x − t))`，需 `convolution_flip`/`convolution_eq_swap` 调整）。
  光滑：`HasCompactSupport.contDiff_convolution_left` 与 `φ.hasCompactSupport_normed`、`φ.contDiff_normed`，
  `𝟙_U` 局部可积（有界可测）。Lipschitz：导数 = (∇η) ⋆ 𝟙_U，范数 ≤ ∫‖∇η‖ dm（`HasCompactSupport.hasFDerivAt_convolution_left`），
  再 `lipschitzWith_of_nnnorm_fderiv_le`。[0,1]：`φ.nonneg_normed`、`φ.integral_normed`、`integral_mono`，被积 ≤ η(x−·)。

第三层（缺基础设施，尽力而为；卡住就留 sorry 并写清楚）
- SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier 与 SmoothDomain.addHaar_frontier：
  思路：由 frontier_inter_eq，边界局部是 {φ = 0} ∩ W，fderiv ≠ 0 ⇒ 隐函数定理（`HasStrictFDerivAt.implicitFunction`，
  Mathlib/Analysis/Calculus/Implicit.lean）把它写成 C¹ 图像；图像是 Lipschitz 像（`LipschitzOnWith`），
  `LipschitzOnWith.hausdorffMeasure_image_le` 给 μH[n−1](紧片) ≤ K^{n−1} μH[n−1](ℝ^{n−1} 中紧集) < ∞
  （需 `hausdorffMeasure_pi_real` 或 EuclideanSpace 上 μH[n−1] 与 volume 的比较）；Haar 零测：图像在乘积测度下
  切片为单点（`Measure.prod_apply` + `measure_singleton`）。紧覆盖后局部有限 ⇒ 用 `IsLocallyFiniteMeasure` 的定义。
- SmoothDomain.enorm_gradient_mollified_le（Gauss–Green 推论）：对固定 x，∇_x ∫ η(x−y) 𝟙_U(y) dy = ∫_U ∇η(x−y) dy
  = −∫_U div_y[η(x−y)] dy；把 U ∩ supp η(x−·) 用有限个定义邻域覆盖并做单位分解，在每个图像坐标块上用一维分部积分
  （沿法向坐标，`intervalIntegral.integral_eq_sub_of_hasDerivAt`）加 Fubini，得边界项 ∫_{∂U} η(x−y) n(y) dH^{n−1}；
  取范数。Mathlib 的 `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` 只对盒子，
  因此要么在图像坐标下先做坐标变换到盒子（`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`），
  要么直接做一维分部积分 + Fubini。这是本节点最重的义务。
- RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le：给定上两条后：逐点用 enorm_gradient_mollified_le
  于 U' := U.homothety a (1/s)，`lintegral_mono`，`lintegral_lintegral_swap`（Tonelli，需 μH 限制在 ∂U' 上 σ-有限：
  由局部有限 + 第二可数），对每个 y' ∈ ∂U' 用 `φ.integral_normed`-型的 ∫ η(x − y') dm(x) = 1 但带权 ρ x：
  当 η(x−y') > 0 时 ‖x−y'‖ < φ.rOut，令 y := a + s•(y'−a) ∈ ∂U（`indicator_homothety`/`hausdorff_frontier_homothety` 的
  像描述）、b := a − (s/(1−s))•(x−y')，‖b−a‖ < r（由 hε），y = s•x + (1−s)•b（代数），
  `le_rpow_mul_of_combination` 给 ρ x ≤ (M/b₀)^{(1−s)/s} ρ y；若 y ∉ interior ν.support 则 ρ x = 0
  （x ∈ {ρ>0} ⊆ ν.support 由上半连续 + `Measure.mem_support`-型论证，b ∈ interior，凸组合进入内部：
  `Convex.combo_interior_closure_mem_interior`）。再对 ∂U' 换元到 ∂U：`lintegral_map` 沿位似的 `MeasurableEquiv`
  + hausdorff_frontier_homothety，得因子 (1/s)^{n−1} = s^{1−n}（`ENNReal.ofReal_rpow_of_pos`）。
- RelativePerimeter.exists_smooth_recovery_sequence：组装。a, r, b₀ 如 exists_le 的 (i)(ii)；M 由 exists_le；
  取 s_j = 1 − 1/(j+2)，ε_j 使 s_j ε_j/(1−s_j) < r 且 ε_j → 0（`ContDiffBump` 用 `⟨rIn, rOut, …⟩`，如 rIn = ε/2，rOut = ε）；
  u_j := (U.homothety a (1/s_j)⁻¹…).mollifiedIndicator φ_j m。正则性：mollifiedIndicator_contDiff_lipschitz_mem_Icc。
  L¹：三角不等式经 v_{s_j}：‖u_j − v_{s_j}‖_{L¹(ν)} → 0 用 `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`
  （m-a.e. 收敛）+ ν ≪ m（`h.withDensity_eq ▸ withDensity_absolutelyContinuous`）+ 有界收敛（控制 1，
  `tendsto_lintegral_of_dominated_convergence`），注意这里 s 固定而 ε → 0，要对角选择；‖v_{s_j} − 𝟙_U‖ → 0 用
  tendsto_indicator_homothety（沿 c_j = 1/s_j → 1，`Tendsto.comp`）与 indicator_homothety。
  limsup：`lintegral_enorm_gradient_mollified_homothety_le` 逐项，右边系数
  `ENNReal.ofReal (s_j^{1−n} (M/b₀)^{(1−s_j)/s_j}) → ENNReal.ofReal 1 = 1`（`Real.rpow` 连续，`Real.rpow_zero`），
  `limsup_le_of_le`/`Filter.limsup_le_limsup` + `ENNReal.Tendsto.mul_const`。

报告格式：每条义务一行：名称 | 完成/未完成 | 用到的关键 API | 若未完成，卡点与所需基础设施。最后给
`lake env lean -DwarningAsError=true` 的输出摘要与 `#print axioms` 结果。不要声称已完成未编译通过的内容。
```

---

## 提示词 B：`thm:smooth-gradient-relaxation-two-cheeger`（只做可证层）

```
仓库同上。任务：填写 formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean 中可用现有输入证明的 20 条 sorry；
另外 6 条（LocalSlope.relaxation_eq_asymptoticLipschitz、Cheeger.energy_eq_ofAsymptoticLipschitz、
SmoothGradient.relaxation_eq_localSlope、relaxation_eq_two_mul_cheeger、Intrinsic.energy_eq_two_mul_cheeger）
是奇异测度下的开放比较（Ambrosio–Gigli–Savaré 2013 型），**不要动**，保留 sorry。
先读 research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md：其中"sorry 义务清单"表
给出了每条的行号、陈述、对应 Blueprint 句子与建议 API；依赖顺序 #1–#7、#14 → #8–#12、#16–#19 → #20、#21 → #25、#26。
规则、编译命令、报告格式与提示词 A 相同（文件路径换成 Energy/WIP/Cheeger.lean；决定记录新建
research/decisions/2026-09-1X-smooth-gradient-relaxation-two-cheeger-proofs.md）。
关键入口：PreEnergy.sequentialRelaxation_comp_le、sequentialRelaxation_toAmbient_le、
lowerSemicontinuous_sequentialRelaxation、le_sequentialRelaxation_of_lowerSemicontinuous、
sequentialRelaxation_le_of_recovery_sequences（Energy/Relaxation/{Basic,LowerSemicontinuous}.lean）；
Energy.LocalSlope.apply_eq_norm_gradient、energy_eq_lintegral_gradient、admissible_iff_memLp_gradient
（Energy/LocalSlope/Gradient.lean）；ContDiff.locallyLipschitz（Mathlib）；
Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2（B = ContinuousLinearMap.id）；
KLS.LogConcave.intrinsic_absolutelyContinuous（KLS/LogConcave/AbsoluteContinuity.lean）。
参照同型已证论证：Energy.LipschitzGradient.localSlope_holds_of_relaxation（Poincare/LipschitzGradient/Comparison.lean）
与 Energy.SmoothGradient.relaxation_eq_intrinsic_energy（Energy/SmoothGradient/Intrinsic/Comparison.lean）。
```

---

## 补记（2026-09-11 晚）：提示词 A 对应文件的陈述已修正

`KLS/WIP/RelativePerimeter.lean` 中 `relativePerimeter` 改用归一化曲面测度 `surfaceMeasure V`
（`= ofReal (ω_{n−1}/2^{n−1}) • μH[n−1]`），`enorm_gradient_mollified_le`、
`lintegral_enorm_gradient_mollified_homothety_le`、`exists_smooth_recovery_sequence` 的参考测度固定为 `volume`
（前提 `IsBorellDensity ν volume ρ`），新增义务 `hausdorffNormalized_finrank_eq_volume`。原因见
[陈述记录补记](2026-09-11-relative-perimeter-smoothing-statement.md)。提示词 A 第三层的 API 提示不变，但
Gauss–Green 推论现在需以标准归一化陈述（`∇(η⋆𝟙_U)(x) = ∫_{∂U} η(x−y) n(y) dℋ^{n−1}_std(y)`，`n` 外法向），
Tonelli 换序时 `surfaceMeasure` 的局部有限性由 `isLocallyFiniteMeasure_hausdorff_frontier` 经 `smul` 得到。
