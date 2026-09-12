# 2026-09-12 — 相对周长链条的分析前提：填 sorry（12/17 完成）

承接同日的[陈述记录](2026-09-12-relative-perimeter-prerequisites-statement.md)与
[sorry 提示词](2026-09-12-relative-perimeter-prerequisites-sorry-prompt.md)。本轮只改动
`formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` 一个文件：17 条义务填完 12 条，
留 5 条 `sorry`。未改任何 `theorem`/`def` 的类型，未改两个 `def` 的定义体，未改
`RelativePerimeter.lean` / `CheegerInfimum.lean`（`sorry` 数仍为 5 与 9），未注册、未提交、未推送。

## 一览

| 义务（省略 `FunctionalInequalities.`） | 状态 | 关键 API | 卡点 |
|---|---|---|---|
| `Analysis.prekopaLeindler` | 完成 | 见下「A 组」 | — |
| `Analysis.volume_rpow_mul_le_volume_combination` | 完成 | 指示函数代入 PL + `MeasurableSet.measure_eq_iSup_isCompact` + `ENNReal.orderIsoRpow` | — |
| `Analysis.volume_rpow_add_le_volume_add_rpow` | 完成 | 齐次化 + `Measure.addHaar_smul_of_nonneg` + `ENNReal.ofReal_rpow_of_nonneg` | — |
| `Analysis.isodiametric` | 完成 | `t = 1/2` 的乘法型 BM + `InnerProductSpace.volume_closedBall` + `Metric.diam_closure` | — |
| `Analysis.volume_le_ofReal_mul_hausdorffMeasure` | 完成 | `Measure.le_hausdorffMeasure`（ε = 1）+ `isodiametric` | — |
| `Analysis.hausdorffMeasure_finrank_eq_smul_volume` | 完成 | Haar 唯一性 + Besicovitch；见下「A2」 | — |
| `Analysis.exists_lipschitzOnWith_levelSet_subset_image` | 完成 | `HasStrictFDerivAt.implicitFunctionOfComplemented`、`to_implicitFunctionOfComplemented`、`HasStrictFDerivAt.exists_lipschitzOnWith` | — |
| `Analysis.exists_hausdorffMeasure_levelSet_lt_top` | 完成 | `LipschitzOnWith.hausdorffMeasure_image_le`、`Module.Dual.finrank_ker_add_one_of_ne_zero`、`isAddHaarMeasure_hausdorffMeasure` | — |
| `Analysis.aemeasurable_lintegral_levelSet` | **未完成** | — | 见下「D 组」 |
| `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | **未完成** | — | 见下「D 组」 |
| `Analysis.sard` | **未完成** | — | 见下「E 组」 |
| `Analysis.ae_forall_fderiv_ne_zero` | 完成（依赖 `sard`） | `ae_iff` + `measure_mono_null` | — |
| `KLS.SmoothDomain.outwardNormal_eq` | 完成 | 沿射线的斜率论证 + 线性泛函的半空间包含；见下「C 组」 | — |
| `KLS.SmoothDomain.norm_outwardNormal` | 完成 | `dif_pos`、`toDual_gradient`、`inv_mul_cancel₀` | — |
| `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | **未完成** | — | 见下「C1」 |
| `KLS.SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal` | **未完成** | — | 见下「C2」 |
| `KLS.SmoothDomain.gradient_mollifiedIndicator_eq` | 完成（依赖 C2） | 卷积求导 + `ext_inner_right` + `integral_inner` | — |

`#print axioms`：上表 12 条「完成」中，**10 条只依赖 `propext / Classical.choice / Quot.sound`**；
`ae_forall_fderiv_ne_zero`（依赖 `sard`）与 `gradient_mollifiedIndicator_eq`（依赖 C2）额外出现 `sorryAx`，
这是提示词的分层设计所预期的（组装层先于其输入完成）。

## 完成的证明：路线与新增的 private 引理

**新增声明全部是 `private`**，没有新增任何非 private 的一般引理；17 条公开陈述与 2 个 `def` 逐字未动。

### A 组（等周直径不等式，6/6 完成，全部无 `sorryAx`）

n 维 Prékopa–Leindler 走「抽象性质 + 维数归纳」：

* `private def IsPL (X) (μ) (t)`：`ℝ≥0∞` 值的 PL 性质（`f g h : X → ℝ≥0∞` 可测，
  `f x ^ t * g y ^ (1−t) ≤ h (t • x + (1−t) • y)` ⟹ 积分的同型不等式）。用 `ℝ≥0∞` 值而不是提示词里的
  `ofReal ∘ (ℝ 值)`，正是为了绕开提示词指出的障碍：切片积分 `∫⁻ s, f (s, x')` 可能为 `⊤`，也不是 `ofReal` 形式。
* `private isPL_real`：由仓库的 `Probability.Line.prekopaLeindler` 经 `min · N`（`N : ℕ`）截断 + `toReal`
  归约，再用 `lintegral_iSup` 单调收敛把截断去掉。辅助 `private iSup_min_natCast`、`private rpow_iSup`
  （后者是 `Probability/Line/BrunnMinkowski.lean` 中同名 private 引理的复制，跨模块不可引用）。
* `private IsPL.prod`：Tonelli（`lintegral_prod`、`Measurable.lintegral_prod_right'`）+ 对切片用 Y 的 PL、
  对切片积分用 X 的 PL。
* `private IsPL.comp` / `IsPL.symm`：沿保测且保凸组合的映射（`MeasurePreserving.lintegral_comp`）搬运；
  `symm` 由 `MeasurableEquiv` 的单射性把正向线性性转成逆向线性性。
* `private isPL_pi`：对 `n` 归纳。`n = 0` 用 `Measure.volume_pi_eq_dirac` + `lintegral_dirac'`；
  `n+1` 用 `MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0` 与 `volume_preserving_piFinSuccAbove`，
  其线性性是 `rfl`。
* `private isPL_euclidean`、`private isPL_volume`：`PiLp.volume_preserving_toLp`（线性性 `rfl`）与
  `OrthonormalBasis.measurePreserving_repr_symm`（线性性 `simp`）。

`volume_rpow_mul_le_volume_combination` 与一维 `le_volume_combination` 同套路（紧子集内正则 + `iSup`），
`volume_rpow_add_le_volume_add_rpow`、`isodiametric`、`volume_le_ofReal_mul_hausdorffMeasure` 按提示词的路线。
`isodiametric` 的 `n = 0` 分支用 `Basis.addHaar_self` 与 `Subsingleton.eq_univ_of_nonempty` 给出 `vol univ = 1`。

**A2（`hausdorffMeasure_finrank_eq_smul_volume`）的实际路线**与提示词略有出入，记录于此：

1. Haar 唯一性用 `Measure.isAddLeftInvariant_eq_smul`（不是 `addHaarMeasure_unique`），
   得 `μH[n] = (addHaarScalarFactor μH[n] volume : ℝ≥0) • volume`。
2. 下界由 `volume_le_ofReal_mul_hausdorffMeasure` 在 `Metric.ball 0 1` 上取值（`InnerProductSpace.volume_ball`）。
3. 上界 `private hausdorffMeasure_ball_le`：**把 Besicovitch 用在 `mkMetric` 的尺度前测度上**，而不是用在
   `μH[n]` 上。关键是提示词没有点明的一步：`μH[n] (closedBall x r) ≤ (2r)^n` 本身与结论同强度，不能先证；
   但对每个尺度 `k⁻¹`，`OuterMeasure.mkMetric'.pre_le` 直接给出「单集覆盖」界。于是
   `μH[n] s = ⨆ k, pre (fun t ↦ ediam t ^ n) k⁻¹ s`（`OuterMeasure.mkMetric'.eq_iSup_nat` +
   `OuterMeasure.coe_mkMetric`），对每个 `k` 用 `Besicovitch.exists_disjoint_closedBall_covering_ae`
   把 `ball 0 1` 覆盖到零测差集，差集部分由第 1 步的 `c • volume` 表示得 `0`，球的部分用 `pre_le`、
   `Metric.diam_closedBall`、`InnerProductSpace.volume_closedBall` 与 `measure_biUnion`（两两不交）求和。
4. **取开球而不是闭球**，并让 Besicovitch 的半径上界取 `min δ (1 − ‖x‖)`，使所有小球落在 `ball 0 1` 内；
   这样上界直接是 `ofReal(2^n/ω_n) · vol(ball 0 1)`，省掉提示词里 `ε → 0` 的极限论证。
5. `n = 0` 分支单列：`Measure.hausdorffMeasure_zero_singleton` 与 `vol univ = 1`，两侧都是 `1`。

### B 组（2/2 完成，无 `sorryAx`）

`exists_lipschitzOnWith_levelSet_subset_image` 用 `HasStrictFDerivAt.implicitFunctionOfComplemented`
（**带 `hker` 的版本**，而不是提示词建议的有限维版 `implicitFunction`），因为只有这个版本能让
`(Φ y).snd = P (y − x)` 对显式的投影 `P = Classical.choose hker` 成立
（`implicitToOpenPartialHomeomorphOfComplemented_apply`）：
`s` 的有界性于是化为「`P` 是连续线性映射、`N ⊆ ball x 1`」，`g` 的 Lipschitz 性由
`to_implicitFunctionOfComplemented` 给出的 `HasStrictFDerivAt g (ker).subtypeL 0` 加
`HasStrictFDerivAt.exists_lipschitzOnWith` 得到——**不需要** `ImplicitContDiff` 文件。
`N` 取 `eq_implicitFunctionOfComplemented` 的邻域、`P(· − x)` 对 Lipschitz 邻域的原像、`ball x 1` 三者之交。

`exists_hausdorffMeasure_levelSet_lt_top` 按提示词组装；`finrank ker = n − 1` 用
`Module.Dual.finrank_ker_add_one_of_ne_zero`（比提示词建议的 `finrank_range_add_finrank_ker` 直接）。

### C 组（3/5 完成）

* `norm_outwardNormal`：`dif_pos` + `toDual_gradient`。
* `outwardNormal_eq`：先证任意两个定义对给出同一个单位法向。三个 private 辅助：
  `eventually_lt_zero_of_hasDerivAt` / `eventually_zero_lt_of_hasDerivAt`（`hasDerivAt_iff_tendsto_slope`，
  与 `RelativePerimeter.frontier_inter_eq` 中的论证同型，但整理成 `𝓝[>] 0` 的 `Eventually` 形式）、
  `hasDerivAt_line`、以及线性代数的 `eq_smul_of_forall_lt_imp_le`：
  `{A v < 0} ⊆ {B v ≤ 0}` 且 `A` 满射 ⟹ `B = λ • A`、`λ > 0`（核上的双侧 ε 论证）。
  再由 `toDual` 的单射性把 `fderiv` 的比例关系搬到 `gradient`。
* `gradient_mollifiedIndicator_eq`：按提示词，由 C2 对 `η_x = φ.normed volume (x − ·)` 得到。
  卷积求导用 `HasCompactSupport.hasFDerivAt_convolution_right` 与 `convolution_precompR_apply`，
  再用 `ext_inner_right ℝ` 与 `integral_inner` 逐向量比较；`gradient η_x y = −gradient η (x − y)` 由
  `HasFDerivAt.const_sub` 与 `toDual` 单射性。两条 private 复制品
  `mollifiedIndicator_eq_convolution`、`locallyIntegrable_indicator_one` 对应 RP 中不可跨模块引用的 private 引理。

## 未完成的 5 条：卡点

### C1 `integral_divergence_eq_integral_inner_outwardNormal`（Gauss–Green）

未动。卡点与提示词第三层的判断一致，且更具体：唯一真正缺的是 **Lipschitz 图上的面积公式**
`∫_P G(z, g z) √(1+|∇g z|²) dz = ∫_{graph} G dℋ^{n−1}`，Mathlib 只有同维数面积公式
（`MeasureTheory/Function/Jacobian.lean`）。单位分解与沿法向的一维分部积分都有现成材料，
但把它们接到 `surfaceMeasure`（即 `μH[n−1]` 的归一化）上必须经过这条子义务。本轮没有开始这条。

### C2 `setIntegral_gradient_eq_integral_smul_outwardNormal`

**提示词把这条列为「易（给定 C1）」，这个判断偏乐观**，记录原因：把 C1 的
`∫_U ⟪∇η, e⟫ = ∫_{∂U} ⟪e, η ν⟫` 提升成向量等式 `∫_U ∇η = ∫_{∂U} η ν`，需要 `integral_inner`，
因而需要右端被积函数 `y ↦ η y • ν y` 在 `(surfaceMeasure V).restrict (frontier U)` 下**可积**，
其中包含两件事：

1. `surfaceMeasure V (frontier U ∩ tsupport η) < ⊤`——即 `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`
   （RP 中仍是 `sorry`，但本轮的 `exists_hausdorffMeasure_levelSet_lt_top` 已经是它的完整输入）；
2. **`outwardNormal` 在 frontier 上的可测性**。这一条在陈述记录里没有出现过：`outwardNormal` 用
   `Classical.choose` 定义，逐点可测性不显然。真命题是「`ν` 在 frontier 上连续」——由 `outwardNormal_eq`
   与 `∇φ/‖∇φ‖` 的连续性，但只在每个定义邻域 `W` 内成立；要得到整体可测性需要对 frontier 的开覆盖
   `{W_i}` 取可数子覆盖（`V` 有限维故 Lindelöf），再作可数分片。这是一条独立的、约百行的义务，
   建议日后作为 `SmoothDomain.continuousOn_outwardNormal` / `measurable_outwardNormal` 单列。

若不成立（即 `η • ν` 不可积），右端按 Bochner 约定为 `0`，而左端一般非零，所以这一步不能绕过。

### D 组 `aemeasurable_lintegral_levelSet`、`lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（coarea）

未动，与提示词第三层的预期一致：缺 Lipschitz 图上的面积公式（同 C1）、Whitney 延拓（`C¹` 逼近），
以及 `t ↦ μH[n−1] (A ∩ {u = t})` 的可测性所需的 s-有限化。本轮没有做局部版本。

### E 组 `sard`

未动。Milnor 的对维数归纳需要 Taylor 余项在紧集上的一致估计与沿坐标切片的 Fubini，Mathlib 材料齐备
但无现成框架；提示词建议的 (a) `n = 0`、(b) `n = 1` 两个分支即使写出来也不能消掉这一条 `sorry`
（陈述是对所有 `n` 的），所以本轮没有写半成品。**注意**：`ae_forall_fderiv_ne_zero` 已经完成并只依赖
`sard`，所以 `sard` 一旦证出，`CheegerInfimum.lean` 的 `SmoothDomain.ae_exists_superlevel` 立即可组装。

## 陈述问题

没有发现假陈述。17 条陈述在本轮的使用中都如其字面所说；两个 `def` 的定义体也够用
（`outwardNormal` 的 `Classical.choose` 形式在 `outwardNormal_eq` 中处理得很顺，见上）。
唯一的「陈述层面的遗漏」是上面 C2 里说的 `outwardNormal` 可测性——它不是某条陈述为假，
而是链条里还缺一条没有被写成义务的引理。

## 新增的非 private 引理

无。

## 编译

在 `formalization/` 下（原生 arm64 工具链）：

```
lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites   # Build completed successfully (3088 jobs)
lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
```

`lake env lean` 恰好输出 5 条 `declaration uses 'sorry'`（879、889、906、1102、1111 行），无其他警告；
`-DwarningAsError=true` 下这 5 条升级为 error，**没有任何其他诊断**。文件 1218 行。

新增 import：`Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls`、`Mathlib.Analysis.Calculus.Implicit`、
`Mathlib.MeasureTheory.Constructions.Pi`、`Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace`、
`FunctionalInequalities.Probability.Line.BrunnMinkowski`；`open scoped` 增加 `Convolution`。
按提示词第 3 条，逐条填完后新冒出的 `unusedSectionVars` 警告用 `omit [...] in` 处理
（`rpow_iSup`、`hasDerivAt_line`、`eq_smul_of_forall_lt_imp_le`、两条 C3 的 private 复制品）。

## 未做

- 未改动 `RelativePerimeter.lean`（5 条 `sorry`）、`CheegerInfimum.lean`（9 条 `sorry`）。
- 未注册：`FunctionalInequalities.lean`、lakefile `Solutions` 根、`research/a-series/ledger.yaml`、
  `research/check_blueprint.py`、`research/tasks.json`、Blueprint 的 `\lean{}`/`\leanok` 均未动。
- 未 `git commit`、未 `git push`。
