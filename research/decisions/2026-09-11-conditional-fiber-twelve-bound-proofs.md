# 2026-09-11 — `cor:conditional-fiber-twelve-bound`：唯一 `sorry` 已补全

接 [陈述记录](2026-09-11-conditional-fiber-twelve-bound-statement.md)。该记录列出的三条基础设施缺口
（一维 Brunn–Minkowski / Prékopa–Leindler、沿直线的显式分解、a.e. 非退化）已全部补上，
`FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean` 中的 `ae_conditionalFiber_logConcave`
不再是 `sorry`。同文件其余五条定理未改类型、未改证明体。

## 子义务完成状态

| 子义务 | 状态 | 说明 |
|---|---|---|
| A 一维"对数凹密度 ⇒ 紧集对数凹" | 完成 | A1 紧集 Brunn–Minkowski、A2 **完全一般**的 Prékopa–Leindler（不带有界性前提）、A3 `LineDensity.logConcave` 全部证完 |
| B 沿直线的显式分解核 | 完成 | B1 `compProd_baseLaw_sliceKernel`、B2 `ae_sliceKernel_eq` 证完 |
| B3 好集几乎处处 | **未按原计划做，且不需要** | 见下"路线偏差" |
| C 装配 | 完成 | `ae_conditionalFiber_logConcave` 无 `sorry` |

## 新文件与公开声明

1. `formalization/FunctionalInequalities/Probability/Line/BrunnMinkowski.lean`
   （命名空间 `FunctionalInequalities.Probability.Line`，384 行）
   - `volume_add_le_volume_add`：`K L : Set ℝ` 非空紧 ⇒ `volume K + volume L ≤ volume (K + L)`。
   - `le_volume_combination`：`S T` 非空可测、`0 < t < 1` ⇒
     `ofReal t * volume S + ofReal (1-t) * volume T ≤ volume {z | ∃ x ∈ S, ∃ y ∈ T, z = t•x+(1-t)•y}`。
     组合集不必可测（右端用外测度），这正是层饼论证需要的形式。
   - `prekopaLeindler`：`f g h : ℝ → ℝ` 可测、`f, g ≥ 0`、`0 < t < 1`、
     `∀ x y, f x ^ t * g y ^ (1-t) ≤ h (t*x + (1-t)*y)` ⇒
     `(∫⁻ ofReal f)^t * (∫⁻ ofReal g)^(1-t) ≤ ∫⁻ ofReal h`。**无有界性前提**。
   - 私有：`geom_le_arith`（ENNReal 两项加权 AM–GM，Mathlib 只有 `NNReal`/`Real` 版本）、
     `lintegral_add_le_of_sup_one`（上确界归一化后的算术形式）、`prekopaLeindler_bddAbove`、`rpow_iSup`。

2. `formalization/FunctionalInequalities/Probability/HaarLine.lean`
   （命名空间 `FunctionalInequalities.Probability`，101 行）
   - `lineMap`、`lineEquiv`（`(ℝ ∙ θ)ᗮ × ℝ ≃ₗ[ℝ] E`，`(z, s) ↦ z + s • θ`）与两条 `@[simp]` 求值引理。
   - `exists_lintegral_line`：`m` 为 Haar、`‖θ‖ = 1` ⇒ 存在 `c ≠ 0, ≠ ⊤` 使得对一切可测 `G`，
     `c * ∫⁻ G dm = ∫⁻ z : (ℝ∙θ)ᗮ, ∫⁻ s : ℝ, G (z + s•θ)`（外层 `Measure.addHaar`，内层 `volume`）。

3. `formalization/FunctionalInequalities/KLS/LogConcave/Line/OfDensity.lean`
   （命名空间 `FunctionalInequalities.KLS.LineDensity`，65 行）
   - `LineDensity.logConcave (d : LineDensity μ) : LogConcave μ`。
     与既有 `LogConcave.exists_lineDensity` 互为反方向，按 `d.` 点记法调用（`research/naming.md`）。

4. `formalization/FunctionalInequalities/KLS/ConditionalFiber/SliceKernel.lean`
   （命名空间 `FunctionalInequalities.KLS.ConditionalFiber`，253 行）
   - `sliceMass p b`、`SliceGood p`、`sliceDensity p b t`、`sliceKernel p hp`（`Kernel (Direction E × E) ℝ`）。
     `hp : Measurable p` 是显式参数（`Kernel.piecewise` 需要可测集证明）；`Measurable` 是 `Prop`，故无选择歧义。
   - `measurable_sliceMass`、`measurableSet_sliceGood`、`measurable_sliceDensity`、
     `sliceKernel_apply_of_good`、`sliceKernel_eq_withDensity_of_good`、`sliceKernel_apply_of_not_good`、
     `instIsMarkovKernelSliceKernel`。
   - `inner_add_smul_orthogonal`、`coordinates_add_smul_orthogonal`、`baseMap_add_smul_orthogonal`：
     正交分解下 `coordinates (θ, z + tθ) = ((θ, z), t)`。
   - `sliceKernel_mul_sliceMass`：`Z ≠ ⊤` ⇒ `sliceKernel b A * Z = ∫⁻ t in A, ofReal (p (reconstruct b t))`
     （同时覆盖 `Z = 0`）。
   - `exists_lintegral_line_density`：带 Haar 密度的 `μ` 沿固定方向的 Fubini 分解。
   - `compProd_baseLaw_sliceKernel`：`baseLaw μ ρ ⊗ₘ sliceKernel p hp = jointLaw μ ρ`。
   - `ae_sliceKernel_eq`：`∀ᵐ b ∂baseLaw μ ρ, sliceKernel p hp b = kernel μ ρ b`。

## 改动的既有文件

- `FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean`：
  `affineSupport_eq_top_of_absolutelyContinuous` 去掉 `private`（类型与证明未动，docstring 已有）。
- `FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean`：
  新增四条 import；新增私有引理 `isBorellDensity_sliceKernel`；补全 `ae_conditionalFiber_logConcave`；
  更新模块 docstring（不再声称有 `sorry` 与缺口）。五条合成定理一字未改。

## 路线偏差（与提示相比）

1. **B3 不需要。** 提示要求证"好集几乎处处"。实际上坏基点上 `sliceKernel b = Measure.dirac 0`，
   而 `KLS.logConcave_dirac` 已证狄拉克律对数凹，所以 `LogConcave (sliceKernel p hp b)` 对**每个** `b` 成立，
   不必区分好坏集。分解恒等式里只需要 "`Z < ⊤` 几乎处处"，这一条由 `exists_lintegral_line_density`
   取 `F ≡ 1` 直接得到（`∫⁻ z, Z(θ,z) = c < ⊤`），写在 `lintegral_section_eq` 内部。
2. **A2 做成了完全一般的陈述。** 提示允许先留 `sorry`；实际用"上确界归一化 + 截断取极限"
   去掉了有界性前提，`prekopaLeindler` 对任意可测非负 `f g` 成立。
3. **`c_θ` 不做成可测对象。** 按提示的替代路线：对每个固定 `θ` 用 `lintegral_congr` 逐点改写，
   两边共用同一个 `c`，从不需要 `θ ↦ c_θ` 的可测性，也从不计算 `c`。
4. **A2 用实值而非 ENNReal 值函数。** 层饼公式 `lintegral_eq_lintegral_meas_lt` 只有实值版本；
   实值形式也正是 A3 的用法（`IsBorellDensity` 的 `ρ : V → ℝ`）。

## 用到的关键 Mathlib API

- `MeasureTheory.lintegral_eq_lintegral_meas_lt`（层饼）、`MeasurableSet.measure_eq_iSup_isCompact`（内正则）、
  `measure_union_add_inter`、`measure_preimage_add`、`Measure.addHaar_smul`、
  `IsCompact.sSup_mem` / `sInf_mem`、`ENNReal.iSup_add_iSup_le`、`ENNReal.mul_iSup`、
  `NNReal.geom_mean_le_arith_mean2_weighted`、`ENNReal.orderIsoRpow`、`lintegral_iSup`。
- `ContinuousLinearEquiv.isAddHaarMeasure_map`、`Measure.prod.instIsAddHaarMeasure`、
  `Measure.isAddLeftInvariant_eq_smul`、`Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure`、
  `LinearEquiv.toContinuousLinearEquiv`、`Submodule.mem_orthogonal_singleton_iff_inner_right`、
  `LinearMap.coprod` / `toSpanSingleton`。
- `ProbabilityTheory.Kernel.withDensity(')`、`Kernel.piecewise`、`Kernel.measurable_kernel_prodMk_left`、
  `Measure.compProd_apply`、`Measure.prod_apply`、`ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`。
- `UpperSemicontinuous.comp`、`Continuous.comp_upperSemicontinuous`（切片密度的上半连续性）。

## 陈述层面的怀疑

未发现既有陈述有误：`ae_conditionalFiber_logConcave` 按原样可证，未发现缺前提或方向相反。
两点记录以备 owner 判断：

- `hρ : Admissible μ ρ` 与 `[CompleteSpace E]` 在这条引理的证明里**用不到**（结论对任意方向律成立）。
  为保持与同块五条定理一致的参数表、且不改类型，本次用
  `set_option linter.unusedSectionVars false in` 与 `set_option linter.unusedVariables false in`
  局部关闭两条 linter，而非删参数。是否收紧签名留给 owner。
- `hac : μ ≪ m` 只用来推出仿射支撑为 ⊤（进而支撑内部非空、存在 Borell 密度）；
  参考测度 `m` 本身在结论里不出现。

## 这些新引理应放到哪个共享文件

- `volume_add_le_volume_add`、`le_volume_combination`、`prekopaLeindler`：留在
  `Probability/Line/BrunnMinkowski.lean`。它们与对数凹无关，是纯一维测度论工具，
  与 `Probability/Line/{Cdf,AffineProfile,ExpIntegral}.lean` 同级。
  若将来要高维 Prékopa–Leindler，这个文件是自然的一维基例所在。
- `lineEquiv`、`exists_lintegral_line`：留在 `Probability/HaarLine.lean`。与概率无关、
  只依赖内积空间与 Haar 测度；如果 `Energy/` 侧将来也要沿方向做 Fubini，应从这里取。
- `LineDensity.logConcave`：并入 `KLS/LogConcave/Line/Density.lean` 也说得通（与
  `LogConcave.exists_lineDensity` 互逆），但那会让 `Density.lean` 依赖 `BrunnMinkowski.lean`。
  本次保留在独立的 `Line/OfDensity.lean`，依赖方向更干净；若 owner 更看重"密度结论集中"，
  合并进 `Density.lean` 是低风险改动。
- `sliceMass` / `sliceKernel` 一族：留在 `KLS/ConditionalFiber/SliceKernel.lean`，
  与 `ConditionalFiber/{Closed,EnergyComparison}.lean` 同级。它是纤维层的显式构造，
  不属于 `KLS/LogConcave/`（不假设对数凹，只要一个 Haar 密度）。

## 编译与公理

```
lake env lean -DwarningAsError=true <每个新文件与 KLS/LogConcave/ConditionalFiber.lean>   # 全部无输出
lake build                                                                                # 3383 jobs 全通过
```

`#print axioms`：`ae_conditionalFiber_logConcave`、`conditionalFiber_literatureConstant_le_four_mul`、
`conditionalFiber_literatureConstant_le_twelve_mul_of_four`、`compProd_baseLaw_sliceKernel`、
`Probability.Line.prekopaLeindler`、`LineDensity.logConcave`
均只依赖 `propext, Classical.choice, Quot.sound`。

## 未做

按本轮约束：未注册（`FunctionalInequalities.lean` 聚合导入、lakefile `Solutions` 根、
`research/a-series/ledger.yaml`、`research/check_blueprint.py` 的 `CERTIFICATES`、`research/tasks.json`
均未改），Blueprint 的 `\lean{}`/`\leanok` 未加，未 `git commit`、未 `git push`。
`tasks.json` 中该节点仍标 `missing`，需要 owner 在注册轮改为已证并写证书
`solutions/CorConditionalFiberTwelveBound.lean`。
