# 2026-09-11 — `lem:conditional-fiber-energy-comparison`：两条 sorry 的证明

## 决定

- 填完 `formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean` 中的两条 `sorry`
  （`energy_le_of_fiberBound`、`literatureConstant_le_of_fiberBound`）。两条 `theorem` 与 `FiberBound` 的类型
  一字未改；陈述与 Blueprint 的逐句对齐仍以
  [同日陈述记录](2026-09-11-conditional-fiber-energy-comparison-statement.md) 为准。
- 只在该文件内工作：新增 `private` 辅助引理／一个 `private def`、两条 `import`
  （`Mathlib.MeasureTheory.Function.SpecialFunctions.Inner`、`Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`）。
  未改任何共享文件，未注册（`FunctionalInequalities.lean` 聚合导入、`lakefile.toml` 的 `Solutions` 根、
  `research/a-series/ledger.yaml`、`research/check_blueprint.py` 的 `CERTIFICATES`、`research/tasks.json`），
  未改 Blueprint 的 `\lean{}`/`\leanok`。未 `git commit`、未 `git push`。

## 编译

在 `formalization/` 下：

```
lake env lean FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
```

两者均无任何诊断（无 error、无 warning、无 `declaration uses 'sorry'`）。`#print axioms` 对两条顶层定理均为
`[propext, Classical.choice, Quot.sound]`。（本机 CommandLineTools 的 x86_64 lake / arm64 xcrun 不兼容问题沿用
git 包装脚本 + `GIT_EXEC_PATH`/`GIT_TEMPLATE_DIR` 的绕过方式；lake 在首次运行时因 manifest URL 变动重新克隆了
`.lake/packages/checkdecls`，只影响 `.lake/`，未改仓库内容。）

## 证明结构（私有引理分三组）

### 1. 等距运输（`section IsometryTransport`，一般有限维 Hilbert 空间 `X Y`）

- `localSlope_apply_comp_isometryEquiv (e : X ≃ᵢ Y) h x : apply (h ∘ e) x = apply h (e x)`：
  `apply` 的 `iInf`/`iSup` 定义直接用 `e.surjective.iSup_comp` 换元，`e.dist_eq` 收尾。
- `localSlope_energy_comp_isometryEquiv`：`MeasurePreserving.lintegral_comp_emb`（用
  `e.toHomeomorph.toMeasurableEquiv.measurableEmbedding`，不需要 `apply` 的可测性）。
- `evariance_comp_measurePreserving`：`evariance` 展开后用 `MeasurePreserving.integral_comp` 与
  `lintegral_comp_emb`。
- `holds_of_isometryEquiv`：`Holds ν' C → Holds ν C`（`e : X ≃ᵢ Y` 保测 `ν ↦ ν'`）。测试 `g` 对应 `g ∘ e.symm`，
  局部 Lipschitz 用 `LocallyLipschitz.comp`，`L²` 用 `MemLp.comp_measurePreserving`，能量与方差用上两条。

### 2. 满仿射支撑（`section FullAffineSupport`）

- `surjective_intrinsicReconstruct`、`intrinsicIsometryEquiv`：`affineSupport ν = ⊤` 时
  `Probability.reconstruct ν : direction ≃ᵢ E`（`Equiv.ofBijective` + `AffineIsometry.isometry`），
  `Probability.measurePreserving_reconstruct` 给保测性。
- `holds_iff_intrinsicMeasure`：`Holds ν C ↔ Holds (intrinsicMeasure ν) C`（两个方向各用一次
  `holds_of_isometryEquiv`）。
- `intrinsic_constant_eq_iInf`：`Intrinsic.constant ν = ⨅ C : {C // Holds ν C}, C`。
- `evariance_le_mul_energy_of_iInf_le`：`⨅ C : {C // Holds ν C}, C ≤ B`、`B ≠ ⊤`、`Admissible ν g` ⇒
  `evariance g ν ≤ B * energy ν g`。用 `le_iInf` + `ENNReal.iInf_mul`（`Nonempty` 由 `B ≠ ⊤` 排除空下确界），
  无 `ε` 剩余项；`B = 0`、`energy = 0` 均无需分支。这就是任务提示里"最需要小心的一步"，
  未改 `Poincare/LocalSlope/Basic.lean`。
- `affineSupport_eq_top_of_absolutelyContinuous`：`μ ≪ m`（Haar）⇒ `affineSupport μ = ⊤`
  （`Measure.addHaar_affineSubspace` + `measure_compl_affineSupport`）。
- `affineSupport_eq_top_of_evariance_ne_zero`：`ν : ProbabilityMeasure ℝ`，`evariance id ν ≠ 0` ⇒
  `affineSupport ν = ⊤`（真仿射子空间的方向是 `ℝ` 的真子模 ⇒ `⊥`（`Submodule.finrank_lt`、`finrank_self`、
  `Submodule.finrank_eq_zero`）⇒ 支撑上所有点等于 `supportPoint` ⇒ `id =ᵐ const` ⇒ 方差为 0）。

### 3. 解析核心（主命名空间）

- `lipschitzWith_reconstruct b : LipschitzWith 1 (reconstruct b)`。
- `hasDerivAt_comp_reconstruct`／`localSlope_apply_comp_reconstruct`：`f` 在 `reconstruct b t` 可微 ⇒
  切片 `s ↦ f (reconstruct b s)` 在 `t` 有导数 `fderiv ℝ f x θ`（`HasFDerivAt.comp_hasDerivAt`），
  局部斜率 `= ofReal |fderiv ℝ f x θ|`（`Energy.LocalSlope.apply_eq_norm_gradient` 的一维实例 +
  `HasDerivAt.hasGradientAt.gradient`）。
- `fderiv_apply_eq_inner_gradient : fderiv ℝ f x θ = ⟪θ, ∇f x⟫`（`InnerProductSpace.toDual_symm_apply`）。
- `directionalIntegrand f q := ofReal (⟪θ, ∇f(reconstruct b t)⟫²)`（`q = (b, t)`），`measurable_directionalIntegrand`
  用 `LipschitzApproximation.measurable_gradient` + `Measurable.inner`。
- `ae_ae_reconstruct`：`μ`-a.e. 的可测性质沿 a.e. 纤维成立（仿 `ae_restrict_congr`：`ae_map_iff`、
  `Measure.snd_prod`、`compProd_baseLaw_kernel`、`Measure.ae_ae_of_ae_compProd`）。
- `ae_memLp_comp_reconstruct`：`MemLp f 2 μ` ⇒ a.e. 纤维上切片 `MemLp 2`（仿 `ae_memLp_id`：
  `Measure.lintegral_compProd`、`lintegral_map`、`lintegral_prod_symm`、`ae_lt_top`）。
- `energy_le_of_fiberBound` 主体：
  1. `hI`：`∫⁻ b ∫⁻ t directionalIntegrand = ∫⁻ x ∫⁻ θ ofReal ⟪θ,∇f x⟫² dρ dμ`（compProd → jointLaw →
     `lintegral_map` + `reconstruct_coordinates` → `lintegral_prod_symm`）。
  2. `hframe`：`d * ∫⁻ θ ofReal ⟪θ,u⟫² dρ = ofReal ‖u‖²`（`Integrable.of_bound`、
     `ofReal_integral_eq_lintegral_ofReal`、`hρ.frame_identity u u`、`real_inner_self_eq_norm_sq`）。
  3. `hItot`：总方向积分 `≠ ⊤`（`1 ≤ d` 由 `positive_dimension`，与 `energy_eq_lintegral_gradient`、
     `hf.finite_energy`）；由此 a.e. 纤维的方向积分有限。
  4. `hfiberwise`：a.e. `b`，非退化时 `energyAt ≤ κ * ∫⁻ t directionalIntegrand`：切片 `Admissible`
     （第 3 组 + `ae_memLp_comp_reconstruct` + 有限性），`intrinsic_constant_eq_iInf` +
     `affineSupport_eq_top_of_evariance_ne_zero` 把 `hfiber` 转成 `⨅ ≤ κ·Var`，
     `evariance_le_mul_energy_of_iInf_le` 给具体测试不等式，`ENNReal.div_le_iff` 除以方差。退化纤维为 0。
  5. 组装：`lintegral_mono_ae`、`lintegral_const_mul'`、`hI`、`hframe`、`energy_eq_lintegral_gradient`；
     `≠ ⊤` 由 `ENNReal.mul_ne_top` 与 `ne_top_of_le_ne_top`。
- `literatureConstant_le_of_fiberBound`：`Holds μ (κ*C)` 直接展开证明（`form_toLp` 把 `toLp f` 放进
  `domain μ ρ`，`L2.variance_toLp` + `ofReal_variance` 把 `L2.variance` 换成 `evariance`，与义务 1 串联），
  再经 `holds_iff_intrinsicMeasure`（`affineSupport_eq_top_of_absolutelyContinuous`）与 `iInf_le_of_le`。
  不需要 `Poincare.L2Comparison` 或 `SmoothTest.constant_eq_intrinsicMeasure_and_localSlope`。

## 与 Blueprint 证明段落的对应

| Blueprint | Lean |
|---|---|
| "A finite upper bound for the literature infimum is itself valid: choose admissible constants below that bound plus 1/j and pass to the limit" | `evariance_le_mul_energy_of_iInf_le`（用 `ENNReal.iInf_mul` 一步到位，无 `1/j` 序列） |
| "Disintegration gives square integrability of the restricted test and integrability of its directional derivative on almost every fiber" | `ae_memLp_comp_reconstruct`、`hItot` + `ae_lt_top` |
| "Rademacher's theorem, absolute continuity, and Fubini identify that derivative with ⟨∇f,θ⟩" | `hdiff`（`ae_differentiableAt_of_locallyLipschitz` + `hac.ae_le`）、`ae_ae_reconstruct`、`localSlope_apply_comp_reconstruct`、`fderiv_apply_eq_inner_gradient` |
| "Dividing the assumed fiber inequality by its positive variance and using Tonelli" | `hfiberwise`（`ENNReal.div_le_iff`）、`hI`（`lintegral_prod_symm`） |
| "The last equality is the frame identity" | `hframe` |
| "Conditional Dirac laws have zero numerator; exceptional ... fibers are null" | `energyAt` 的 `if_neg` 分支；a.e. 过滤 |
| "puts the test in the maximal form domain before the form-gap inequality is applied" | `hmem : toLp f ∈ domain μ ρ` |
| "The final multiplication by C is the abstract implication in lem:finite-energy-factor-poincare" | 直接在 `Holds` 上展开（裸函数版本），未调用 `Poincare.L2Energy` |

## 应搬到共享文件的辅助引理（留给注册阶段）

- `holds_of_isometryEquiv`、`holds_iff_intrinsicMeasure`、`intrinsic_constant_eq_iInf`、
  `evariance_le_mul_energy_of_iInf_le` 属于 `Poincare.LocalSlope`（`Poincare/LocalSlope/Basic.lean`）。
- `localSlope_apply_comp_isometryEquiv`、`localSlope_energy_comp_isometryEquiv` 属于 `Energy.LocalSlope`。
- `affineSupport_eq_top_of_absolutelyContinuous`、`affineSupport_eq_top_of_evariance_ne_zero`、
  `surjective_intrinsicReconstruct`、`intrinsicIsometryEquiv` 属于 `Probability`（`AffineSupport.lean`）。
- `evariance_comp_measurePreserving` 是通用 Mathlib 缺口。
- `ae_ae_reconstruct`、`ae_memLp_comp_reconstruct`、`lipschitzWith_reconstruct` 属于 `KLS.ConditionalFiber`
  基模块。

## 未做 / 后续

- 未注册、未提交、未推送；未改 Blueprint、`FunctionalInequalities.lean`、`lakefile.toml`、`solutions/README.md`、
  `research/tasks.json`、`research/a-series/ledger.yaml`。
- 若注册：`cor:conditional-fiber-twelve-bound` 可用 `κ = 4`（`KLS.LogConcave.localSlope_constant_le_four_evariance`）
  实例化 `literatureConstant_le_of_fiberBound`。
