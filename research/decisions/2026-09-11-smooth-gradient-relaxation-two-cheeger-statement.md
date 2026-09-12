# 2026-09-11 — `thm:smooth-gradient-relaxation-two-cheeger`：陈述设计（仅陈述，无证明）

## 决定

- 为 Blueprint 唯一 `\notready` 节点 `thm:smooth-gradient-relaxation-two-cheeger` 写出 Lean 陈述，全部证明体为
  `sorry`，放在独立 WIP 模块 `formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean`。
- Cheeger 能量的约定按 Blueprint 原文选定为**局部斜率约定**：`Ch_ν = ½ · (f ↦ ∫ |∇f|² dν 在局部 Lipschitz、
  L²(ν)、斜率能量有限的测试类上的序列 L² 松弛)`。渐近 Lipschitz 常数 `Lip_a` 版本另行定义，两者相等作为独立
  义务陈述，不做定义性等同。选定动作只在 `Energy.Cheeger.energy := Cheeger.ofLocalSlope` 一处记录。
- 测试类取仓库已有的文献测试域 `Energy.LocalSlope.Admissible`（局部 Lipschitz、`MemLp 2`、`energy ≠ ⊤`），
  不新造第三个 Lipschitz 类。
- "下半连续松弛"用项目的序列松弛实现，并以三条陈述刻画它就是下半连续包络：`lowerSemicontinuous_relaxation`、
  `relaxation_toLp_le`、`le_relaxation_of_lowerSemicontinuous`。
- 仿射支撑传输沿用 `def:intrinsic-affine-energy` 的同一构造：`Cheeger.Intrinsic.energy μ :=
  (Cheeger.energy (intrinsicMeasure μ)).comap (toIntrinsicL2 μ)`。
- 不填 sorry；不加入 `FunctionalInequalities.lean` 聚合导入、lakefile、ledger、`check_blueprint.CERTIFICATES`、
  Blueprint `\lean{}`/`\leanok`、`tasks.json`；不提交、不推送。

## Lean 陈述（formech 风格）

命名空间均省略 `FunctionalInequalities`。

主张：

1. `Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger (μ : ProbabilityMeasure E) (f : Lp ℝ 2 μ) :
   SmoothGradient.Intrinsic.energy μ f = 2 * Cheeger.Intrinsic.energy μ f` —— Blueprint 定理本体，对有限维实内积空间上
   的任意 Borel 概率律，两边允许 `⊤`。
2. 坐标层 `Energy.SmoothGradient.relaxation_eq_localSlope (ν) : relaxation ν = LocalSlope.relaxation ν`
   与 `relaxation_eq_two_mul_cheeger`。
3. 无条件方向 `SmoothGradient.localSlope_relaxation_le`：光滑测试是斜率测试且能量相同
   （`Test.localSlope_admissible`、`Test.localSlope_energy`，不需绝对连续，因 `LocalSlope.apply_eq_norm_gradient` 逐点成立）。
4. 两种 Cheeger 约定相等：`LocalSlope.relaxation_eq_asymptoticLipschitz`、`Cheeger.energy_eq_ofAsymptoticLipschitz`。

不主张：任何 Poincaré 不等式、常数有限性、Cheeger–Buser 比较、单个测试上原始斜率能量与松弛能量一致、
`h_μ`（`def:isoperimetric-cheeger-scale`）与 `Ch_μ` 的任何关系、以 `Lip_a` 定义 `Cheeger.energy`。

有限范围（可用现有已认证输入证明的版本）：`relaxation_le_localSlope_of_absolutelyContinuous`、
`relaxation_eq_localSlope_of_absolutelyContinuous`（`ν ≪ m`，`m` Haar，无需边界零测）、
`Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`、
`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger`（对数凹律，经 `hμ.intrinsic_absolutelyContinuous`）。

零维：`LocalSlope.relaxation_eq_zero_of_subsingleton`、`Cheeger.energy_eq_zero_of_subsingleton`、
`AsymptoticLipschitz.apply_eq_zero_of_subsingleton`；主定理包含一点仿射支撑（`0 = 2 * 0`）。

编译：`lake env lean FunctionalInequalities/Energy/WIP/Cheeger.lean` 仅有 26 条 `declaration uses 'sorry'`
警告，无其他警告（四条 `rfl` 展开引理已加 `omit ... in`）。`#check` 核对：`LocalSlope.preEnergy/relaxation`、
`Cheeger.energy` 只需 `[NormedAddCommGroup V] [MeasurableSpace V]`；`Cheeger.Intrinsic.energy` 与
`SmoothGradient.Intrinsic.energy` 同样不含 `CompleteSpace E`；各 sorry 定理带完整欧氏实例表
（`InnerProductSpace`、`CompleteSpace`、`BorelSpace`、`SecondCountableTopology`、`FiniteDimensional`），
其中 `relaxation_eq_zero_of_subsingleton` 等零维引理实际只需前两者，证明时可按需 `omit`。

## 逐句对齐（Blueprint ↔ Lean）

| Blueprint 句子 | Lean | 结论 |
|---|---|---|
| "On the affine support" | `Cheeger.Intrinsic.energy μ` 在 `Probability.intrinsicMeasure μ`（方向空间，继承环境度量）上计算 | 一致 |
| "the standard metric Cheeger energy normalized as one half of …" | `Cheeger.ofLocalSlope ν = ⟨fun f ↦ LocalSlope.relaxation ν f / 2⟩`，`Cheeger.energy := ofLocalSlope` | 一致；½ 写在定义里 |
| "… the lower-semicontinuous relaxation …" | `LocalSlope.relaxation := (preEnergy ν).sequentialRelaxation`；`lowerSemicontinuous_relaxation` + `relaxation_toLp_le` + `le_relaxation_of_lowerSemicontinuous` 刻画为最大下半连续下界 | 一致（Lean 把"lsc 松弛 = 序列松弛"作为可证义务写出，不做定义） |
| "… of the squared local slope" | `Energy.LocalSlope.apply`（单动点斜率）、`LocalSlope.energy ν f = ∫⁻ apply f x ^ 2` | 一致 |
| （测试类未写明，"standard"） | `Energy.LocalSlope.Admissible`：局部 Lipschitz、L²、斜率能量有限 | **待澄清**：AGS 用（有界/紧支）Lipschitz 函数类；不同 Lipschitz 类的松弛相等是常规截断论证，但本模块未陈述该比较 |
| "After transporting it to ambient real L²(μ)" | `Cheeger.Intrinsic.energy μ := comap (toIntrinsicL2 μ)`，与 `SmoothGradient.Intrinsic.energy` 同一传输 | 一致 |
| "prove 𝓔^can_μ = 2 Ch_μ" | `Intrinsic.energy_eq_two_mul_cheeger : energy μ f = 2 * Cheeger.Intrinsic.energy μ f`，∀ `f : Lp ℝ 2 μ`，含 `⊤` | 一致（Lean 显式覆盖无穷值） |
| 附注："The factor 2 is part of the intended normalization" | 定义中 `/ 2`，定理中 `2 *`；`Cheeger.two_mul_energy` | 一致 |
| 附注："relaxation of the local slope and asymptotic-Lipschitz relaxation must be distinguished" | 两个独立定义 `Cheeger.ofLocalSlope`、`Cheeger.ofAsymptoticLipschitz`（后者基于新定义 `AsymptoticLipschitz.apply = ⨅ r>0, ⨆ y z ∈ B(x,r), |f y − f z|/d(y,z)`）；逐点 `LocalSlope.apply_le_asymptoticLipschitz`；松弛比较 `relaxation_le_asymptoticLipschitz`、`relaxation_eq_asymptoticLipschitz` | 更强：给出了区分与比较的陈述 |
| 附注："their comparison for singular measures has no source recorded in the bibliography" | `relaxation_eq_asymptoticLipschitz`、`relaxation_eq_localSlope` 按 Blueprint 定理无条件陈述；另给 `_of_absolutelyContinuous` 有限范围版本 | **待澄清**：奇异情形的数学来源。`references.bib` 已含 `AmbrosioGigliSavare2013Density`（Rev. Mat. Iberoam. 29, 2013），其弱梯度等价定理覆盖完备可分、局部有限测度的度量测度空间，应即为此比较的来源；本记录不改 Blueprint 章节（共享文件） |
| `\uses{def:selected-canonical-frontend}` | `import …SmoothGradient.Intrinsic.Basic`，定理左边即 `SmoothGradient.Intrinsic.energy` | 一致 |
| 45 章："The isoperimetric number h_μ is not the metric energy Ch_μ" | `Energy.Cheeger` 与 `KLS.Isoperimetry` 互不引用；模块头注明 | 一致 |
| （未提零维） | 三条零维引理；主定理无维数假设 | 更强 |

## sorry 义务清单（26 条，按文件顺序）

文件 `formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean`。"API"列为建议使用的仓库/Mathlib 入口。

| # | 行 | Lean 名称（省略 `FunctionalInequalities.Energy`） | 陈述 | 对应 Blueprint 句子 | 建议 API |
|---|---|---|---|---|---|
| 1 | 98 | `AsymptoticLipschitz.apply_const` | 常数的 `Lip_a` 为 0 | 附注：区分 Lip_a | 仿 `LocalSlope.apply_const`：`iInf_le_of_le 1`，`dist_self`，`div_zero`，`simp` |
| 2 | 103 | `AsymptoticLipschitz.apply_eq_zero_of_subsingleton` | 一点空间上 `Lip_a = 0` | 零维 | `Subsingleton.elim` 化为常数 + #1 |
| 3 | 108 | `AsymptoticLipschitz.apply_le_of_lipschitzWith` | `LipschitzWith K f → Lip_a f x ≤ K` | 附注：区分 Lip_a | `LipschitzWith.dist_le_mul`，`div_le_iff₀`，`ENNReal.ofReal_le_ofReal`，`iInf_le_of_le 1` |
| 4 | 137 | `LocalSlope.apply_le_asymptoticLipschitz` | 逐点 `|∇f| ≤ Lip_a f` | 附注：区分 Lip_a | 展开两个 `⨅⨆`，`iInf_mono`，`le_iSup₂_of_le y hy x (by simpa)`（取 `z = x`，`dist x x = 0 < r`） |
| 5 | 147 | `LocalSlope.energy_le_asymptoticLipschitz` | 斜率能量 ≤ Lip_a 能量 | 同上 | `lintegral_mono` + #4 + `pow_le_pow_left'` |
| 6 | 152 | `LocalSlope.Admissible.of_asymptoticLipschitz` | Lip_a 测试 ⇒ 斜率测试 | 同上 | 结构字段逐条；有限性由 #5 与 `ne_top_of_le_ne_top` |
| 7 | 175 | `LocalSlope.coe_preEnergy_energy` | `↑((preEnergy ν).energy f) = energy ν f.1` | "squared local slope" | `ENNReal.coe_toNNReal f.2.finite_energy` |
| 8 | 193 | `LocalSlope.lowerSemicontinuous_relaxation` | 松弛下半连续 | "lower-semicontinuous relaxation" | `PreEnergy.lowerSemicontinuous_sequentialRelaxation (preEnergy ν)` |
| 9 | 198 | `LocalSlope.relaxation_toLp_le` | 松弛 ≤ 测试原始能量 | 同上 | `PreEnergy.sequentialRelaxation_toAmbient_le (preEnergy ν) ⟨f, hf⟩` + #7 |
| 10 | 205 | `LocalSlope.le_relaxation_of_lowerSemicontinuous` | 松弛是最大 lsc 下界 | 同上 | `PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous`，把 `hQ` 经 #7 改写为对 `P.Test` 的界 |
| 11 | 214 | `LocalSlope.relaxation_eq_zero_of_subsingleton` | 零维松弛为 0 | 零维 | 一点空间上 `f : Lp ℝ 2 ν` a.e. 等于常数 `c := f default`（`Subsingleton.elim`），测试 `fun _ ↦ c` 可容许（`LocallyLipschitz` 常数、`memLp_const`、能量 0 由 `LocalSlope.apply_eq_zero_of_subsingleton` + `lintegral_zero`），其 `toLp` 与 `f` 相等（`Lp.ext`/`MemLp.toLp` 的 a.e. 同类），再用 `sequentialRelaxation_toAmbient_le` 与 `le_antisymm _ bot_le` |
| 12 | 246 | `LocalSlope.relaxation_le_asymptoticLipschitz` | 斜率松弛 ≤ Lip_a 松弛 | 附注：区分 Lip_a | `PreEnergy.sequentialRelaxation_comp_le (P := AsymptoticLipschitz.preEnergy ν) (Q := LocalSlope.preEnergy ν) id continuous_id`，每个 Lip_a 测试用 #6 映为斜率测试，能量由 #5 + `ENNReal.toNNReal_mono` |
| 13 | 256 | `LocalSlope.relaxation_eq_asymptoticLipschitz` | 两种约定松弛相等 | 附注："must be distinguished … comparison for singular measures" | 方向 ≤ 是 #12；方向 ≥：需 AGS 2013 Density 型论证。欧氏情形可绕开 Hopf–Lax：任意 `ν` 下，对局部 Lipschitz `f` 取磨光 `f * ρ_n`（`Energy.Euclidean.LipschitzApproximation` 中的 `mollify` 机制），`‖∇(f*ρ_n)(x)‖ ≤ Lip(f, B(x, 2/n)) → Lip_a f x`，再用 `sequentialRelaxation_le_of_recovery_sequences`（`Relaxation/LowerSemicontinuous.lean`）。这给出 `SmoothGradient.relaxation ≤ AsymptoticLipschitz.relaxation`；与 #16（无条件 `LocalSlope.relaxation ≤ SmoothGradient.relaxation`）合起来只得到 `LocalSlope ≤ Smooth ≤ Lip_a`，仍缺 `Lip_a 松弛 ≤ 斜率松弛`（AGS Thm 6.2 的核心）。**奇异律下这是真正的开放义务**，见后续 |
| 14 | 291 | `Cheeger.two_mul_energy` | `2 * (x / 2) = x` 于 `ℝ≥0∞` | 附注：factor 2 | `ENNReal.mul_div_cancel'`（`two_ne_zero`、`ENNReal.ofNat_ne_top`）或 `ENNReal.div_eq_inv_mul` + `ENNReal.mul_inv_cancel` |
| 15 | 297 | `Cheeger.energy_eq_ofAsymptoticLipschitz` | 两约定 Cheeger 能量相等 | 同 #13 | `Functional.ext` + #13 |
| 16 | 302 | `Cheeger.energy_eq_zero_of_subsingleton` | 零维 Cheeger 能量 0 | 零维 | #11 + `ENNReal.zero_div` |
| 17 | 344 | `SmoothGradient.Test.localSlope_admissible` | 光滑测试 ∈ `LocalSlope.Admissible` | "squared local slope"（测试类包含） | `ContDiff.locallyLipschitz (f.contDiff.of_le le_top)`（Mathlib `Analysis/Calculus/ContDiff/RCLike`）；`f.memLp_two`；有限性由 #18 |
| 18 | 349 | `SmoothGradient.Test.localSlope_energy` | `LocalSlope.energy ν f = ↑f.energy` | 同上 | `LocalSlope.apply_eq_norm_gradient f x (f.contDiff.differentiable le_top).differentiableAt`（无测度假设），`lintegral_congr`，`ofReal_integral_eq_lintegral_ofReal f.gradient_sq_integrable`，`ENNReal.ofReal_pow`，`Test.coe_energy` |
| 19 | 357 | `SmoothGradient.localSlope_relaxation_le` | 无条件 `LocalSlope.relaxation ≤ SmoothGradient.relaxation` | 定理主体（≥ 方向） | `PreEnergy.sequentialRelaxation_comp_le (SmoothGradient.preEnergy ν) (LocalSlope.preEnergy ν) id continuous_id`，测试映射 `f ↦ ⟨f, #17⟩`，`toL2` 同类（`rfl`），能量由 #18 + `ENNReal.toNNReal_coe` |
| 20 | 365 | `SmoothGradient.relaxation_le_localSlope_of_absolutelyContinuous` | `ν ≪ m` 时反向不等式 | 定理主体（≤ 方向，有限范围） | 用 `PreEnergy.sequentialRelaxation_le_of_recovery_sequences (P := LocalSlope.preEnergy ν) (Q := SmoothGradient.preEnergy ν)`；对每个可容许 `g`，`LocalSlope.admissible_iff_memLp_gradient ν m hac` 给 `MemLp (gradient g) 2`，`Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2 hac (ContinuousLinearMap.id ℝ V) g` 给光滑紧支序列 `gSeq`（`ContDiff ℝ ∞`、`MemLp 2`、梯度 L² 收敛）；构造 `SmoothGradient.Test`（`gradient_sq_integrable` 由 `memLp_two_iff_integrable_sq_norm`），`toL2` 收敛用 `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`；能量收敛：`‖·‖₂²` 连续 + `LocalSlope.energy_eq_lintegral_gradient ν m hac g hlip`（或 `Energy.LocalSlope.energy_eq_integral_gradient`，在 `Poincare/LipschitzGradient/Comparison.lean`）；`liminf` 用 `Tendsto.liminf_eq`。参考 `Energy.LipschitzGradient.localSlope_holds_of_relaxation` 的同型论证 |
| 21 | 373 | `SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous` | `ν ≪ m` 时松弛相等 | 同上 | `Functional.ext` + `le_antisymm` #20 #19 |
| 22 | 381 | `SmoothGradient.relaxation_eq_localSlope` | 无条件松弛相等 | 定理主体（含奇异律） | ≥：#19。≤：奇异情形无仓库输入。可行路线：(a) 对 `ν` 任意，磨光给出 `Smooth ≤ Lip_a 松弛`（见 #13），再用 AGS 2013 `Lip_a 松弛 = 斜率松弛`；(b) 或直接证 AGS 的 `|Df|_{*,slope} = |Df|_{*,Lip_a}`。两者都需要新的分析基础设施（Hopf–Lax 半群或等价的 Cheeger 能量的 weak upper gradient 理论），当前 Mathlib 无 |
| 23 | 387 | `SmoothGradient.relaxation_eq_two_mul_cheeger` | 坐标形式 `relaxation ν f = 2 * Cheeger.energy ν f` | "𝓔^can = 2 Ch" | #22 逐点 + `Cheeger.energy_apply` + #14 |
| 24 | 401 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger` | **Blueprint 定理** | 定理主体 | `SmoothGradient.Intrinsic.energy_apply`、`Cheeger.Intrinsic.energy_apply`，代入 #23 于 `ν := intrinsicMeasure μ`、`f := toIntrinsicL2 μ f` |
| 25 | 407 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous` | 内在律 `≪ m` 时的定理 | 定理主体（有限范围） | 同 #24，用 #21 代替 #22 |
| 26 | 432 | `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | 对数凹律的定理 | 定理主体（KLS 路线用例） | #25 with `m := Measure.addHaar`、`hμ.intrinsic_absolutelyContinuous Measure.addHaar`（`KLS/LogConcave/AbsoluteContinuity.lean`）；对照 `KLS.LogConcave.intrinsicSmooth_constant_eq_localSlope` 的写法 |

依赖顺序建议：#1–#7、#14 → #8–#12、#16–#19 → #20、#21 → #25、#26（到此为止只用已认证输入，可先做）；
#13、#15、#22、#23、#24 为奇异情形，等基础设施决定。

## 缺少的基础设施与来源

- 奇异律下 `Lip_a` 松弛与斜率松弛相等（#13）以及由此的无条件主定理（#22–#24）：AGS 2013 Density 定理在欧氏
  载体上的局部证明。Mathlib（`db584cd6`）没有 Hopf–Lax 半群、weak upper gradient 或度量 Sobolev 空间。
  `references.bib` 已有 `AmbrosioGigliSavare2013Density`；Blueprint 30 章附注"no source recorded"可在核对该文
  Theorem 6.2（或对应编号）后更新，本会话不改共享的 Blueprint 章节。
- 测试类变体（全局 Lipschitz / 有界 / 紧支撑 Lipschitz）的松弛相等未陈述；若日后要与 AGS 原文逐字对齐，需要为
  另一测试类再建 `PreEnergy` 并证明截断恢复序列。`Energy.LipschitzGradient.relaxation`（算子式、需 `≪ m`）是仓库
  中的第三种表现，其与 `LocalSlope.relaxation` 的关系也未陈述。

## 未做

- 未注册：不在 `FunctionalInequalities.lean`、lakefile `Solutions` 根、`research/a-series/ledger.yaml`、
  `check_blueprint.CERTIFICATES`、Blueprint `\lean{}`/`\leanok`、`tasks.json`；`\notready` 标记保留。
- 未提交、未推送。
- 未改动任何共享文件（HANDOFF、README、Blueprint 章节、ledger、tasks.json、naming.md）。若日后转正，需要在
  `research/naming.md` 表中加入 `Energy.AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`、
  `Energy.LocalSlope.{preEnergy,relaxation}`、`Energy.Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`，
  并把模块从 `Energy/WIP/` 移到 `Energy/Cheeger/` 与 `Energy/LocalSlope/`。
