# 2026-09-12 — 交给证明会话的提示词：填 `KLS/WIP/AnalyticPrerequisites.lean` 的 sorry

复制下方代码块给证明会话。背景：同日的[陈述记录](2026-09-12-relative-perimeter-prerequisites-statement.md)
把相对周长链条所缺的分析前提写成了 17 条与 KLS 无关的 Lean 陈述；本提示词按可行性分四层给出路线与 API。
陈述本身**不许改**；发现为假或不可证的，保留 `sorry` 并在报告中说明。

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交
db584cd6d46c92f209a44c0f1c829460d327499d；Lake 根目录 formalization/）。
本机 elan 与全部 Lean 工具链已是原生 arm64，lake 调 git 正常，不需要任何 git 包装脚本。

任务：填写 formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean 中的 sorry（17 条）。
该文件是相对周长链条（Blueprint lem:relative-perimeter-smoothing、lem:relative-perimeter-cheeger-infimum）
所缺分析前提的独立陈述：A 等周直径不等式（经 Prékopa–Leindler / Brunn–Minkowski）、B 正则水平集的 Lipschitz 图
与 μH[n−1] 局部有限、C 光滑区域的 Gauss–Green、D 加权 coarea、E Sard。设计、来源与每条的可行性评估见
research/decisions/2026-09-12-relative-perimeter-prerequisites-statement.md；先读它、目标 .lean 的模块文档，
以及 research/naming.md。

先读的仓库材料：
- formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean：SmoothDomain、frontier_inter_eq、
  addHaar_frontier（沿法向单调性的论证，可复用于 outwardNormal_eq）、mollifiedIndicator 与
  mollifiedIndicator_contDiff_lipschitz_mem_Icc 的证明（卷积求导 API 的用法）。注意其 private 引理
  （mollifiedIndicator_eq 等）不能跨文件引用，需要时在本文件重证为 private。
- formalization/FunctionalInequalities/Probability/Line/BrunnMinkowski.lean：一维 Brunn–Minkowski 与
  Prékopa–Leindler（prekopaLeindler 无有界性前提），以及 le_volume_combination 里"紧子集内正则 + iSup"的套路。
- formalization/FunctionalInequalities/Probability/HaarLine.lean：lineEquiv、exists_lintegral_line（沿直线的 Fubini）。
- formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean：norm_gradient_le_of_lipschitz、
  gradient_eq_of_hasFDerivAt、measurable_gradient、ae_differentiableAt_of_locallyLipschitz。

规则：
1. 不改任何 theorem/def 的陈述（类型），包括两个 def 的定义体。若确认某陈述为假或不可证，保留 sorry 并在报告中
   说明反例/障碍。允许加 private 辅助引理与 import；允许新增非 private 的一般引理（命名遵守 research/naming.md），
   但要在报告中列出。
2. 只在这个文件内工作。不改 RelativePerimeter.lean / CheegerInfimum.lean。不加入 FunctionalInequalities.lean、
   lakefile Solutions 根、research/a-series/ledger.yaml、research/check_blueprint.py、research/tasks.json、
   Blueprint \lean{}/\leanok。不 git commit、不 git push。决定记录只追加：新建
   research/decisions/2026-09-1X-relative-perimeter-prerequisites-proofs.md。
3. 编译（在 formalization/ 下）：
     lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites
     lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
   目标：无错误；填完的声明不再有 "declaration uses 'sorry'"；无其他警告。注意：unusedSectionVars linter 对含
   sorry 的声明不报告，所以每填完一条都可能新冒出该警告——用 `omit [...] in`（放在 docstring 之前）处理不再需要的
   section 实例，需要的用 `include ... in`；不要为此改陈述。收尾用
     lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
   并对每个填完的顶层定理 #print axioms，只允许 propext / Classical.choice / Quot.sound。
4. 语法：`∞` 需 `open scoped ContDiff`；`μH[d]` 需 `open MeasureTheory`；`⟪x, y⟫` 是 `open scoped RealInnerProductSpace`
   下的 `inner ℝ x y`；`S + T`、`t • S` 需 `open scoped Pointwise`；`volume` 来自 measureSpaceOfInnerProductSpace；
   `LinearMap.ker` 只接受 LinearMap，对 fderiv 写 `(fderiv ℝ φ x).toLinearMap`（文件里已如此）；`push_neg` 已废弃用 `push Not`。

按层做，先易后难；卡住的留 sorry 并写明卡点。

第一层（给定同文件其他条后是组装，或纯 Mathlib；应全部完成）
- KLS.SmoothDomain.norm_outwardNormal：展开 outwardNormal，`dif_pos hx`；`(U.exists_defining x hx).choose_spec.choose_spec`
  给出 W、φ 的性质，特别是 `fderiv ℝ φ x ≠ 0`（x ∈ W）；`gradient` 与 `fderiv` 互为 `toDual` 像
  （`gradient_eq_toDual_symm_fderiv`? 或用 LipschitzApproximation.norm_gradient_eq_norm_fderiv）⇒ `gradient φ x ≠ 0`；
  `norm_smul`、`norm_inv`、`norm_norm`、`inv_mul_cancel₀`。
- Analysis.ae_forall_fderiv_ne_zero ← sard：`ae_iff`；`{t | ¬ ∀ x, u x = t → Du x ≠ 0} = u '' {x | Du x = 0}`
  （`Set.ext`，`Set.mem_image`，`not_forall`/`not_imp`/`not_not`），再 `measure_mono_null` + sard。
- Analysis.volume_le_ofReal_mul_hausdorffMeasure ← isodiametric：`Measure.hausdorffMeasure_apply`（`μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → Set X)
  (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ (_ : (t n).Nonempty), diam (t n) ^ d`，diam 为 EMetric.diam）。
  只需对 r = 1 的那个 ⨅ 证 `vol S ≤ ofReal(ω/2^n) * (⨅ ...)`：对每个覆盖 `vol S ≤ ∑' vol (t n)`（`measure_iUnion_le` + `measure_mono`）；
  每个 `t n`：若 `EMetric.diam (t n) = ⊤` 则该项为 ⊤（n ≥ 1；n = 0 单独处理，此时 `0^0 = 1`、V 是一点、`vol S ≤ 1`），
  否则 `t n` 有界（`Metric.isBounded_iff_ediam_ne_top`），`isodiametric` 给 `vol (t n) ≤ ofReal(ω (diam/2)^n)`，
  再 `Metric.diam = (EMetric.diam).toReal`（`Metric.diam` 定义）与 `ENNReal.ofReal_rpow_of_nonneg`/`ENNReal.ofReal_pow`
  换成 `ofReal(ω/2^n) * EMetric.diam^n`；`ENNReal.tsum_mul_left`、`le_iInf`、`le_iSup_of_le`。
- Analysis.exists_hausdorffMeasure_levelSet_lt_top ← exists_lipschitzOnWith_levelSet_subset_image：取 N、K、s、g；
  `measure_mono` 到 `g '' s`；`LipschitzOnWith.hausdorffMeasure_image_le hg (d := finrank − 1) hd`（需 `0 ≤ d`；n = 0 时
  前提 `Dφ x ≠ 0` 不可能，先 `rcases Nat.eq_zero_or_pos`）给 `≤ K^d * μH[d] s`；`μH[d]` 在 `ker` 上：
  `finrank ℝ ker = n − 1`（`LinearMap.finrank_range_add_finrank_ker`，range 为 ⊤ 因为非零泛函到 ℝ 满射：
  `LinearMap.range_eq_top`/`finrank_top`/`Module.finrank_self`），于是 `μH[finrank ℝ ker]` 是 `IsAddHaarMeasure`
  （instance `isAddHaarMeasure_hausdorffMeasure`，需要 ker 上的 MeasurableSpace/BorelSpace 实例：`Subtype.instMeasurableSpace`、
  `Subtype.borelSpace`，以及 `FiniteDimensional`、`SecondCountableTopology`——有限维赋范空间自动有），
  Haar ⇒ `IsFiniteMeasureOnCompacts`，有界集包含在紧闭球内（`Bornology.IsBounded.subset_closedBall` + `isCompact_closedBall`）⇒ 有限。
  把 `(finrank ℝ V : ℝ) − 1` 与 `(finrank ℝ ker : ℝ)` 对齐用 `Nat.cast_sub`/`push_cast`。
- Analysis.volume_rpow_add_le_volume_add_rpow ← volume_rpow_mul_le_volume_combination：标准齐次化。`a := vol S ^ (1/n)`、
  `b := vol T ^ (1/n)`（紧 ⇒ 有限，`IsCompact.measure_lt_top`）。若 a = 0 或 b = 0：`x + T ⊆ S + T` 给 `vol T ≤ vol (S+T)`
  （`measure_preimage_add`/`Set.singleton_add`），单调即可。否则 `S' := a⁻¹ • S`、`T' := b⁻¹ • T` 体积为 1
  （`Measure.addHaar_smul volume r s : volume (r • s) = ofReal |r ^ finrank| * volume s`，`ENNReal.rpow_natCast`），
  取 `t := a/(a+b)`（实数），乘法型 BM 给 `1 ≤ vol {t x' + (1−t) y'}`，而该组合集 = `(a+b)⁻¹ • (S + T)`
  （`Set.ext`，`Set.mem_add`、`Set.mem_smul_set`、`smul_smul`、`smul_add`），再 `addHaar_smul` 回去。ENNReal/ℝ 之间用
  `ENNReal.toReal`，`ENNReal.rpow_add`（非零非顶）、`ENNReal.rpow_mul`、`ENNReal.rpow_le_rpow_iff`。
- Analysis.isodiametric ← volume_rpow_mul_le_volume_combination：`S ⊆ closure S`（`measure_mono subset_closure`），
  `Metric.diam_closure`；`closure S` 紧（`hS.isCompact_closure`）故可测非空（S = ∅ 平凡）。`T := (-1 : ℝ) • closure S`
  （体积相等：`Measure.addHaar_smul`，`|(-1)^n| = 1`），`t = 1/2`：组合集 ⊆ `closedBall 0 (diam S / 2)`
  （`z = (x − y)/2`，`norm_sub_le`→`Metric.dist_le_diam_of_mem hS.isCompact_closure.isBounded hx hy`，`dist_eq_norm`）；
  `InnerProductSpace.volume_closedBall`（需 `Nontrivial V`；n = 0 分支：`Module.finrank_zero_iff` ⇒ Subsingleton，
  `vol S ≤ vol univ = 1`：`measureSpaceOfInnerProductSpace` 的 `volume` 是 `(stdOrthonormalBasis ℝ V).toBasis.addHaar`，
  `Basis.addHaar_self` 给平行多面体测度 1，空基的平行多面体为 `{0} = univ`），`ω_n = √π^n / Γ(n/2+1)` 与
  `KLS.unitBallVolume` 定义逐字相同（`unfold KLS.unitBallVolume`）。左边 `vol^{1/2} · vol^{1/2} = vol`：
  `ENNReal.rpow_add`（vol 非零非顶；零时平凡），或 `ENNReal.rpow_add_of_nonneg`。
- Analysis.hausdorffMeasure_finrank_eq_smul_volume ← volume_le_ofReal_mul_hausdorffMeasure：
  (i) `μH[n]` 是 Haar（instance `isAddHaarMeasure_hausdorffMeasure`；注意实例的指标是 `(finrank ℝ E : ℝ)`，与陈述一致），
  Haar 唯一性 `MeasureTheory.Measure.isAddLeftInvariant_eq_smul`（`Haar/Unique.lean`，`to_additive` 自 `isMulLeftInvariant_eq_smul`）
  或 `Measure.addHaarMeasure_unique` 给 `μH[n] = c • volume`，`c := addHaarScalarFactor μH[n] volume`，`c ≠ 0, ⊤`
  （`addHaarScalarFactor_pos_of_isAddHaarMeasure`，NNReal）。
  (ii) 下界 `2^n/ω_n ≤ c`：把 (i) 代入上一条于 `closedBall 0 1`（体积 `ω_n`，`volume_closedBall`），除以 `ω_n`。
  (iii) 上界 `c ≤ 2^n/ω_n`：对 `B := closedBall 0 1`、`ε > 0`，`Besicovitch.exists_disjoint_closedBall_covering_ae volume
  (fun _ ↦ Ioo 0 ε) B ...`（`Mathlib/MeasureTheory/Covering/Besicovitch.lean`，需 `SFinite volume`；给出可数族两两不交的闭球
  `closedBall (x i) (r i)`，`x i ∈ B`，`r i < ε`，`volume (B \ ⋃) = 0`）。则
  `μH[n] B ≤ μH[n] (⋃) + μH[n] (B \ ⋃)`；第二项由 (i) 为 `c • 0 = 0`；第一项 `≤ ∑ μH[n] (closedBall) ≤ ∑ (2 r i)^n`
  （单集覆盖，`Measure.hausdorffMeasure_le_liminf_tsum` 或直接 `hausdorffMeasure_apply` 的 ⨅ 取一元覆盖 + `EMetric.diam_closedBall`）
  `= (2^n/ω_n) ∑ volume (closedBall (x i) (r i)) = (2^n/ω_n) volume (⋃) ≤ (2^n/ω_n) volume (closedBall 0 (1+ε))`
  （不交 `measure_iUnion`，`x i ∈ B, r i < ε` ⇒ 球 ⊆ `closedBall 0 (1+ε)`）。令 `ε → 0`（`volume_closedBall` 连续于半径），
  与 (i) 比较得 `c · ω_n ≤ 2^n`。ENNReal 乘除：`ENNReal.mul_le_iff_le_inv`、`ENNReal.div_eq_inv_mul`。
  最后 `Measure.ext`/`smul` 形式：`ENNReal.ofReal (2^n/ω_n) = (c : ℝ≥0∞)` 由两边不等式 + `le_antisymm`。
- Analysis.volume_rpow_mul_le_volume_combination ← prekopaLeindler：与一维 `le_volume_combination` 同套路：先对紧 `K ⊆ S`、`L ⊆ T`
  证，`t • K + (1−t) • L` 紧（`IsCompact.smul`、`IsCompact.add`）故可测，取 `f := K.indicator 1`、`g := L.indicator 1`、
  `h := (t • K + (1−t) • L).indicator 1`（都可测：`measurable_one.indicator`），PL 前提逐点：`0^t = 0`（`Real.zero_rpow ht0.ne'`）、
  `1^t = 1`；结论中 `∫⁻ ofReal (indicator 1) = vol`（`lintegral_indicator_one`）；再 `MeasurableSet.measure_eq_iSup_isCompact`
  + `ENNReal.rpow` 单调 + `ENNReal.iSup_mul`/`ENNReal.mul_iSup`（rpow 与 iSup 交换：`ENNReal.rpow_iSup`? 一维文件里有
  private `rpow_iSup`，可复制），组合集包含关系 `t • K + (1−t) • L ⊆ {t x + (1−t) y | x ∈ S, y ∈ T}`。

第二层（Mathlib + 仓库输入，应能完成）
- Analysis.prekopaLeindler（n 维）：对维数归纳。建议不在抽象 V 上归纳，而是：
  (a) 先证 `Fin n → ℝ`（乘积 Lebesgue `volume`）上的版本 `prekopaLeindler_pi`，对 n 归纳：n = 0 平凡（一点空间，积分即取值，
  `Fin 0 → ℝ` 上 `volume univ = 1`）；n+1 用 `MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0` 与
  `MeasureTheory.volume_preserving_piFinSuccAbove`（`Mathlib/MeasureTheory/Constructions/Pi.lean`）把 `Fin (n+1) → ℝ` 拆成
  `ℝ × (Fin n → ℝ)`，`lintegral_prod`（Tonelli，需 AEMeasurable）；对固定的 `x' y'`，切片函数 `s ↦ f (s, x')` 等满足一维 PL 前提
  （用 `hfgh` 于 `(s, x')`、`(s', y')`），一维 PL（`Probability.Line.prekopaLeindler`）给切片积分的不等式；再对
  `F x' := ∫⁻ s, ofReal (f (s, x'))` 等用 n 维归纳假设。**障碍**：一维 PL 陈述的是 ℝ 值函数 + `ENNReal.ofReal`，而切片积分
  `F, G, H` 取值 ℝ≥0∞（可能为 ⊤，且不是 `ofReal` 形式）。先证一个 ℝ≥0∞ 值版本 `prekopaLeindler_ennreal`
  （`f g h : ℝ → ℝ≥0∞` 可测，`f x ^ t * g y ^ (1−t) ≤ h (t x + (1−t) y)`）：由截断 `min (f x) N` 与 `ENNReal.toReal`
  归约到 ℝ 值版本，再 `lintegral_iSup` 单调收敛（`Monotone`，`Measurable.min`）；同样处理 n 维的归纳假设，最好整个归纳都在
  ℝ≥0∞ 值形式下进行，最后再特化到 `ofReal ∘ f`。可测性：`Measurable.lintegral_prod_right'`。
  (b) 从 `Fin n → ℝ` 搬到 V：`(stdOrthonormalBasis ℝ V).repr : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)`，
  `measurePreserving_repr_symm`（见 `VolumeOfBalls.lean` 中 `volume_ball` 的证明）与
  `EuclideanSpace.volume_preserving_measurableEquiv`（到 `Fin n → ℝ`）；线性等价保持 `t • x + (1−t) • y`
  （`map_add`、`map_smul`），`lintegral_map_equiv`/`MeasurePreserving.lintegral_comp`。
- Analysis.exists_lipschitzOnWith_levelSet_subset_image：Mathlib 的隐函数定理 `HasStrictFDerivAt.implicitFunction`
  （`Analysis/Calculus/Implicit.lean`，需 `f'` 满射 + `ker f'` 闭补；对 `f' = fderiv ℝ φ x : V →L[ℝ] ℝ ≠ 0`，满射由
  `LinearMap.range_eq_top` + 一维目标，闭补由 `ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range`）：
  `ψ := HasStrictFDerivAt.implicitFunction φ f' hφ' hsurj hker : ℝ → ker f' → V`，`implicitFunction_apply_image`
  （`∀ᶠ y in 𝓝 x, ψ (φ y) (proj (y − x)) = y`）给出：N 内每个水平集点 y 是 `ψ (φ x) (proj (y − x))`，即
  `g := ψ (φ x)`、`s := proj '' (N ∩ 水平集)`（有界，因 N 可取球，proj 连续线性）。`g` 的 Lipschitz：
  `ImplicitContDiff.contDiffAt_implicitFunction`（`Analysis/Calculus/ImplicitContDiff.lean`）给 `ContDiffAt ℝ 1 (uncurry ψ) (φ x, 0)`，
  再 `ContDiffAt.exists_lipschitzOnWith`（`ContDiff/RCLike.lean`）给某邻域上的 Lipschitz；缩小 N 使 `s` 落进该邻域。
  `HasStrictFDerivAt`：由 `ContDiff ℝ 1 φ` 得 `hφ.contDiffAt.hasStrictFDerivAt le_rfl`。
- KLS.SmoothDomain.outwardNormal_eq：设 `(W₁, φ₁)` 是 `choose` 出的对，`(W, φ)` 是给定的对，两者在 x 的邻域内有相同的
  负集 `{φ₁ < 0} = U ∩ W₁ ∩ W = {φ < 0}`。证 `Dφ₁ x = λ • Dφ x`，`λ > 0`：对任意 v 与 `Dφ x v < 0`，沿 `x + t v`
  一阶展开（`HasFDerivAt.lim` 或 `hasDerivAt_iff_tendsto_slope`，见 `frontier_inter_eq` 的证明）得小 t > 0 时 `φ (x + t v) < 0`
  ⇒ `φ₁ (x + t v) < 0` ⇒ `Dφ₁ x v ≤ 0`（否则同样展开给正值）。于是半空间 `{Dφ x v < 0} ⊆ {Dφ₁ x v ≤ 0}`，线性代数：
  取 `v₀` 使 `Dφ x v₀ = 1`，对任意 w 写 `w = (w − (Dφ x w) v₀) + (Dφ x w) v₀`，第一项在 `ker (Dφ x)` 上（其上 `Dφ₁ x = 0`，
  由 `±` 两侧极限），得 `Dφ₁ x w = (Dφ₁ x v₀) (Dφ x w)`，`λ := Dφ₁ x v₀ ≥ 0`，`λ ≠ 0` 因 `Dφ₁ x ≠ 0`。
  再 `gradient` 是 `fderiv` 的 `toDual.symm` 像（线性），`norm_smul`、正数归一化。写成 private 引理
  `fderiv_eq_smul_fderiv_of_forall_lt_imp_le`。
- KLS.SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal ← integral_divergence_eq_integral_inner_outwardNormal：
  对每个 `e : V`，`F := fun x ↦ η x • e`（`ContDiff.smul_const`，`HasCompactSupport.smul_right`），
  `divergence F x = fderiv ℝ η x e = ⟪gradient η x, e⟫`：`fderiv` 的 `smul_const` 规则 `fderiv_smul_const`，
  `LinearMap.trace` 的秩一公式（`LinearMap.trace_smulRight`? 若无：`(fderiv ℝ η x).smulRight e` 的迹等于 `fderiv ℝ η x e`，
  用 `LinearMap.trace_eq_matrix_trace` 对任一基或 `LinearMap.trace_eq_sum_inner`/正交基展开），`gradient` 与内积：
  `HasGradientAt`/`gradient_eq`。两边取与 e 的内积：`integral_inner`（`∫ ⟪e, f x⟫ = ⟪e, ∫ f⟫`，需可积；被积函数紧支撑连续
  ⇒ 可积，边界侧用 `IntegrableOn` + `outwardNormal` 在 frontier 上的连续性/有界性 + 局部有限），`ext_inner_right ℝ`。
- KLS.SmoothDomain.gradient_mollifiedIndicator_eq ← setIntegral_gradient_eq_integral_smul_outwardNormal：
  `mollifiedIndicator x = ∫_U η (x − y) dy`（`integral_indicator`/`setIntegral` 改写）；对 x 求导：卷积形式
  `U.carrier.indicator 1 ⋆[lsmul ℝ ℝ, volume] φ.normed volume`（在本文件重证 RP 的 private `mollifiedIndicator_eq`），
  `HasCompactSupport.hasFDerivAt_convolution_right` + `convolution_precompR_apply` 给
  `fderiv (mollified) x v = ∫ 𝟙_U(y) · (fderiv η (x − y)) v dy`；另一边：`η_x := fun y ↦ φ.normed volume (x − y)`，
  `ContDiff ℝ 1`（`contDiff_normed.comp (contDiff_const.sub contDiff_id)`）、紧支撑（`hasCompactSupport_normed` 经
  `HasCompactSupport.comp_homeomorph` 或 `.comp_isClosedEmbedding`），`gradient η_x y = −gradient (φ.normed) (x − y)`
  （`HasFDerivAt.comp` 与 `hasFDerivAt_const_sub`/`(hasFDerivAt_id).const_sub`，`fderiv_comp`），代入 C2，`integral_neg`。
  两边在 `V` 中取值，用 `ext_inner_right ℝ` 逐分量比较更省事。

第三层（缺基础设施，尽力而为；预计留 sorry）
- Analysis.sard：Milnor 的归纳证明（对 n 归纳；`C_i` = 前 i 阶导数全零的集合）。建议先做能做的：
  (a) n = 0：`Subsingleton V`，像是单点，`measure_singleton`。
  (b) n = 1：`V ≃L[ℝ] ℝ`（`ContinuousLinearEquiv.ofFinrankEq`/`LinearEquiv.toContinuousLinearEquiv`），Mathlib 同维数 Sard
  `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`（`Function/Jacobian.lean`）对 `u ∘ e.symm : ℝ → ℝ`，行列式 = 导数。
  (c) 一般 n：需要 Fubini（沿坐标切片，`volume_preserving_piFinSuccAbove`）、Taylor 余项（`taylor_mean_remainder`/
  `ContDiff` 的 `isLittleO`）与紧集上的一致估计；Mathlib 无现成框架。若做不动，留 sorry 并写明已完成 (a)(b)。
  注意陈述用锐指数 `ContDiff ℝ (finrank ℝ V) u`；`C^∞` 特例由 `hu.of_le le_top` 得到，但不要改陈述。
- Analysis.aemeasurable_lintegral_levelSet 与 lintegral_enorm_gradient_mul_eq_lintegral_levelSet（coarea）：
  Evans–Gariepy §3.4 的路线：Rademacher（`LipschitzWith.ae_differentiableAt`）；在 `{∇u ≠ 0}` 的开子集上用 B2 的隐函数把
  u 局部拉直为坐标投影，同维数面积公式 `lintegral_image_eq_lintegral_abs_det_fderiv_mul`（`Function/Jacobian.lean`）+ Fubini
  给局部 coarea（需 `ℋ^{n−1}` 于 Lipschitz 图 = `√(1+|∇g|²)` 加权 Lebesgue，见下 C1 的同一障碍）；`{∇u = 0}` 上左边为 0、
  右边由 Sard（`C¹` Lipschitz 不够——EG 用 `C¹` 逼近 + Lipschitz 函数的 `ℋ^{n−1}(A ∩ {u = t})` 对 `A ⊆ {∇u = 0}` 的直接估计）；
  Lipschitz 一般情形再由 `C¹` 逼近（Whitney 延拓，Mathlib 无）。**预计留 sorry**；若做，先做 `u` 为 `C¹` 且 `{∇u ≠ 0}` 上的局部版本
  作为 private 引理。可测性那条独立于 coarea 恒等式，可先试：`t ↦ surfaceMeasure (A ∩ {u = t})` 的可测性经
  `{(t, y) | u y = t}` 的乘积可测性 + Fubini 型论证（`Measurable.lintegral_prod_right`），但需要 `surfaceMeasure` 的 s-有限性
  （`μH` 一般不是 s-有限的，限制到 `A` 有界紧片上则有限——用局部有限 + 可数并）。
- KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal（Gauss–Green，本文件最重）：
  (a) 局部形式：F 支撑在某定义邻域 W 内，且 `{φ = 0} ∩ W` 是超平面 `P = (ℝ ∙ ν)ᗮ` 上 `C¹` 函数 `g` 的图（由 B2 + 沿 ν 的严格
  单调性，见 RP 的 `addHaar_frontier`）。换元 `Φ (z, s) := z + (g z + s) • ν`（`P × ℝ → V`，`C¹` 微分同胚，雅可比行列式 1）：
  `integral_image_eq_integral_abs_det_fderiv_smul` 把 `∫_U div F` 化为 `∫_{s<0} (div F) ∘ Φ`；沿 s 的 FTC
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` + Fubini（`Probability.exists_lintegral_line` 的 Bochner 版本，或
  `MeasurePreserving.integral_prod` 经 `lineEquiv`）；剩下要证的是边界项 `∫_P G(z, g z) √(1+|∇g z|²) dz = ∫_{graph} G dℋ^{n−1}`
  ——**Lipschitz 图的面积公式**，Mathlib 只有同维数面积公式。这是一条独立的、Mathlib 级的子义务；写成 private 或公开引理
  `hausdorffMeasure_graph_eq`，做不动就把它作为唯一残留 sorry。
  (b) 全局：`SmoothPartitionOfUnity.exists_isSubordinate`（`Geometry/Manifold/PartitionOfUnity.lean`，取 `𝓘(ℝ, V)` 模型）
  或 `exists_smooth_zero_one_of_isClosed` 手工拼接：`tsupport F ∩ frontier U` 紧，有限个定义邻域覆盖，加上 `U` 内部与
  `closure U` 外部（那里 F 的贡献分别是 `∫ div F = 0`：全空间紧支撑场的散度积分为零——这本身要证，用 Fubini + 一维 FTC，
  Mathlib 的 `integral_divergence_of_hasFDerivAt_off_countable` 只对盒子，取足够大的盒子含 `tsupport F` 即可直接用它）。
  `divergence` 对 `ψ • F` 的 Leibniz 律：`divergence (ψ • F) = ⟪∇ψ, F⟫ + ψ divergence F`（`fderiv_smul`，`LinearMap.trace` 线性 +
  秩一迹）。

第四层（若第三层的 C1 完成）
- 无。C2、C3、B1、E2、A2a、A2 均已在第一/二层作为组装列出。

报告格式：每条义务一行：名称 | 完成/未完成 | 关键 API | 卡点。新增的非 private 引理单列。给出 `-DwarningAsError=true`
编译摘要与 `#print axioms` 结果。不要声称未编译通过的内容已完成。若发现某条陈述为假，单列"陈述问题"并给反例，不改类型。
```
