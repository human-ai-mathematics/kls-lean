# 2026-09-12 — 相对周长链条的分析前提：独立 Lean 陈述（仅陈述，无证明）

承接同日的[可行性判断与提示词](2026-09-12-relative-perimeter-prerequisites-statement-prompt.md)。
本轮把 `lem:relative-perimeter-smoothing` → `lem:relative-perimeter-cheeger-infimum` 链条所缺的分析前提
写成**与 KLS 无关**的 Lean 陈述，全部证明体为 `sorry`，放进一个新的 WIP 模块。未注册、未提交、未推送，
未改动任何既有文件的既有声明（`RelativePerimeter.lean` 的 5 条与 `CheegerInfimum.lean` 的 9 条 `sorry`
类型原样保留）。

## 决定

- 新文件 `formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean`，17 条 `sorry`，
  两个 `def`（`Analysis.divergence`、`KLS.SmoothDomain.outwardNormal`，均有真实定义体）。
  一般命题放在命名空间 `FunctionalInequalities.Analysis`（五个 section：`Isodiametric`、`LipschitzGraph`、
  `LevelSet`、`Coarea`、`Sard`，另有 `Divergence`），只有 Gauss–Green 一组放在 `FunctionalInequalities.KLS.SmoothDomain`
  下，因为散度定理需要一个区域。
- 只导入 `FunctionalInequalities.KLS.WIP.RelativePerimeter`（取 `SmoothDomain`、`unitBallVolume`、
  `surfaceMeasure`、`mollifiedIndicator`）与 `Mathlib.LinearAlgebra.Trace`（散度用迹定义）。
- A 组选 **Brunn–Minkowski 路线**而非 Steiner 对称化（理由见下）。
- B 组**拒绝**「限制到水平集的 `μH[n−1]` 是局部有限测度」这种写法（它是假的），改为逐点陈述。
- E 组用 Sard 的**锐指数** `C^n`（`n = finrank`）而不是 `C^∞`：更强且是教科书原形；仓库需要的 `C^∞` 情形由
  `ContDiff.of_le` 得到。

## 陈述清单（17 条 + 2 个定义）

下表「对应」列指 `RelativePerimeter.lean`（RP）与 `CheegerInfimum.lean`（CI）中的既有 `sorry`。
「可行性」列写明钉住的 Mathlib（v4.33.0，`db584cd6`）已有什么、缺什么。

### A. 等周直径不等式（section `Isodiametric`）

| 全名（省略 `FunctionalInequalities.`） | 内容 | 来源 | 对应 | 可行性 |
|---|---|---|---|---|
| `Analysis.prekopaLeindler` | `V` 上的 n 维 Prékopa–Leindler：`(∫f)^t (∫g)^{1−t} ≤ ∫h`，`f x^t g y^{1−t} ≤ h(t x + (1−t) y)`，与一维版 `Probability.Line.prekopaLeindler` 逐字同型（`*` 换 `•`） | Prékopa 1971/73，Leindler 1972；Gardner, *The Brunn–Minkowski inequality*, Bull. AMS 39 (2002) §7 | 无直接对应；A 组中间产物 | 一维基例已证（`Probability/Line/BrunnMinkowski.lean`）。归纳需要 `V ≃ W × ℝ` 的正交分解与沿直线的 Fubini，仓库有 `Probability.lineEquiv`/`exists_lintegral_line`；Mathlib 无任何维数 ≥ 2 的 PL。中等偏重 |
| `Analysis.volume_rpow_mul_le_volume_combination` | 乘法型 Brunn–Minkowski：`vol S^t · vol T^{1−t} ≤ vol{t x + (1−t) y}`，`S, T` 可测非空，右端外测度；组合集写法与 `KLS.LogConcave` 一致 | Gardner 2002 §4；Schneider, *Convex Bodies* §7.1 | 无直接对应 | 由 PL 取指示函数 + 内正则（紧子集）得到，与一维 `le_volume_combination` 同套路。中等 |
| `Analysis.volume_rpow_add_le_volume_add_rpow` | 加法型 Brunn–Minkowski：`vol S^{1/n} + vol T^{1/n} ≤ vol(S+T)^{1/n}`，`S, T` 紧非空，`[Nontrivial V]`（`n = 0` 时 `1/0 = 0`、`x^0 = 1` 会使不等式为假） | 同上 | 无直接对应 | 由乘法型经齐次性得到。中等偏易 |
| `Analysis.isodiametric` | `vol S ≤ ofReal(ω_n (diam S/2)^n)`，`S` 有界任意（外测度）；用 `Metric.diam` + `Bornology.IsBounded`，因为无界集的 `Metric.diam` 为 0 | Bieberbach 1915（n=2），Urysohn 1924；Evans–Gariepy §2.2 Thm 1；Federer 2.10.33 | `KLS.hausdorffNormalized_finrank_eq_volume`（RP:119）的核心输入 | Mathlib 无。路线：`vol S ≤ vol(closure S)`，`½S + ½(−S) ⊆ closedBall 0 (diam/2)`，乘法型 BM（`t = ½`，`vol(−S) = vol S`），`InnerProductSpace.volume_closedBall`。给定 BM 后是短证明 |
| `Analysis.volume_le_ofReal_mul_hausdorffMeasure` | `vol S ≤ ofReal(ω_n/2^n) · μH[n] S`（归一化恒等式的一半） | Evans–Gariepy §2.2 Thm 2 的第一半 | 同上 | 由 `isodiametric` 对 `μH` 的覆盖定义（`mkMetric`）逐覆盖求和即得。易（给定 A1） |
| `Analysis.hausdorffMeasure_finrank_eq_smul_volume` | `μH[n] = ofReal(2^n/ω_n) • volume`，`V` 显式 | Evans–Gariepy §2.2 Thm 2；Federer 2.10.35 | **是 `KLS.hausdorffNormalized_finrank_eq_volume` 的一般形式**：展开 `hausdorffNormalized` 后 `smul_smul` + `ENNReal.ofReal_mul` 即得。未改 RP 中该定理的类型 | Haar 唯一性（`isAddHaarMeasure_hausdorffMeasure`、`isAddLeftInvariant_eq_smul`）给 `μH[n] = c • volume`；下界 `c ≥ 2^n/ω_n` 由上一条；上界另需 Vitali/Besicovitch 覆盖（`Besicovitch.exists_disjoint_closedBall_covering_ae` 在 Mathlib 中已有）。中等 |

**Steiner vs. Brunn–Minkowski。** 选 BM 路线，因为：(i) 一维基例已经在仓库里且无有界性前提；(ii) 中间产物
（n 维 PL、两种 BM）本身是 Mathlib 级别的独立贡献，而 Steiner 对称化的中间引理（保测性、直径不增、
n 次迭代的可测性保持）在 Lean 里既重又无复用价值；(iii) BM 路线的最后一步只用 `volume_closedBall` 与
`t = ½`，不需要「等号仅在球取到」。代价是 A 组比 Steiner 多两条中间陈述，但它们承重（对数凹理论里迟早要用 BM）。

**承重说明（重申第一节的判断）。** A 组不解锁任何下游节点：`hausdorffNormalized_finrank_eq_volume` 在全仓库
无使用点，`relativePerimeter` 只用 `ℋ^{n−1}`。写进来是因为 `surfaceMeasure` 的归一化约定必须由一条陈述而不是
注释钉住，而这条陈述的一般形式就是 A2。

### B. C¹ 超曲面的面积测度局部有限（section `LipschitzGraph`、`LevelSet`）

| 全名 | 内容 | 来源 | 对应 | 可行性 |
|---|---|---|---|---|
| `Analysis.exists_lipschitzOnWith_levelSet_subset_image` | `φ` 为 `C¹`，`Dφ x ≠ 0`：存在 `N ∈ 𝓝 x`、有界 `s ⊆ ker(Dφ x)`、Lipschitz 于 `s` 的 `g : ker(Dφ x) → V`，使 `N ∩ {φ = φ x} ⊆ g '' s`。只需 `[NormedSpace ℝ V] [CompleteSpace V]`，不需有限维 | 隐函数定理的 Lipschitz 图形式（任何分析教材） | 无直接对应；B1 的路线 | Mathlib 有 `HasStrictFDerivAt.implicitFunction`（`Analysis/Calculus/Implicit.lean`，`ImplicitFunctionData`），给出 `C¹` 隐函数；`C¹` ⇒ 局部 Lipschitz 由 `ContDiff` + 有界导数得到。中等 |
| `Analysis.exists_hausdorffMeasure_levelSet_lt_top` | 同前提：`∃ N ∈ 𝓝 x, μH[n−1] (N ∩ {φ = φ x}) < ⊤` | Evans–Gariepy §2.4.1 / Federer 2.10.11（Lipschitz 像的 `ℋ^k` 界） | **`SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`（RP:418）的一般命题**：边界点取定义邻域 `(W, φ)`，`frontier ∩ W = {φ = 0} ∩ W`（`frontier_inter_eq`），`N ∩ W` 即所需邻域；非边界点用闭 frontier 的补集 | 给定 B2 后：`LipschitzOnWith.hausdorffMeasure_image_le`（已有）+ `μH[k]` 在 `k` 维内积空间（`ker` 作为子模的诱导结构）上是 Haar 测度（`isAddHaarMeasure_hausdorffMeasure`，已有）故在有界集上有限 + `LinearMap.finrank_range_add_finrank_ker` 得 `finrank ker = n − 1`。易 |

**为什么是逐点陈述。** 「`μH[n−1].restrict {x ∈ W | φ x = c}` 是 `IsLocallyFiniteMeasure`」对开集 `W` 内的正则水平集
是**假**的：`n = 2`，`W = {x > 0}`，`φ(x, y) = y − sin(1/x)`，`Dφ ≠ 0` 处处成立，但水平集在原点每个邻域内长度无穷。
它对光滑区域的闭 frontier 成立，是因为每个 frontier 点都有自己的定义邻域；这正是 RP:418 那条成立而其「一般化」
不成立的原因。

### C. Gauss–Green / 散度定理（namespace `KLS.SmoothDomain`，section `Normal`、`GaussGreen`）

| 全名 | 内容 | 来源 | 对应 | 可行性 |
|---|---|---|---|---|
| `Analysis.divergence`（def） | `div F x := tr (fderiv ℝ F x)`，用 `LinearMap.trace`，与基无关；不可微处为 0 | — | — | 定义 |
| `KLS.SmoothDomain.outwardNormal`（def） | 边界点处取 `exists_defining` 选出的定义函数 `φ`，值 `‖∇φ x‖⁻¹ • ∇φ x`；边界外为 0 | — | — | 定义（`Classical.choose`） |
| `KLS.SmoothDomain.outwardNormal_eq` | 对**任意**定义对 `(W, φ)`，`outwardNormal x = ‖∇φ x‖⁻¹ • ∇φ x`（良定义性） | 两个定义函数的梯度在公共零集上平行且同向（都在 `U` 内为负） | 无直接对应；C1–C3 的前提 | 需要「两个 `C¹` 函数有相同的局部零集且同侧 ⇒ 梯度正比例」，可由 B2 的图表示或沿法向的一维单调性（RP 中 `addHaar_frontier` 已用过的论证）得到。中等 |
| `KLS.SmoothDomain.norm_outwardNormal` | frontier 上 `‖ν‖ = 1` | — | 同上 | 直接由定义与 `fderiv ≠ 0`。易 |
| `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n−1}`，`F` 为 `C¹` 紧支撑向量场，`ℋ^{n−1} = surfaceMeasure V`（标准归一化），`U`、`∂U` 可无界 | Maggi, *Sets of Finite Perimeter*, Ch. 9（`C¹` 边界开集的 Gauss–Green）；Evans–Gariepy §5.8 | 无直接对应；C 组主定理 | Mathlib 的 `integral_divergence_of_hasFDerivAt_off_countable` 只对 `Fin (n+1) → ℝ` 中的盒子。路线：单位分解（`SmoothPartitionOfUnity`，Mathlib 有）+ 图坐标下换元（`integral_image_eq_integral_abs_det_fderiv_smul`）或沿法向的一维分部积分 + Fubini；面积元 `√(1+|∇g|²)` 与 `ℋ^{n−1}` 的对应还需要 Lipschitz 图上的面积公式（Mathlib 只有同维数面积公式）。**本链条最重的一条** |
| `KLS.SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal` | `∫_U ∇η = ∫_{∂U} η ν dℋ^{n−1}`，`η` 为 `C¹` 紧支撑标量，即 `D𝟙_U = −ν ℋ^{n−1}⌊∂U` | Maggi Ch. 9；Ambrosio–Fusco–Pallara §3.3 | 无直接对应；C1 的标量形式 | 由 C1 对 `F = η • e`（`e` 取正交基）逐分量得到。易（给定 C1） |
| `KLS.SmoothDomain.gradient_mollifiedIndicator_eq` | `∇(η ⋆ 𝟙_U)(x) = −∫_{∂U} η(x−y) ν(y) dℋ^{n−1}(y)`，`η = φ.normed volume` | 同上 | **是 `SmoothDomain.enorm_gradient_mollified_le`（RP:580）背后的精确公式**：取范数、`‖ν‖ = 1`、`norm_integral_le_lintegral_norm` 即得 | 由 C2 对 `η_x := η(x − ·)`（`∇η_x(y) = −(∇η)(x−y)`）与 RP 中已有的 `hasFDerivAt_convolution_right`/`convolution_precompR_apply` 得到。易（给定 C2） |

### D. 加权 coarea 公式（section `Coarea`）

| 全名 | 内容 | 来源 | 对应 | 可行性 |
|---|---|---|---|---|
| `Analysis.aemeasurable_lintegral_levelSet` | `t ↦ ∫_{u = t} g dℋ^{n−1}` 关于 Lebesgue 测度 a.e. 可测（`u` Lipschitz，`g` 可测） | Evans–Gariepy §3.4（coarea 定理的可测性部分）；Federer 3.2.12 | 无直接对应；经典定理的组成部分，`lintegral` 形式下不影响 D1 的意义但下游 Fubini 需要 | Mathlib 无。中等 |
| `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | `∫ ‖∇u‖ g dvol = ∫_ℝ ∫_{u=t} g dℋ^{n−1} dt`，`u` **只需 Lipschitz**，`gradient` 在不可微处为 0（Rademacher 零测） | Evans–Gariepy §3.4 Thm 2 及其加权推论；Federer 3.2.12；Maggi Ch. 13 | **强于 `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（CI:112）**：去掉 `ContDiff ℝ 1 u`；后者是直接特化 | Mathlib 有：Rademacher（`LipschitzWith.ae_differentiableAt`）、同维数面积公式（`lintegral_image_eq_lintegral_abs_det_fderiv_mul`）、`μH` 的 Lipschitz 像界。缺：coarea 本身。标准证明（EG）需要 `{∇u ≠ 0}` 上的局部拉直/`C¹` 逼近 + 面积公式 + 对 Lipschitz 的逼近论证。**重** |

### E. Sard 定理（section `Sard`）

| 全名 | 内容 | 来源 | 对应 | 可行性 |
|---|---|---|---|---|
| `Analysis.sard` | `u : V → ℝ` 为 `C^n`（`n = finrank ℝ V`，Lean 中 `ContDiff ℝ (Module.finrank ℝ V) u`），`volume (u '' {Du = 0}) = 0`；只需 `[NormedSpace ℝ V] [FiniteDimensional ℝ V]`，`V` 上不需测度 | Sard 1942；Federer 3.4.3；Milnor, *Topology from the Differentiable Viewpoint* §3（`C^∞` 证明）；Whitney 1935（`C^{n−1}` 反例） | 无直接对应；E2 的来源 | Mathlib 只有同维数版本 `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`（`Function/Jacobian.lean`）。Milnor 的对维数归纳证明需要 Fubini 与 Taylor 余项估计，Mathlib 材料齐备但无现成框架。**重** |
| `Analysis.ae_forall_fderiv_ne_zero` | 同前提：`∀ᵐ t, ∀ x, u x = t → Du x ≠ 0`（a.e. `t` 是正则值） | 同上 | **给出 `SmoothDomain.ae_exists_superlevel`（CI:87）**：正则值 `t` 处，`U = {t < u}` 开，`frontier ⊆ {u = t}`（已证 `frontier_superlevel_subset`），定义函数 `φ = t − u`、`W = V` | 由 `sard` 取补集即得。易（给定 E1） |

## 对应关系总表

| 既有 `sorry` | 本轮陈述 | 关系 |
|---|---|---|
| RP:119 `hausdorffNormalized_finrank_eq_volume` | `Analysis.hausdorffMeasure_finrank_eq_smul_volume`（← `isodiametric` ← BM ← PL） | 一般形式，`smul_smul` 即得；**不承重** |
| RP:418 `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` | `Analysis.exists_hausdorffMeasure_levelSet_lt_top`（← `exists_lipschitzOnWith_levelSet_subset_image`） | 一般命题；组装需 `frontier_inter_eq` |
| RP:580 `SmoothDomain.enorm_gradient_mollified_le` | `SmoothDomain.gradient_mollifiedIndicator_eq`（← C2 ← C1） | 精确公式，取范数即得 |
| CI:87 `SmoothDomain.ae_exists_superlevel` | `Analysis.ae_forall_fderiv_ne_zero`（← `sard`） | 组装需 `frontier_superlevel_subset` |
| CI:112 `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | 直接特化（去掉 `C¹`） |

**未被本轮覆盖的既有 `sorry`（9 条）**，因为它们不是「一般分析前提」而是仓库内的分析工作或纯组装：
RP 的 `lintegral_enorm_gradient_mollified_homothety_le`、`exists_smooth_recovery_sequence`（组装）；
CI 的 `lintegral_enorm_gradient_distanceCutoff_le`（Rademacher + 水平集上梯度 a.e. 为零；Mathlib 已有 Rademacher）、
`exists_smooth_approximation_lipschitz`（磨光收敛）、`lintegral_minkowskiContent_superlevel_le`（ADG 2017 Lemma 3.2）、
`smoothConstant_mul_lintegral_min_superlevel_le`、`minkowskiConstant_mul_lintegral_min_superlevel_le`、
`minkowskiConstant_le_smoothConstant`、`smoothConstant_le_minkowskiConstant`（组装）。

## 不以这种形式陈述的内容（及理由）

1. **B 组的「局部有限测度」形式**：假命题，见上；已改为逐点形式。
2. **没有重述** `hausdorffNormalized_finrank_eq_volume` 与 `ae_exists_superlevel`：二者分别由 A2、E2 经几行推出，重述只会制造重复义务。
3. **C 组无法完全脱离仓库对象**：Gauss–Green 需要一个区域类，仓库已有 `SmoothDomain`，重新定义「`C¹` 边界开集」只会产生第二个平行概念。若日后转正，`divergence`、`outwardNormal` 与 C1–C3 应随 `SmoothDomain` 一起搬到 `KLS/Isoperimetry/SmoothDomain.lean`；A、B、D、E 四组应搬到独立的 `FunctionalInequalities/Analysis/` 目录（或直接上游到 Mathlib）。
4. **A 组不承重**（见第一节）。仍然写入，因为它钉住 `surfaceMeasure` 的归一化约定；若 owner 认为约定检查可以用注释代替，可以整组删除而不影响任何下游。
5. **Sard 的 `C^n` 而非 `C^∞`**：更强、教科书原形、Mathlib PR 的自然目标；仓库只用 `C^∞` 特例。若审阅认为应与提示词逐字一致，改为 `ContDiff ℝ ∞ u` 是纯弱化，不影响任何下游。
6. **D 组只需 Lipschitz**：比 CI:112 的 `C¹ ∧ Lipschitz` 更一般，也是 Evans–Gariepy 的原形。加权 coarea 对局部 Lipschitz（如 `C¹` 无 Lipschitz 界）也成立，但需要 McShane 延拓论证；本轮不写，因为 CI 的消费者都是全局 Lipschitz 的。

## 编译

在 `formalization/` 下（原生 arm64 工具链，无 git 包装脚本）：

```
lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites   # Build completed successfully
lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
```

两次 `lake env lean` 均恰好输出 17 条 `declaration uses 'sorry'`，无其他警告或错误。
两个 `def` 的 section 变量都被定义体使用，未加任何 `omit` 或 `set_option linter.unusedSectionVars`。
`#check` 复核：`sard` 的阶数为 `↑(Module.finrank ℝ V)`；`hausdorffMeasure_finrank_eq_smul_volume` 的 `V` 显式；
`exists_lipschitzOnWith_levelSet_subset_image` 只带 `NormedAddCommGroup`、`NormedSpace ℝ`、`CompleteSpace`；
Gauss–Green 的内积显示为 `inner ℝ (F x) (U.outwardNormal x)`。

编译中遇到的两处调整：`LinearMap.ker` 在此 Mathlib 版本只接受 `LinearMap`，对 `fderiv ℝ φ x : V →L[ℝ] ℝ`
须写 `(fderiv ℝ φ x).toLinearMap`（直接类型上升会在 `isDefEq` 超时）；`divergence` 同样用 `.toLinearMap`。

## 工具链发现（对后续仅陈述轮次有用）

- `unusedSectionVars` linter **跳过证明体含 `sorry` 的声明**：这就是为什么 RP:418、RP:580、CI:87 等带着未用的
  `[CompleteSpace V]`、`[SecondCountableTopology V]` 却在 `-DwarningAsError=true` 下无警告。后果：仅陈述文件可以用宽松的
  `variable` 块；但每填完一条 `sorry`，该声明的未用 section 实例会立刻被报告，需要逐条加 `omit ... in`。这也是提示词里
  「`unusedSectionVars` 逐轮报告」现象的机制。两个有真实定义体的 `def` 不受此保护，因此各自放在只含所需实例的 section。
- 此 Mathlib 的 `LinearMap.ker` 只接受 `LinearMap`；对 `fderiv ℝ φ x : V →L[ℝ] ℝ` 须写 `(fderiv ℝ φ x).toLinearMap`，
  直接的类型上升 `(… : V →ₗ[ℝ] ℝ)` 会在 `isDefEq` 中耗尽 200000 心跳而不是报类型错误。

## 后续

证明会话的提示词见同日的
[sorry 提示词](2026-09-12-relative-perimeter-prerequisites-sorry-prompt.md)（四层：组装与纯 Mathlib；中等；缺基础设施；空）。
HANDOFF、`research/verification.md`、`KLS/README.md` 与两个伴随 WIP 模块的模块文档已加指向本模块的说明；
`tasks.json` 中两个节点的 `infrastructure: missing` 分类不变，因为义务是有类型的，不是已证的。

## 未做

- 未注册：`FunctionalInequalities.lean` 聚合导入、lakefile `Solutions` 根、`research/a-series/ledger.yaml`、
  `research/check_blueprint.py` 的 `CERTIFICATES`、`research/tasks.json`、Blueprint 的 `\lean{}`/`\leanok` 均未动。
- 未 `git commit`、未 `git push`。
- 未尝试证明任何一条；未为可证性弱化任何一条。伴随 WIP 模块只改了模块文档，声明与证明体未动。
