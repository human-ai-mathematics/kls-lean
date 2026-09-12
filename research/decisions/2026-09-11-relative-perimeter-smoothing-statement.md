# 2026-09-11 — `lem:relative-perimeter-smoothing`：定义骨架与陈述（仅陈述，无证明）

## 决定

- 为 Blueprint 附录 A 的 `lem:relative-perimeter-smoothing`（基础设施于同日被另一会话核对为 `missing`，见
  [核对记录](2026-09-11-spectator-and-relative-perimeter-infrastructure.md)）写出缺失的定义骨架与 Lean 陈述，
  全部证明体为 `sorry`，放在独立 WIP 模块 `formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean`。
- **光滑区域** `KLS.SmoothDomain V`：结构，字段 `carrier`（开集）、`isOpen`、`exists_defining`（每个边界点有开邻域 `W`
  与全局 `C^∞` 函数 `φ`，`fderiv ℝ φ ≠ 0` 于 `W`，`carrier ∩ W = {y ∈ W | φ y < 0}`）。这是"开集、局部位于其 `C^∞`
  边界一侧"的精确化；只需 `[NormedAddCommGroup V] [NormedSpace ℝ V]`。
- **相对周长** `KLS.relativePerimeter ρ Ω U := ∫⁻ x in frontier U.carrier ∩ Ω, ofReal (ρ x) ∂μH[finrank ℝ V − 1]`，
  用 Mathlib 的 Hausdorff 测度 `μH[d]`（`V` 自身度量）。权重 `ρ` 与开集 `Ω` 显式参数；引理中取 Borell 密度与
  `Ω = interior ν.support`。
- 主引理 `KLS.RelativePerimeter.exists_smooth_recovery_sequence` 对任意带 Borell 密度（相对 Haar 测度）的概率律 `ν`
  陈述，比 Blueprint 的"对数凹律的内在律"更强（后者由 `KLS.LogConcave.exists_isBorellDensity` 提供密度）。
- 不填 sorry；不注册；不提交、不推送；不改共享文件。

## Lean 陈述（formech 风格）

主张（`KLS.RelativePerimeter.exists_smooth_recovery_sequence`）：`hρ : IsBorellDensity ν m ρ`（`m` Haar），
`U : SmoothDomain V`，`relativePerimeter ρ (interior ν.support) U ≠ ⊤` ⇒
`∃ u : ℕ → V → ℝ`，每个 `u j` 全局 `C^∞`、全局 Lipschitz、取值于 `[0,1]`；
`∫⁻ ‖u j − 𝟙_U‖ₑ dν → 0`；`limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ relativePerimeter ρ (interior ν.support) U`。

中间义务（都是 Blueprint 证明中显式使用、而钉住的 Mathlib 缺少的步骤）：

- `SmoothDomain.frontier_inter_eq`：定义邻域内 `frontier U ∩ W = {φ = 0} ∩ W`；
- `SmoothDomain.homothety`（位似像仍是光滑区域）、`indicator_homothety`（`𝟙_{cU} = 𝟙_U ∘ homothety a c⁻¹`，即 Blueprint 的 `v_s`）；
- `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`（曲面测度局部有限，Tonelli 用）；
- `SmoothDomain.addHaar_frontier`（`∂U` Haar 零测，故 `ν`-零测）；
- `SmoothDomain.hausdorff_frontier_homothety`（膀胀标度 `‖c‖^{n−1}`，即 `s^{1−n}`）；
- `SmoothDomain.mollifiedIndicator`、`enorm_gradient_mollified_le`（Gauss–Green 的唯一被用形式：
  `‖∇(η⋆𝟙_U)(x)‖ ≤ ∫_{∂U} η(x−y) dℋ^{n−1}(y)`）、`mollifiedIndicator_contDiff_lipschitz_mem_Icc`；
- `IsBorellDensity.exists_le`（`M = sup ρ < ∞`，Blueprint 小节前言）、`le_rpow_mul_of_combination`
  （`ρ x ≤ (M/b₀)^{(1−s)/s} ρ y`，`y = s x + (1−s) b`，`ρ b ≥ b₀`）；
- `RelativePerimeter.tendsto_indicator_homothety`（`v_s → 𝟙_U` 于 `L¹(ν)`）；
- `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`（一步定量界
  `∫‖∇u_{s,ε}‖ dν ≤ s^{1−n}(M/b₀)^{(1−s)/s} P_ρ(U)`，条件 `sε/(1−s) < r`）。

不主张：一般形式的 Gauss–Green、外法向场、有限周长集/多元 BV、周长的下半连续性
（`P_ρ(U) ≤ liminf ∫‖∇u_j‖`）、`lem:relative-perimeter-cheeger-infimum` 的任何部分、与 Minkowski 边界含量
`KLS.Isoperimetry.boundaryContent` 的比较。

有限范围：无附加假设；Blueprint 前言的 `n ≥ 1` 未作为前提。

零维：`V` 为一点，开集边界为空，`relativePerimeter = 0`（`relativePerimeter_eq_zero_of_frontier_eq_empty`），常序列
`u_j = 𝟙_U` 满足结论；`μH[−1]` 只在空集上取值，为 0。

编译：`lake env lean FunctionalInequalities/KLS/WIP/RelativePerimeter.lean` 仅 17 条 `sorry` 警告，无其他警告。
`#check`：`SmoothDomain.mk` 只需 `NormedAddCommGroup`、`NormedSpace ℝ`；`relativePerimeter` 只需
`InnerProductSpace`、`MeasurableSpace`、`BorelSpace`（Hausdorff 测度）；定理带完整欧氏实例表。
需导入 `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct` 以获得 `HasContDiffBump V`。

## 逐句对齐（Blueprint ↔ Lean）

| Blueprint | Lean | 结论 |
|---|---|---|
| 前言："a smooth domain is open and locally lies on one side of its smooth boundary" | `SmoothDomain`：开集 + 局部定义函数 `φ`，`fderiv ≠ 0`，`U ∩ W = {φ<0} ∩ W`；`frontier_inter_eq` | 一致；"一侧"由定义函数精确化 |
| 前言：`P_ρ(U) = ∫_{∂U∩Ω} ρ dℋ^{n−1}`，`n = dim V ≥ 1` | `relativePerimeter ρ Ω U`，`d = (finrank ℝ V : ℝ) − 1`，Mathlib `μH[d]` | 一致；`n ≥ 1` 未作前提（更强，零维平凡） |
| 前言：`M = sup ρ < ∞`（`ρ ≥ √(b₀ρ(x))` 于半径一半的球） | `IsBorellDensity.exists_le` | 一致 |
| "For every smooth domain U with P_ρ(U) < ∞" | `(U : SmoothDomain V) (hU : relativePerimeter ρ (interior ν.support) U ≠ ⊤)` | 一致 |
| "globally smooth Lipschitz functions 0 ≤ u_j ≤ 1" | `ContDiff ℝ ∞ (u j) ∧ (∃ K, LipschitzWith K (u j)) ∧ ∀ x, u j x ∈ Icc 0 1` | 一致 |
| "u_j → 𝟙_U in L¹(ν)" | `Tendsto (fun j ↦ ∫⁻ ‖u j x − 𝟙_U x‖ₑ ∂ν) atTop (𝓝 0)` | 一致（`lintegral` 形式，等价于 `eLpNorm 1`） |
| "limsup_j ∫‖∇u_j‖ dν ≤ P_ρ(U)" | `limsup (fun j ↦ ∫⁻ ‖gradient (u j) x‖ₑ ∂ν) atTop ≤ relativePerimeter …` | 一致（ENNReal，无可积性前提） |
| "The domain and the convex carrier may be unbounded" | 无有界性假设 | 一致 |
| `\uses{thm:borell-logconcave-density}`；ν 为对数凹律的内在律，ρ 其 Borell 密度，Ω = int K_ν | 前提 `IsBorellDensity ν m ρ`，`Ω = interior ν.support`（`closure_convexHull_intrinsic_support` 说明二者一致） | 更强：任意带 Borell 密度的律 |
| 证明："v_s(x) = 𝟙_U(a + s(x−a))，its domain is the outward dilation of U by 1/s" | `SmoothDomain.homothety a (1/s)`，`indicator_homothety` | 一致 |
| 证明："dilation multiplies its total variation by s^{1−n}" | `hausdorff_frontier_homothety`（`‖c‖^{n−1}`，`c = 1/s`） | 一致 |
| 证明："The distributional derivative of 𝟙_U is its oriented surface measure … convolution, triangle inequality" | `enorm_gradient_mollified_le`（逐点范数界） | 一致（只陈述证明所需的推论） |
| 证明：`ρ(x) ≤ (M/b₀)^{(1−s)/s} ρ(y)`，`y = sx + (1−s)b` | `IsBorellDensity.le_rpow_mul_of_combination` | 一致 |
| 证明：`∫‖∇u_{s,ε}‖ dν ≤ s^{1−n}(M/b₀)^{(1−s)/s} P_ρ(U)`，条件 `sε/(1−s) < r` | `lintegral_enorm_gradient_mollified_homothety_le`（`φ.rOut = ε`） | 一致 |
| 证明："Tonelli on unbounded boundaries; local finiteness of the smooth surface measure suffices" | `isLocallyFiniteMeasure_hausdorff_frontier` | 一致 |
| 证明："∂U is ν-null"，"v_s → 𝟙_U away from ∂U" | `addHaar_frontier` + `ν ≪ m`；`tendsto_indicator_homothety` | 一致 |
| 证明："a piece of ∂U on ∂K contributes no cost" | `Ω` 限制在 `relativePerimeter` 定义里；比较引理中 `ρ x > 0 ⇒ y ∈ Ω` | 一致 |

## sorry 义务清单（17 条，按文件顺序）

见同日提示词文件 [sorry 提示词](2026-09-11-relative-perimeter-smoothing-sorry-prompt.md)，其中按"可直接证 / 需要
分析基础设施"分层并给出每条的建议 API。分层结论：

- 可用钉住 Mathlib 直接证（10 条）：`frontier_inter_eq`、`empty`、`univ`、`homothety`（两个字段）、
  `indicator_homothety`、`measurableSet`、`relativePerimeter_eq_zero_of_frontier_eq_empty`、
  `IsBorellDensity.le_rpow_mul_of_combination`、`tendsto_indicator_homothety`；
- 中等（3 条）：`hausdorff_frontier_homothety`（`hausdorffMeasure_homothety_image` + 同胚保边界）、
  `IsBorellDensity.exists_le`（已认证 `exists_bounds_of_isCompact` + 对数凹 + 球质量 ≤ 1）、
  `mollifiedIndicator_contDiff_lipschitz_mem_Icc`（Mathlib 卷积/`ContDiffBump` API）；
- 需要新基础设施（4 条）：`isLocallyFiniteMeasure_hausdorff_frontier`、`addHaar_frontier`（光滑超曲面局部为
  Lipschitz 图像 + `hausdorffMeasure_image_le`/Fubini）、`enorm_gradient_mollified_le`（Gauss–Green 推论，
  Mathlib 散度定理只对盒子）、以及依赖它们的 `lintegral_enorm_gradient_mollified_homothety_le` 与主引理
  `exists_smooth_recovery_sequence`（后两者在前述引理给定后是组装）。

## 未做

- 未注册（聚合导入、lakefile、ledger、`check_blueprint.CERTIFICATES`、Blueprint 锚点、tasks.json 均未动）；
  tasks.json 的 `infrastructure: missing` 结论保持，本模块把"missing"的对象写成了带 sorry 的 Lean 定义与义务。
- 未提交、未推送。未改任何共享文件。
- 若日后转正：模块拆到 `KLS/Isoperimetry/SmoothDomain.lean`、`KLS/Isoperimetry/RelativePerimeter.lean`；
  `research/naming.md` 表中加入 `KLS.SmoothDomain`（`carrier`、`homothety`、`mollifiedIndicator`）、
  `KLS.relativePerimeter`、`KLS.IsBorellDensity.exists_le`/`le_rpow_mul_of_combination`、
  `KLS.RelativePerimeter.exists_smooth_recovery_sequence`。

## 补记（2026-09-11 晚）：两处陈述修正

在为 `lem:relative-perimeter-cheeger-infimum` 写陈述时发现本记录的骨架有两处与 Blueprint 不一致，均已在
`KLS/WIP/RelativePerimeter.lean` 中修正（只改定义与仍为 `sorry` 的陈述，另一会话已完成的 13 条证明不受影响，重新编译通过）：

1. **Hausdorff 测度归一化。** Mathlib 的 `μH[d]` 用规范 `diam^d`，经典定义用 `ω_d (diam/2)^d`，因此在欧氏空间上
   `μH[d] = (2^d/ω_d) · ℋ^d_std`，`d ≥ 2` 时二者不同（`μH[n]` 只在 sup 范数的 `ι → ℝ` 上等于 Lebesgue）。原
   `relativePerimeter` 直接用 `μH[n−1]`，于 `n ≥ 3` 时比 Blueprint 的 `P_ρ` 大 `2^{n−1}/ω_{n−1}` 倍：平滑引理因此变弱
   （右边更大），而两种 Cheeger 下确界相等则会变成假命题。修正：新增 `KLS.unitBallVolume d`、
   `KLS.hausdorffNormalized V d := ofReal (ω_d / 2^d) • μH[d]`、`KLS.surfaceMeasure V := hausdorffNormalized V (finrank − 1)`，
   `relativePerimeter` 与 `enorm_gradient_mollified_le` 改用 `surfaceMeasure V`；并以 sorry 陈述
   `hausdorffNormalized_finrank_eq_volume`（`ℋ^n_std = volume`，等周直径不等式）钉住约定。已证的
   `hausdorff_frontier_homothety` 仍针对 `μH`，缩放常数经 `smul` 传递。
2. **参考测度必须是 Lebesgue。** Borell 密度的参考测度原为任意 Haar `m`。若 `m = c·volume`，密度变为 `ρ/c`、`P_ρ` 变为
   `P/c`，而 `∫‖∇u‖dν` 不变，故 `limsup ∫‖∇u_j‖dν ≤ P_ρ(U)` 在 `c > 1` 时为假。修正：`exists_smooth_recovery_sequence`、
   `lintegral_enorm_gradient_mollified_homothety_le`、`enorm_gradient_mollified_le` 的参考测度固定为内积空间的
   `volume`（`measureSpaceOfInnerProductSpace`），前提写成 `IsBorellDensity ν volume ρ`。`mollifiedIndicator φ m`、
   `exists_le`、`addHaar_frontier` 等对一般 Haar `m` 的陈述不变。

对齐表相应两行更新为：`P_ρ(U) = ∫_{∂U∩Ω} ρ dℋ^{n−1}` ↔ `relativePerimeter`（`surfaceMeasure`，标准归一化）——一致；
`dν = ρ dLeb_V` ↔ `IsBorellDensity ν volume ρ` ——一致。编译：仅 5 条 sorry（原 4 条 + 约定检查）。
