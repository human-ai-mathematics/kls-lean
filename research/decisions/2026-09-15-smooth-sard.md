# C^∞ Sard 定理证明完成

2026-09-15，承接同日的[路线探查](2026-09-15-smooth-sard-route.md)与
[三块拼图](2026-09-15-smooth-sard-ingredients.md)，补齐剩余的 L1、L3′、L6、L7。
起始回执 `build/verification/latest.json`（`20260914T165021.064313Z`）为 passed，
重新计算确认工作区逐字节一致。HEAD 仍为 `2965b32`，不提交、不推送。

## 完成范围

`Analysis/SmoothSard.lean` 现在证明了 **C^∞ 实值函数的 Sard 定理**：

```lean
theorem sard_smooth_pi : ∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0

theorem sard_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0

theorem ae_forall_fderiv_ne_zero_of_contDiff_top {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x, u x = t → fderiv ℝ u x ≠ 0
```

任意有限维实赋范空间，任意维数，临界集**不假设可测**。三者与本轮新增的
`exists_contDiff_eventuallyEq` 一样，仅依赖 `propext / Classical.choice / Quot.sound`，
无直接洞、无占位、无新增公理。

## 路线的第二处修正：用延拓替代开集版顶层

探查记录的 L3 是"把顶层零测放宽到开集上的 `ContDiffOn`"。本轮改用一条更便宜的替代：

```lean
theorem exists_contDiff_eventuallyEq (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hz : z ∈ O) :
    ∃ g, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 z] f
```

（bump 乘上去，支撑落在开集内，光滑性是局部性质：在 `O` 上等于 `χ • f`，
在 `tsupport χ` 外等于 `0`，两个开集覆盖全空间。）

有了它，归纳步里把局部的 `γ` 换成与之局部相同的**全局** `C^∞` 映射 `γ'`，
于是归纳假设可以保持**全局**形式，顶层直接用上一轮已证的
`Analysis.volume_image_flat_pow_univ_eq_zero`，**完全不需要**开集版的余项或顶层。
L3 因此没有做，也不再需要。

## 实际证明

对维数归纳。维数 `0`：平坦条件空洞，临界集含于顶层，直接由已证顶层结论收掉。

维数 `m+1`：用 `critical_subset_layers` 把临界集拆成顶层与 `j ∈ Finset.Ico 1 (m+1)` 的中间层。
顶层用 `volume_image_flat_pow_univ_eq_zero`（`ContDiff.of_le` 把 `∞` 降到 `m+1`）。
每个中间层 `j`，对其中每个点 `x₀`：

1. `exists_flat_direction` 由 `iteratedFDeriv (j+1) u x₀ ≠ 0` 造出标量 `C^∞` 函数
   `w x := iteratedFDeriv j u x m`，它在整层上为零且 `fderiv w x₀ ≠ 0`。
2. `exists_local_graph` 给出连续参数映射 `p`、参数开集 `O` 与在 `O` 上 `C^∞` 的 `γ`，
   使 `x₀` 附近的零点满足 `γ (p x) = x`。
3. `exists_contDiff_eventuallyEq` 把 `γ` 换成全局 `C^∞` 的 `γ'`，在 `p x₀` 附近相同。
4. `u ∘ γ'` 全局 `C^∞`，落在 `Fin m → ℝ` 上，可用**归纳假设**。
   层上的点是 `u` 的临界点，链式法则给出 `p x` 是 `u ∘ γ'` 的临界点，
   且 `u x = (u ∘ γ') (p x)`。于是该点邻域内该层的像落进一个零测集。
5. `TopologicalSpace.isOpen_iUnion_countable`（Lindelöf）取可数子覆盖，
   `measure_biUnion_null_iff` 合成整层。

一般有限维版本由 `ContinuousLinearEquiv.ofFinrankEq` 与链式法则从坐标版传递；
a.e. 版本照抄 WIP 中 `ae_forall_fderiv_ne_zero` 的 `ae_iff` 论证。

## 它堵上了哪个洞——以及没有堵上哪个

`build/audit/SmoothSardAudit.lean` 中的 `superlevel_without_sard` **逐字重证**了
`SmoothDomain.ae_exists_superlevel` 的语句（`filter_upwards` 新的 a.e. 定理，
再接已证无洞的 `SmoothDomain.ofSuperlevel` 与 `frontier_superlevel_subset`），
其公理报告**不含 `sorryAx`**；同一份日志里 `SmoothDomain.ae_exists_superlevel` 本身
仍然带 `sorryAx`。两条报告并排阅读即是证据：这个消费者的缺口在数学上已经堵上。

**但本轮没有改动任何 WIP 文件**，所以：

* `SmoothDomain.ae_exists_superlevel` 仍然继承 `sorryAx`；
* 直接洞仍为 **11**（3/3/5），证书仍为 **24**，
  perimeter infrastructure 仍为 **missing**；
* 尖锐的 `Analysis.sard`（`C^(finrank)`）语句与直接洞身份**完全不变**，
  `Analysis.ae_forall_fderiv_ne_zero` 仍继承 `sorryAx`。
  路线记录中定位的 `n = 4, j = 2` 障碍**未触及**——本轮证的是光滑范畴，不是尖锐版本。

把 WIP 改接到新定理（从而真正减少 `sorryAx` 与洞数）是**下一轮的独立决定**，
涉及 `ae_exists_superlevel` 是否随之迁出 WIP，本轮不擅自做。

## 验证

* 新模块 `lake env lean -DwarningAsError=true` 严格通过；`lake build` 目标模块通过（2706 jobs）。
* `build/audit/SmoothSardAudit.lean` 严格通过：12 条标准公理报告 + 1 条**故意保留**的
  `sorryAx` 报告（WIP 的 `ae_exists_superlevel`，用作对照）。覆盖零维、三维、
  任意有限维无可测性实例的接口、常函数（临界集为全空间、源侧测度无穷而像零测）。
* `SmoothSardIngredientsAudit`、`QuadraticRemainderAudit`、`QuadraticCoverAudit`、
  `PlanarSardAudit`、`HigherSardAudit`、`SardLowDimAudit`、`AreaFormulaAudit`、
  `SuperlevelSardScope` 全部重新严格通过，**未作改动**。
* 三个 WIP 文件逐个实际编译，诊断仍为 **3/3/5** 个直接洞。
* 默认 `lake build` 通过（3393 jobs）。根目录 `python3 research/verify.py` 的最终快照回执为
  `build/verification/latest.json`。证据哈希记录于
  `research/explorations/2026-09-15-smooth-sard.json`。
* 本轮**没有**扩大任何证书或 `leanok` 范围。

## 仍未完成

* **WIP 改接**：让 `ae_exists_superlevel` 真正不带 `sorryAx`（下一轮决定）。
* **尖锐 `C^n` Sard**：`Analysis.sard` 仍是直接洞。
* **加权 coarea** `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  及其水平集可测性：两个未触动的直接洞，这才是反方向 Cheeger 比较的主要阻塞。
* **反方向比较** `smoothConstant_le_minkowskiConstant` 与常数相等：仍未证明。

整条链**没有**闭合。
