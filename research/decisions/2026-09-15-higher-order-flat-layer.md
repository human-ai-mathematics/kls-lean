# n 阶一致余项与 n 维顶层

2026-09-15，承接[平面 Sard](2026-09-14-planar-sard.md)中类型检查过的两条下一义务
（`build/audit/HigherSardNextStatement.lean`）。起始回执
`build/verification/latest.json`（`20260914T154144.742286Z`）为 passed，重新计算确认工作区逐字节一致。
HEAD 仍为 `2965b32`，保留此前全部未提交及未跟踪成果，不提交、不推送，历史决定不改写。

## 完成范围

上一轮记录的两条义务**逐字证明**，并合成 `n` 维顶层。

`Analysis/TaylorRemainder.lean` 推广为任意阶：

```lean
theorem exists_uniform_pow_remainder {u : V → ℝ} {K : Set V} {n : ℕ}
    (hu : ContDiff ℝ (n : ℕ) u) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, (∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0) →
        ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ n
```

`Analysis/QuadraticCover.lean` 推广为任意维：

```lean
theorem volume_image_eq_zero_of_oscillation_pow {n : ℕ} {A : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ n) :
    (volume : Measure ℝ) (f '' A) = 0

theorem volume_image_flat_pow_eq_zero {n : ℕ} {u : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hu : ContDiff ℝ (n : ℕ) u) (hK : IsCompact K) :
    (volume : Measure ℝ)
      (u '' {x ∈ K | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}) = 0

theorem volume_image_flat_pow_univ_eq_zero {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ (n : ℕ) u) :
    (volume : Measure ℝ)
      (u '' {x | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}) = 0
```

四条新结果仅依赖 `propext / Classical.choice / Quot.sound`，无直接洞、无占位、无新增公理。

**没有新增重复证明**：原 `exists_uniform_quadratic_remainder` 与
`volume_image_eq_zero_of_quadratic_oscillation` 改为一般结果的推论，
两者**语句逐字未变**（已逐行 diff 核对），全部既有客户端不改动即通过。
余项的阶从 2 升到任意 `n` 后，二阶证明整段被归纳取代，模块净行数没有膨胀。

## 实际证明

**余项（对阶数归纳）**。零阶就是紧集上的一致连续（`IsCompact.uniformContinuousAt_of_continuousAt`
的外部近邻版本）。归纳步：`fderiv ℝ f` 是 `C^m`，它在 `x` 处 `1..m` 阶导数为零等价于
`f` 在 `x` 处 `2..m+1` 阶导数为零（`norm_iteratedFDeriv_fderiv`），又 `f` 的一阶导数为零给
`fderiv ℝ f x = 0`，于是球内 `‖fderiv ℝ f z‖ ≤ ε‖z-x‖^m`，一次凸集中值不等式把幂次抬到 `m+1`。
常数**不退化**，始终是同一个 `ε`。

归纳要在**向量值**函数上进行（`fderiv f` 取值在 `V →L[ℝ] F`），所以内部辅助定理把
`W` 与 `F` 放在同一 universe；公开的实值定理对 `n = m+1` 先降一阶到
`fderiv ℝ u : V → (V →L[ℝ] ℝ)` 再套辅助定理，因此**没有** universe 限制，
对任意实赋范空间成立，不要求有限维、完备、内积或测度。

**覆盖（对维数一般化）**。格子编号从 `ℤ × ℤ` 换成 `Fin n → ℤ`，指标集用
`Fintype.piFinset`，基数 `(2M+1)^n` 由 `Fintype.card_piFinset` 与 `Finset.prod_const` 给出。
总量 `(2M+1)^n · 2εr^n = 2ε((2M+1)r)^n ≤ 2ε(2R+3)^n`，与 `r` 无关。
维数与幂次必须相等：格子数 `O(r⁻ⁿ)` 与像区间长 `O(εrⁿ)` 恰好抵消。
二维版本现在就是 `n = 2` 的实例；`Fin.forall_fin_two` 被 `congrFun` 取代，证明反而更短。
`n = 0`（空积基数为 1）与 `n = 1` 都被同一证明覆盖，无分支。

## 验证与公理边界

* 三个模块 `lake env lean -DwarningAsError=true` 严格通过。
* `build/audit/HigherSardAudit.lean` 严格通过：13 个客户端与 5 条主定理共 17 条公理报告，
  全部仅含标准三公理。其中 `recorded_pow_cover` 与 `recorded_pow_remainder`
  逐字给出上一轮登记的两条义务；`pow_remainder_general` 在无维数的任意赋范空间上使用余项；
  `dim_zero`（平坦条件空洞、集合为全空间）、`dim_one`、`dim_three` 覆盖小维与非小维；
  `flat_two_unchanged` 确认平面二阶层接口未变；
  `constant_fully_flat` + `constant_sard_pow` 给出任意维常函数处处全平坦、
  平坦集是**整个 `ℝⁿ`** 而像仍零测的非平凡实例。
* `QuadraticRemainderAudit`、`QuadraticCoverAudit`、`PlanarSardAudit`、`SardLowDimAudit`、
  `AreaFormulaAudit`、`SuperlevelSardScope` 全部重新严格通过，**未作任何改动**。
  `SuperlevelSardScope` 再次确认一般 `Analysis.sard`、`Analysis.ae_forall_fderiv_ne_zero`、
  `SmoothDomain.ae_exists_superlevel` **仍继承 `sorryAx`**。
* 三个 WIP 文件逐个实际编译，诊断仍为 **3/3/5** 个直接洞，无其他诊断。直接洞总数仍为 **11**；
  证书仍为 **24**；perimeter infrastructure 仍为 **missing**。
* 默认 `lake build` 通过（3393 jobs）。根目录 `python3 research/verify.py` 的最终快照回执为
  `build/verification/latest.json`。证据哈希记录于
  `research/explorations/2026-09-15-higher-order-flat-layer.json`，不冒充正式证书。
* 本轮**没有**扩大任何证书或 `leanok` 范围。

## 明确未完成

本轮只完成 `n` 维的**顶层**（全平坦层）。以下全部仍未完成：

* **中间各层**：`1 ≤ j < n` 时
  `{x ∈ K | 1..j 阶导数全为零 ∧ (j+1) 阶导数 ≠ 0}` 的像零测。
  已类型检查于 `build/audit/IntermediateLayerNextStatement.lean`（无证明、无占位公理）。
  平面情形 `n = 2, j = 1` 已证，用的是"临界集局部是某坐标上的 Lipschitz 图、
  再塌到一维"的初等路线。一般 `n` 时同样的估计只给出 `(n-1)` 维的 Lipschitz 图，
  还需要在该图上做 `(n-1)` 维的 Sard，并处理限制后正则性下降——
  这正是 Whitney–Morse–Sard 的难点，本轮**没有**触及。
* **`n` 维 Sard**（把所有层叠起来）：同文件第二条，未证明。
* **一般 Sard**（`Analysis.sard`，任意有限维赋范空间）：仍是
  `WIP/AnalyticPrerequisites` 的直接洞，两个消费者仍继承 `sorryAx`。
  即使 `n` 维 `Fin n → ℝ` 版本完成，也还需要有限维空间与 `Fin n → ℝ` 的线性同构传递。
* **加权 coarea** 及其水平集可测性：两个未触动的直接洞。
* **反方向 Cheeger 比较** `smoothConstant_le_minkowskiConstant` 与常数相等：仍未证明，
  仍传递依赖 `sorryAx`；只有 `h_M ≤ h_S` 一个方向是证明过的。

整条链**没有**闭合。
