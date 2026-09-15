# 二维定量覆盖与二阶平坦层零测

2026-09-14，承接[一致二阶余项](2026-09-14-uniform-quadratic-remainder.md)中精确提出的下一引理。
起始回执 `build/verification/latest.json`（`20260913T190354.174769Z`）为 passed，重新计算确认
全部 390 个文件与工作区逐字节一致，HEAD 仍为 `2965b32`。保留此前全部未提交及未跟踪成果，
不提交、不推送，历史决定不改写。

## 完成范围

新增 `formalization/FunctionalInequalities/Analysis/QuadraticCover.lean`，三条公开结果：

```lean
theorem volume_image_eq_zero_of_quadratic_oscillation
    {A : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℝ} (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ 2) :
    (volume : Measure ℝ) (f '' A) = 0

theorem volume_image_flat_eq_zero {u : (Fin 2 → ℝ) → ℝ} {K : Set (Fin 2 → ℝ)}
    (hu : ContDiff ℝ 2 u) (hK : IsCompact K) :
    (volume : Measure ℝ)
      (u '' {x ∈ K | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}) = 0
```

再由可数穷竭把紧集版本升到整个平面：

```lean
theorem volume_image_flat_univ_eq_zero {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}) = 0
```

完整命名为 `FunctionalInequalities.Analysis.volume_image_eq_zero_of_quadratic_oscillation`、
`FunctionalInequalities.Analysis.volume_image_flat_eq_zero` 与
`FunctionalInequalities.Analysis.volume_image_flat_univ_eq_zero`。
三者仅依赖 `propext / Classical.choice / Quot.sound`，没有直接洞、隐藏占位或新增公理。

* 覆盖引理的假设与上一轮提出的目标逐字一致：二维、`A` 有界、一致二次振幅控制。
  没有增加可测性、连续性、可微性或紧性假设，`f` 在 `A` 外完全任意。
  `A = ∅` 由 `R > 0` 的有界常数与空覆盖自动覆盖，不需要分支。
* 平坦层定理是**子集版本**：平坦条件逐点施加在 `{x ∈ K | Du x = 0 ∧ D²u x = 0}` 上，
  不假设整个 `K` 平坦，也不假设该子集可测。
* 全平面版本用 `⋃ n : ℕ, closedBall 0 n` 穷竭、`Set.image_iUnion` 与 `measure_iUnion_null`，
  紧性、有界性与可测性假设全部消失。这是后续拼装需要的形状，不引入新工具。
* 新模块只导入 Mathlib 的 `Measure.Lebesgue.Basic`、`Normed.Group.Bounded` 和本仓库的
  `Analysis/TaylorRemainder`。没有迁移任何已有声明，没有改动任何已有公开签名，
  没有引入 Sard、KLS 或 WIP 依赖，也没有新建覆盖或外测度框架。

## 实际证明

搜索 Mathlib 后确认：`Finset` 有限次可加性 `measure_biUnion_finset_le` 与
`Real.volume_Icc` 已经够用，不需要 `OuterMeasure` 的自定义构造或 Vitali 型引理；
可数覆盖 API 单独不足，因为格子数与 `ε` 的平衡必须是定量的。

固定 `ε > 0`，由假设取 `δ > 0`，令 `r = min δ 1`（同时保证 `r ≤ δ` 与 `r ≤ 1`）。

1. `Bornology.IsBounded.exists_pos_norm_le` 给 `R > 0` 使 `A ⊆ {x | ‖x‖ ≤ R}`。
   `Fin 2 → ℝ` 的 Pi 范数是分量上确界，所以 `norm_le_pi_norm` 直接给 `|x i| ≤ R`。
2. 格子编号 `q x = (⌊x 0 / r⌋, ⌊x 1 / r⌋) : ℤ × ℤ`。
   `Int.floor_le_floor`、`Int.floor_le_ceil` 与 `Int.floor_neg` 把 `|x i| ≤ R` 变成
   `q x ∈ S := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M`，其中 `M = ⌈R / r⌉`。
   这是**有限**指标集，`Int.card_Icc` 与 `Finset.card_product` 给 `#S = (2M+1)²`。
3. 用 `choose` 对每个格子取一个代表 `g c`：只要该格子里有 `A` 的点，就有 `g c ∈ A ∧ q (g c) = c`；
   否则 `g c` 是任意值。因此覆盖区间 `I c = Icc (f (g c) - ε r²) (f (g c) + ε r²)`
   总是一个真区间，不需要 `dite` 分支，测度恒为 `ENNReal.ofReal (2 ε r²)`。
4. 同格两点：`Int.abs_sub_lt_one_of_floor_eq_floor` 给 `|a/r - b/r| < 1`，
   除法整理后得 `|a - b| < r`；`pi_norm_lt_iff` 与 `Fin.forall_fin_two` 把两个分量
   合成 `‖y - g (q y)‖ < r ≤ δ`。于是假设适用，且 `‖y - g (q y)‖² ≤ r²`，
   得 `f y ∈ I (q y)`。这就是 `f '' A ⊆ ⋃ c ∈ S, I c`，**不需要**任何可测性。
5. `measure_mono`、`measure_biUnion_finset_le`、`Finset.sum_le_card_nsmul` 给
   `volume (f '' A) ≤ #S • ofReal (2 ε r²) = ofReal ((2M+1)² · 2 ε r²)`。
   `Int.ceil_lt_add_one` 给 `(2M+1) r ≤ 2R + 3r ≤ 2R + 3`，所以上界是
   `ofReal (2 (2R+3)² ε)`，**与 `r`、`δ` 无关**。
6. `ENNReal.le_of_forall_pos_le_add` 对每个 `η > 0` 取 `ε = η / (2 (2R+3)²)`，得零。

维数二用在第 2 与第 5 步的乘积：格子数是 `O(r⁻²)`，每个像区间长 `O(ε r²)`，
乘积才与 `r` 无关。三维同样论证给 `O(ε r⁻¹)`，发散，所以此引理不能照搬到高维。

平坦层定理只是把 `IsCompact.isBounded` 与
`Analysis.exists_uniform_quadratic_remainder` 接到这个接口上：
紧集的平坦子集有界，余项定理对该子集给出所需的一致二次振幅控制
（余项定理允许 `y` 在 `K` 外，这里只用到 `y ∈ A` 的更弱情形）。

## 验证与公理边界

* 新模块 `lake env lean -DwarningAsError=true` 严格通过（`build/audit/quadratic-cover-module-strict.log`），
  `lake build FunctionalInequalities.Analysis.QuadraticCover` 通过（2551 jobs）。
* `build/audit/QuadraticCoverAudit.lean` 严格通过：16 个客户端与 3 条主定理共 19 条公理报告，
  全部仅含标准三公理。覆盖空集；单点集配完全任意（可能处处不连续）的 `f`；
  任意有界集配常值 `f`，客户端内**没有**任何可测性实例或假设；
  紧集上常函数的平坦层；全平面平坦层（无紧性、有界性、可测性假设）；
  非常值三次函数 `x ↦ (x 0)³` 的平坦层与闭球实例。
  `cubic_ball_layer_proper` 同时给出闭球内的非平坦点 `![1,0]` 与平坦点 `0`，
  确认子集版本既非空也非全体，不能用“整个 `K` 平坦”替代。
* `QuadraticRemainderAudit`、`SardLowDimAudit`、`AreaFormulaAudit`、`SuperlevelSardScope`
  重新严格编译通过。`SuperlevelSardScope` 再次确认一般 `Analysis.sard`、
  `Analysis.ae_forall_fderiv_ne_zero`、`SmoothDomain.ae_exists_superlevel` 仍继承 `sorryAx`。
* 三个 WIP 文件逐个实际普通模式编译，诊断仍为 **3/3/5** 个直接洞警告，无其他诊断。
  **直接洞总数仍为 11**；证书仍为 **24**，perimeter infrastructure 仍为 **missing**。
* 默认 `lake build` 通过（3393 jobs），日志 `build/audit/quadratic-cover-lake-build.log`；
  根目录 `python3 research/verify.py` 的最终快照回执为 `build/verification/latest.json`。
  独立客户端与日志位于被忽略的 `build/` 目录，其证据哈希记录于
  `research/explorations/2026-09-14-quadratic-cover-audit.json`，不冒充正式证书。
* 本轮**没有**扩大任何证书或 `leanok` 范围。一般 Sard、加权 coarea、其可测性、
  反方向 Cheeger 比较与常数相等仍未证明。本地回执不等于远端 CI。

## 明确未完成

本轮只完成**二维二阶平坦层**。以下仍然全部未完成：

* **二维非平坦层**：`{x ∈ K | Du x = 0 ∧ D²u x ≠ 0}` 的像零测。
  `build/audit/PlanarNonflatNextStatement.lean` 只检查此命题类型，无证明声明、无占位公理。
  该层需要对某个一阶偏导数用隐函数定理得到 `C¹` 曲线，再降到一维 Sard；
  当前仓库没有这个局部图表与降维拼接。
* **一般 Sard**（`Analysis.sard`）：仍是 `WIP/AnalyticPrerequisites` 中的直接洞。
  即使两个二维层都完成，还需要 σ-紧穷竭、任意有限维、高阶平坦余项与高阶覆盖，
  以及高阶分层下降时的正则性损失处理。本轮结果**不是**一般 Sard，也不改变其状态。
* **加权 coarea** 及其水平集可测性：两个未触动的直接洞。
* **反方向 Cheeger 比较** `smoothConstant_le_minkowskiConstant` 与常数相等：仍未证明，
  仍传递依赖 `sorryAx`；只有 `h_M ≤ h_S` 一个方向是证明过的。

整条链**没有**闭合，也不得据本轮结果暗示闭合。
