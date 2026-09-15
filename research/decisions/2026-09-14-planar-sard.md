# 二维非平坦层与平面 Sard

2026-09-14，承接[二维定量覆盖](2026-09-14-planar-quadratic-cover.md)中类型检查过的下一命题
（`build/audit/PlanarNonflatNextStatement.lean` 的非平坦层）。起始回执
`build/verification/latest.json`（`20260914T150543.429034Z`）为 passed，重新计算确认工作区逐字节一致。
HEAD 仍为 `2965b32`，保留此前全部未提交及未跟踪成果，不提交、不推送，历史决定不改写。

## 完成范围

`Analysis/QuadraticCover.lean` 增加一维覆盖引理；新增
`formalization/FunctionalInequalities/Analysis/PlanarSard.lean`，公开结果两条：

```lean
theorem volume_image_eq_zero_of_quadratic_bound {A : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hA : Bornology.IsBounded A)
    (hC : ∀ x ∈ A, ∀ y ∈ A, |f y - f x| ≤ C * |y - x| ^ 2) :
    (volume : Measure ℝ) (f '' A) = 0

theorem volume_image_nonflat_eq_zero {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x ≠ 0}) = 0

theorem sard_plane {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0
```

全名分别为 `FunctionalInequalities.Analysis.volume_image_eq_zero_of_quadratic_bound`、
`…volume_image_nonflat_eq_zero`、`…sard_plane`。三者仅依赖
`propext / Classical.choice / Quot.sound`，无直接洞、无占位、无新增公理。

`sard_plane` 是 **C² 函数在平面上的 Sard 定理**：临界值集零测，临界集不假设可测、不假设有界、
不假设紧。它**不是** `Analysis.sard`——后者是任意有限维的一般命题，仍是 WIP 中的直接洞。

## 实际证明：不需要隐函数定理

一维覆盖引理是二维版本的简化：常数固定，不需要 ε-δ 精化，因为格子数 `O(r⁻¹)` 已经压过
像区间长度 `O(r²)`，总量 `O(r) → 0`。

非平坦层的关键是把它**塌成一维**，路线如下（`x₀` 处只要求 `D²u x₀ ≠ 0`，不要求临界）：

1. `T := fderiv ℝ (fderiv ℝ u) x₀ ≠ 0`（由 `iteratedFDeriv ℝ 2 u x₀ ≠ 0` 经范数相等得到），
   取 `v₀, w` 使 `(T v₀) w ≠ 0`，令 `α := T.flip w`，则 `α ≠ 0`。
2. **纯线性代数**：非零泛函 `α` 在某个基向量 `Pi.single i 1` 上非零；令 `j := 1 - i`。
   若 `|α v| ≤ (|α eᵢ|/4)‖v‖`，则 `‖v‖ ≤ L |v j|`。用 `‖v‖ ≤ |v i| + |v j|` 与
   `α v = v i · α eᵢ + v j · α e_j` 直接解出，常数显式。
3. **带线性主部的中值不等式** `Convex.norm_image_sub_le_of_norm_fderiv_le'` 用在
   `fderiv ℝ u` 上：球内 `‖D²u z − T‖ ≤ η` 时，对任意 `x, y`，
   `‖Du y − Du x − T(y−x)‖ ≤ η‖y−x‖`。两点都临界时即 `‖T(y−x)‖ ≤ η‖y−x‖`，
   配对 `w` 得 `|α(y−x)| ≤ η‖w‖‖y−x‖ ≤ ε‖y−x‖`。于是第 2 步给
   `‖y − x‖ ≤ L |y j − x j|`：**临界集在球内是关于第 `j` 个坐标的 Lipschitz 图**。
   这一步取代了隐函数定理；仓库已有的 `Analysis/ImplicitGraph.lean` 要求 `C^∞` 与内积结构，
   对只有 `C¹` 的 `Du` 用不上，所以没有复用它，也没有新建隐函数框架。
4. 临界点处的二次估计（两次凸集中值不等式，与平坦余项同构但保留真常数 `M = ‖T‖+1`）给
   `|u y − u x| ≤ M‖y−x‖²`。与第 3 步合成：`|u y − u x| ≤ M L² |y j − x j|²`。
5. Lipschitz 图同时给**单射性**：同一 `j` 坐标的两点距离为零，故相等。于是
   `t ↦ u(代表点)` 在 `A := (· j) '' (临界集 ∩ 球)` 上良定义并满足一维二次界，
   一维覆盖引理直接给出该球内像零测。
6. `TopologicalSpace.isOpen_iUnion_countable`（二次可数即 Lindelöf）把逐点的球取可数子覆盖，
   `measure_biUnion_null_iff` 合成全平面结论。不需要紧性，所以公开陈述里没有 `K`。

`sard_plane` 只是按 `D²u x = 0` 与 `≠ 0` 拆分临界集，两半分别用上一轮的
`volume_image_flat_univ_eq_zero` 与本轮的 `volume_image_nonflat_eq_zero`。

## 验证与公理边界

* 两个模块 `lake env lean -DwarningAsError=true` 严格通过，`lake build` 目标模块通过。
* `build/audit/PlanarSardAudit.lean` 严格通过：13 个客户端与 3 条主定理共 16 条公理报告，
  全部仅含标准三公理。其中
  `recorded_nonflat_obligation` 逐字给出上一轮记录的紧集版非平坦义务；
  `nonflat_on_subset` 说明紧性其实不需要，任意（可能不可测的）子集都成立；
  `constant_critical_univ` + `constant_sard` 给出临界集是**整个平面**（源侧测度无穷）而像仍零测的
  非平凡实例；`square_critical` 证明 `x ↦ (x 0)²` 的临界集恰是直线 `{x 0 = 0}`，
  `square_critical_line` 给出该直线上任意点，说明非平坦分支不是空转。
* `QuadraticCoverAudit`、`QuadraticRemainderAudit`、`SardLowDimAudit`、`AreaFormulaAudit`、
  `SuperlevelSardScope` 全部重新严格通过。`SuperlevelSardScope` 再次确认一般
  `Analysis.sard`、`Analysis.ae_forall_fderiv_ne_zero`、`SmoothDomain.ae_exists_superlevel`
  **仍继承 `sorryAx`**。
* 三个 WIP 文件逐个实际编译，诊断仍为 **3/3/5** 个直接洞，无其他诊断。直接洞总数仍为 **11**；
  证书仍为 **24**；perimeter infrastructure 仍为 **missing**。
* 默认 `lake build` 通过（3393 jobs）。根目录 `python3 research/verify.py` 的最终快照回执为
  `build/verification/latest.json`。证据哈希记录于
  `research/explorations/2026-09-14-planar-sard-audit.json`，不冒充正式证书。
* 本轮**没有**扩大任何证书或 `leanok` 范围。

## 明确未完成

`sard_plane` 只覆盖**二维、C²、实值**。以下全部仍未完成：

* **一般 Sard**（`Analysis.sard`，任意有限维 `C^n`）：仍是 `WIP/AnalyticPrerequisites` 的直接洞，
  两个消费者仍继承 `sorryAx`。平面情形**不能**推出它。
* 下一项独立缺口已类型检查于 `build/audit/HigherSardNextStatement.lean`（无证明、无占位公理）：
  (1) `n` 维覆盖引理——有界 `A ⊆ ℝⁿ`、一致 `o(‖y−x‖ⁿ)` 振幅控制推出像零测；
  (2) 紧集中全平坦点（1 到 `n` 阶导数全为零）处的 `n` 阶一致余项。
  两者合成才给出 `n` 维的顶层；中间各层还需要有限阶隐函数图表与逐阶降维，
  且降维时正则性会损失，这正是 Whitney–Morse–Sard 的难点。
* **加权 coarea** 及其水平集可测性：两个未触动的直接洞。
* **反方向 Cheeger 比较** `smoothConstant_le_minkowskiConstant` 与常数相等：仍未证明，
  仍传递依赖 `sorryAx`；只有 `h_M ≤ h_S` 一个方向是证明过的。

整条链**没有**闭合。
