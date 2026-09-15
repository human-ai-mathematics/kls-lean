# C^∞ Sard 的三块拼图：分层、平坦方向、局部图

2026-09-15，承接同日的[路线探查](2026-09-15-smooth-sard-route.md)，按 L2 → L4 → L5 的顺序推进。
起始回执 `build/verification/latest.json`（`20260914T162757.518089Z`）为 passed，
重新计算确认工作区逐字节一致。HEAD 仍为 `2965b32`，保留全部未提交成果，不提交、不推送。

## 完成范围

新增 `formalization/FunctionalInequalities/Analysis/SmoothSard.lean`，三条公开结果：

```lean
theorem critical_subset_layers {n : ℕ} (u : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) :
    {x ∈ O | fderiv ℝ u x = 0} ⊆
      {x ∈ O | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0} ∪
        ⋃ j ∈ Finset.Ico 1 n,
          {x ∈ O | (∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0) ∧
            iteratedFDeriv ℝ (j + 1) u x ≠ 0}

theorem exists_flat_direction {n j : ℕ} {u : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hu : ContDiff ℝ ∞ u) (h : iteratedFDeriv ℝ (j + 1) u x₀ ≠ 0) :
    ∃ m : Fin j → (Fin n → ℝ),
      ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ j u x m) ∧
        fderiv ℝ (fun x => iteratedFDeriv ℝ j u x m) x₀ ≠ 0

theorem exists_local_graph {n : ℕ} {w : (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ}
    (hw : ContDiff ℝ ∞ w) (hx₀ : w x₀ = 0) (hd : fderiv ℝ w x₀ ≠ 0) :
    ∃ (p : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (γ : (Fin n → ℝ) → (Fin (n + 1) → ℝ))
      (O : Set (Fin n → ℝ)),
      Continuous p ∧ IsOpen O ∧ p x₀ ∈ O ∧ ContDiffOn ℝ ∞ γ O ∧ γ (p x₀) = x₀ ∧
        ∀ᶠ x in 𝓝 x₀, w x = 0 → p x ∈ O ∧ γ (p x) = x
```

三者仅依赖 `propext / Classical.choice / Quot.sound`，无直接洞、无占位、无新增公理。
分别对应路线记录中的 **L2、L4、L5**。

## 路线修正：L5 必须给邻域版，不能只给一点

探查记录里 L1 写成开集上的 `ContDiffOn ℝ ∞`。本轮实现时发现一个**必须修正**的细节：
`ContDiffAt ℝ ∞ f x` **不能**升级为某邻域上的 `ContDiffOn ℝ ∞ f`——
Mathlib 的 `ContDiffAt.contDiffOn` 带副条件 `m = ∞ → n = ω`，
而这不是接口瑕疵：无穷阶在一点的 `ContDiffAt` 本来就是"对每个 `k` 各有一个邻域"，
交集未必是邻域。

因此隐函数/反函数定理只给出基点处的 `ContDiffAt` 是**不够**的，L5 的结论被加强为
参数开集上的 `ContDiffOn ℝ ∞ γ O`。做法是把区域缩到
`W := {x | fderiv ℝ w x (Pi.single i 1) ≠ 0}`（由 `fderiv` 连续而开），
在 `W` 的每一点重新构造可逆微分，然后对 `H.target ∩ H.symm ⁻¹' W` 的**每一点**
调用 `OpenPartialHomeomorph.contDiffAt_symm`，逐点的 `ContDiffAt` 合成 `ContDiffOn`。
这一步不改变探查记录给出的归纳陈述，只是把 L5 的义务提高了一档；行数估计从 ~100 变成实际 ~90。

## 实际证明

**L2**：`fderiv u x = 0` 等价于 `iteratedFDeriv 1 u x = 0`（范数相等）。若 `1..n` 阶不全为零，
取 `Nat.findGreatest` 抓住"`1..j` 阶全为零"的最大 `j`，由 `1` 阶为零得 `j ≥ 1`，
由假设不成立得 `j < n`，由最大性得 `(j+1)` 阶非零。纯组合，无分析。

**L4**：`iteratedFDeriv (j+1) u x₀ ≠ 0` 给出方向组 `v : Fin (j+1) → ℝⁿ` 使取值非零；
`iteratedFDeriv_succ_apply_left` 把它写成
`(fderiv (iteratedFDeriv j u) x₀ (v 0)) (Fin.tail v)`。取 `m := Fin.tail v`，
`HasFDerivAt.continuousMultilinear_apply_const` 给出
`fderiv (fun x => iteratedFDeriv j u x m) x₀ = (fderiv (iteratedFDeriv j u) x₀).flipMultilinear m`，
作用在 `v 0` 上非零。光滑性由 `ContDiff.iteratedFDeriv_right` 与
`ContinuousMultilinearMap.apply` 的复合给出。

**L5**：取 `i` 使 `fderiv w x₀ (Pi.single i 1) ≠ 0`（非零泛函必在某个基向量上非零）。
令 `Φ x := Function.update x i (w x)`——把第 `i` 个坐标换成 `w`。
`Φ` 全局 `C^∞`；其微分 `ContinuousLinearMap.pi (fun k => if k = i then fderiv w x else proj k)`
在 `W` 上单射，有限维即双射，`LinearEquiv.ofInjectiveEndo` 加
`LinearEquiv.toContinuousLinearEquiv` 得到所需的 `≃L`。
反函数定理 `ContDiffAt.toOpenPartialHomeomorph` 给出局部同胚 `H`。
参数映射取 `p := Fin.removeNth i`（**固定的连续线性投影**，所以零点靠近时参数也靠近），
嵌入取 `Fin.insertNth i 0`；`w x = 0` 时恰有 `Φ x = insertNth i 0 (removeNth i x)`，
于是 `γ := H.symm ∘ insertNth i 0` 在零点上满足 `γ (p x) = x`（`H.left_inv`）。
**没有**引入流形或图表框架，也**没有**新建隐函数框架；仓库自己的
`Analysis/ImplicitGraph.lean` 仍然用不上（它要 `C^∞` 数据加内积图拆分）。

## 验证与公理边界

* 新模块 `lake env lean -DwarningAsError=true` 严格通过，`lake build` 目标模块通过（2560 jobs）。
* `build/audit/SmoothSardIngredientsAudit.lean` 严格通过：7 个客户端与 3 条主定理共 10 条公理报告，
  全部仅含标准三公理。其中 `layers_dim_zero` 覆盖零维（中间层集合为空）；
  `flat_direction_one` 是平面用过的 `j = 1` 情形；
  `local_graph_plane` 给出具体正则零集 `{x | x 0 = 0}` 的实例；
  `top_layer` 确认要与之组合的已证顶层接口未变。
* `QuadraticRemainderAudit`、`QuadraticCoverAudit`、`PlanarSardAudit`、`HigherSardAudit`、
  `SardLowDimAudit`、`AreaFormulaAudit`、`SuperlevelSardScope` 全部重新严格通过，**未作改动**。
  `SuperlevelSardScope` 再次确认一般 `Analysis.sard`、`Analysis.ae_forall_fderiv_ne_zero`、
  `SmoothDomain.ae_exists_superlevel` **仍继承 `sorryAx`**。
* 三个 WIP 文件逐个实际编译，诊断仍为 **3/3/5** 个直接洞。直接洞总数仍为 **11**；
  证书仍为 **24**；perimeter infrastructure 仍为 **missing**。
* 默认 `lake build` 通过（3393 jobs）。根目录 `python3 research/verify.py` 的最终快照回执为
  `build/verification/latest.json`。证据哈希记录于
  `research/explorations/2026-09-15-smooth-sard-ingredients.json`。
* 本轮**没有**扩大任何证书或 `leanok` 范围，**没有**解除任何 `sorryAx`。

## 明确未完成

本轮只交付**三块拼图**，`C^∞` Sard 本身仍未证明。按路线记录的编号：

* **L3**：开集版的顶层零测——把已证的 `Analysis.volume_image_flat_pow_eq_zero`
  从全局 `ContDiff` 放宽到开集上的 `ContDiffOn`。需要把
  `Analysis.exists_uniform_pow_remainder` 的定义域假设一并放宽（阶数有限，
  `ContDiffOn.of_le` 够用，不触发上面那个 `∞` 的副条件）。**未开始**。
* **L1**：维数归纳的装配（分层 + 逐层用 L4/L5 降维 + Lindelöf 拼接）。**未开始**。
* **L6 / L7**：有限维空间与坐标的传递，以及 `C^∞` 版
  `ae_forall_fderiv_ne_zero`。**未开始**。
* **尖锐 `C^n` `Analysis.sard`**：语句与直接洞身份不变，两个消费者仍继承 `sorryAx`。
  路线记录中定位的 `n = 4, j = 2` 障碍**本轮没有触及**。
* 加权 coarea、其水平集可测性与反方向 Cheeger 比较完全未触及。

整条链**没有**闭合。
