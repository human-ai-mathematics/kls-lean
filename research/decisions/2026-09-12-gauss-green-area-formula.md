# 2026-09-12 — Gauss–Green 推进：余维一面积公式已证，散度定理未闭合

Owner 要求推进 `KLS/WIP/AnalyticPrerequisites.lean` 的两条 Gauss–Green 目标并完成实际证明与验证，
本轮解除这两条的"保留 sorry"限制，其他开放目标保持原状；不提交、不推送。承接
[接口接入记录](2026-09-12-perimeter-interface-integration.md)、
[外法向证明记录](2026-09-12-outward-normal-interfaces-proofs.md)与
[外法向收尾](2026-09-12-outward-normal-interfaces-closeout.md)；上一轮未提交的模块拆分与三个接口
证明全部保留，未重置或重写。历史记录保持原意与原计数。

## 结论先说：两条目标都**没有**完成

| 目标 | 状态 | 传递公理 |
| --- | --- | --- |
| `SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`（C1，向量场形式） | **未完成**，仍是直接 `sorry` | 含 `sorryAx` |
| `SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal`（C2，标量测试形式） | 证明体已填，但**由 C1 归约得出** | 含 `sorryAx` |
| `SmoothDomain.gradient_mollifiedIndicator_eq` | 证明体已填 | 含 `sorryAx`（经 C2 经 C1） |

因此 owner 要求的"确认 Gauss–Green 的 hole 已从 `gradient_mollifiedIndicator_eq` 的依赖链消失"
**未达成**，不能按完成报告。C1 仍是唯一独立的 Gauss–Green 义务。

## 本轮实际证明的数学（无 `sorry`，只用标准公理）

### 1. 余维一面积公式（新模块 `Analysis/AreaFormula.lean`，约 950 行）

设 `H`、`V` 为有限维实内积空间，`ι : H →ₗᵢ[ℝ] V` 线性等距，`e : V` 单位向量且与 `ι` 的像正交，
`g : H → ℝ` 为 `C¹`，图映射 `Ψ y = ι y + g y • e`，Jacobian `J a = √(1 + ‖a‖²)`。则对任意可测 `s`：

* `Analysis.hausdorffMeasure_image_graphMap`：`μH[k] (Ψ '' s) = ∫⁻_s ofReal (J (∇g y)) ∂μH[k]`；
* `Analysis.hausdorffNormalized_image_graphMap`：归一化版本，右端对 `volume` 积分，
  即 `ℋ^k(图) = ∫_s √(1+‖∇g‖²)`，正是周长链 `surfaceMeasure` 所用的归一化。

`k = finrank ℝ H` 任意（含 0）；`s` 不必有界，图的总测度可以无穷；没有 Lipschitz 或有界梯度假设。

证明结构：

* **线性情形**（`hausdorffMeasure_image_graphLinear`）。把斜率 `a = r • u`（`u` 单位）的线性图映射
  分解为 `graphLinear ι e a = shearCLM ∘ dilate`：`dilate u c`（`c = √(1+r²)`）是 `H` 上沿 `u` 的
  伸缩，`shearCLM` 是 `H → V` 的线性**等距**。于是 Hausdorff 测度的等距不变性
  （`Isometry.hausdorffMeasure_image`）消掉 `shearCLM`，`Measure.addHaar_image_linearMap` 与
  `det (dilate u c) = c`（取以 `u` 为首向量的正交基后是对角阵）给出常数 `c = J a`。
  `μH[k]` 到 `volume` 的换算用上一轮的 `Analysis.hausdorffMeasure_finrank_eq_smul_volume`。
  **不需要**极分解、SVD 或一般线性面积公式。
* **`C¹` 情形**。三步：
  (a) 局部线性化：在 `∇g` 变化 ≤ ε 的球上，中值不等式给
      `ApproximatesLinearOn Ψ (graphLinear ι e (∇g y₀)) t ε`（球是凸的）；
      用 `SecondCountableTopology.countable_cover_nhds` 取可数球覆盖，再 `disjointed` 得可数不交可测分割。
  (b) 夹逼：`Ψ` 与 `graphLinear` 互为 `(1+ε)`-Lipschitz 重参数化（`Ψ` 与 `graphLinear` 都不收缩，
      `‖y-y'‖ ≤ ‖Ψ y - Ψ y'‖`），故两边的 `μH[k]` 相差因子 `(1+ε)^k`
      （`LipschitzOnWith.hausdorffMeasure_image_le`）。`Ψ` 单射且像可测：
      `Ψ '' E = {x | Ψ (P x) = x} ∩ P ⁻¹' E`，`P` 为 `ι` 的伴随，第一个集合闭，
      **不需要** Lusin–Souslin。
  (c) 求和后令 `ε ↓ 0`（`μ s < ∞` 的情形直接在 `ℝ≥0∞` 里取极限；一般 `s` 用球穷竭 + 单调收敛）。

Mathlib 的 `MeasureTheory/Function/Jacobian.lean` 只有等维换元，没有余维面积公式；
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` 虽对不同维数可用，但它给出的
`A n = f' y` 中的 `y` 只保证属于 `s`，不保证属于该分片，故本轮自建了球覆盖分割。

### 2. 散度与秩一迹（新模块 `Analysis/Divergence.lean`）

`divergence F x = tr (DF x)` 由 WIP 下移到 `Analysis/`（同一命名空间，声明名不变，所有消费者
自动继续可用）。新增 `Analysis.trace_smulRight`（`tr (w ↦ φ w • v) = φ v`，经
`dualTensorHom` / `contractLeft`）与 `Analysis.divergence_smul_const`
（`div (η • v) = ⟪∇η, v⟫`，`v` 常向量）。

### 3. C2 由 C1 归约（**不是**独立证明）

取 `F x = η x • v`：`div F = ⟪∇η, v⟫`，`⟪F x, ν x⟫ = ⟪v, η x • ν x⟫`，两端用 `integral_inner`
与内积交换（体积侧用 `∇η` 连续紧支撑，边界侧用已证的 `integrableOn_smul_outwardNormal`），
再用 `ext_inner_left` 去掉 `v`。数学范围未变：任意有限维实内积空间、当前 `SmoothDomain` 定义、
紧支撑 `C¹` 测试函数、既有 `surfaceMeasure` 与 `outwardNormal`，未增加有界性或更强光滑性假设。
这条归约方向是单向的（C1 ⇒ C2），没有把两条公式互相循环使用。

## C1 仍缺的具体数学引理

1. **边界的图表示**：`SmoothDomain` 的定义函数 `φ`（`∇φ(x₀) ≠ 0`）需给出邻域上 `C^∞` 的
   `g : e^⊥ → ℝ`，使边界局部等于 `g` 的图、区域局部等于图下方，且
   `outwardNormal = (ι(-∇g) + e)/√(1+‖∇g‖²)`。障碍：Mathlib 的
   `HasStrictFDerivAt.implicitFunctionOfComplemented` 只给出**在一点**的严格可微性，
   不给邻域上的 `C¹`；面积公式需要 `ContDiff ℝ 1 g`。可行路线是经
   `ContDiffAt.to_localInverse`（反函数定理保 `C^k`）对 `Φ x = (P x, φ x)` 取局部逆，
   本轮未实现。
2. **子图上的局部 Gauss–Green**：经 `V ≃ₗᵢ WithLp 2 (H × ℝ)`（`LinearIsometryEquiv.measurePreserving`
   与 `WithLp.volume_preserving_ofLp`）做 Fubini，法向分量用微积分基本定理，切向分量需要对
   变上限积分 `y ↦ ∫_{-∞}^{g y} F_i` 求导（Leibniz 规则）再整体积分为零。本轮未实现。
3. **光滑单位分解**：紧支撑上的有限光滑单位分解（可由
   `exists_contDiff_tsupport_subset` 手工拼装），用于把局部恒等式粘起来并抵消分解函数的导数项。
   本轮未实现。

评估过的替代路线及否决理由：Mathlib 的散度定理只覆盖盒子，不能直接用于任意光滑区域；
经剪切微分同胚把区域拉平需要 Piola 恒等式（余因子矩阵按行无散度），在 Lean 中不比原路线便宜；
用 Minkowski 含量或 coarea 绕开面积公式会引入同样未证的输入。

## 模块组织

新增两个无 `sorry` 的通用模块置于 `Analysis/` 下：`AreaFormula.lean` 与 `Divergence.lean`。
依赖方向保持无环：`KLS/Geometry/SurfaceMeasure` → `Analysis/LevelSet` → `Analysis/AreaFormula`；
`Analysis/Divergence` 独立于前三者；`KLS/WIP/AnalyticPrerequisites` 导入 `Analysis/Divergence`
与 `Analysis/LevelSet`，并继续为 `mollifiedIndicator` 导入 `KLS/WIP/RelativePerimeter`。
未完成的 Gauss–Green、coarea、Sard 全部留在 WIP。没有兼容别名、没有重复证明、没有转发声明。
正式聚合入口与 24 个证书都不导入这些模块。

## 计数

WIP 直接 hole 由 21 降至 20：`RelativePerimeter` 3（不变）、`AnalyticPrerequisites` 5 → 4、
`CheegerInfimum` 8（不变）、`Energy/WIP/Cheeger` 5（不变）。
`AnalyticPrerequisites` 迁出 `divergence` 后共 12 条义务，8 条已填证明体，其中 6 条无传递 `sorryAx`；
`ae_forall_fderiv_ne_zero`、`setIntegral_gradient_eq_integral_smul_outwardNormal` 与
`gradient_mollifiedIndicator_eq` 三条已填证明体仍传递依赖 `sorryAx`。
"已填证明体"与"传递无 sorryAx"必须分别表述。

## 验证

- **直接公理检查**：`Analysis.hausdorffMeasure_image_graphLinear`、
  `hausdorffMeasure_image_graphMap`、`hausdorffNormalized_image_graphMap`、
  `exists_approximating_partition`、`trace_smulRight`、`divergence_smul_const`
  的传递公理只有 `propext / Classical.choice / Quot.sound`。
  C1、C2 与 `gradient_mollifiedIndicator_eq` 含 `sorryAx`（如上表）。
- **独立客户端**：`build/audit/AreaFormulaAudit.lean`（忽略目录，`lake env lean` 直接 elaborate，
  不进 `lake build`、重放集合或认证闭包）。六条客户端定理都是推论而非复述：平坦超平面片的测度
  等于参数集测度；倾斜超平面片的测度恰为 `√(1+‖a‖²)` 倍；零维单点情形；参数集取 `univ`
  的无界情形；余维一时公式直接计算 `surfaceMeasure`（核对归一化与周长链一致）；秩一散度恒等式。
  六条的传递公理都只有标准三条。上一轮的 `PerimeterInterfaceAudit.lean` 仍然通过。
- **严格模式**：`Analysis/AreaFormula.lean`、`Analysis/Divergence.lean` 与两个审计客户端在
  `lake env lean -DwarningAsError=true` 下退出 0。
- **含 hole 的 WIP**：四个文件普通模式实际重新 elaborate，退出 0，诊断恰好是预期的
  3 / 4 / 8 / 5 条 `declaration uses sorry`，无其他警告或错误。**这不是严格模式通过。**
- 完成默认 `lake build`，并从仓库根运行 `python3 research/verify.py`；回执由
  `build/verification/latest.json` 指向，与最终源码快照匹配。

证据都信任固定版本的第三方编译依赖，不代表独立重建 Mathlib、远端 CI 或 Blueprint 排版通过。
审计脚本与日志留在忽略的 `build/`。本轮按 owner 要求不提交、不推送。
