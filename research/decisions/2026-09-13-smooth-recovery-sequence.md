# 相对周长的光滑恢复序列

日期：2026-09-13。承接 [外扩梯度积分记录](2026-09-13-dilated-gradient-integral.md)。
起始 HEAD 为 `2965b32`；上轮 passed 回执的 372 个文件与开始时的快照全部匹配。
保留此前未提交和未跟踪成果，本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

`KLS.RelativePerimeter.exists_smooth_recovery_sequence` 已证明，并迁入新的无洞模块
`formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean`。
声明文本与原目标一致：任意有限维实内积空间、对 **Lebesgue volume** 的 Borell 概率密度 `ρ`、
任意 `SmoothDomain U`，仅假设 `relativePerimeter ρ (interior ν.support) U ≠ ⊤`，给出
`u : ℕ → V → ℝ`，每项全局 `C^∞`、全局 Lipschitz、取值在 `[0,1]`，且

```
∫⁻ ‖u j - 1_U‖ₑ dν → 0,      limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ relativePerimeter ρ Ω U.
```

没有增加区域有界、边界有界、载体有界、总边界测度有限、非零维数或额外密度正则性的假设；
Lipschitz 常数不要求对 `j` 一致有界。有限相对周长的假设保留在声明中，实际证明没有用到它
（下界与极限论证对 `⊤` 同样成立），因此该绑定以 `_hU` 出现，数学范围不变。

本轮把直接洞从 **17** 降到 **16**：AnalyticPrerequisites **3**、CheegerInfimum **8**、
Energy/WIP/Cheeger **5**。`KLS/WIP/RelativePerimeter.lean` 已无剩余内容，整层删除。
证书仍为 **24**，相对周长链的 infrastructure 仍为 `missing`。
coarea、Sard、Cheeger 下确界与一般奇异律比较本轮未触及，也不是本构造的前提。

## 实际证明

1. **密度球与全局上界。** `LogConcave/DensityBounds.lean` 中原为 `private` 的
   `IsBorellDensity.exists_ball_le` 改为公开（唯一证明位置不变，没有重新证明），
   给出 `a`、`r₀>0`、`b₀>0` 与 `ball a r₀` 上的下界。取 `r = r₀/2`，
   `closedBall a r ⊆ ball a r₀` 给闭球下界；`ball a r₀ ⊆ {ρ>0}` 加 `interior_maximal`
   与已有 `interior_pos_subset` 给 `closedBall a r ⊆ interior ν.support`。
   `exists_le` 给 `M`，`b₀ ≤ ρ a ≤ M` 给 `M > 0`。
2. **绝对连续性。** 新增 `IsBorellDensity.absolutelyContinuous`（`ν ≪ m`，直接由
   `withDensity_absolutelyContinuous` 得到）。与已证的 `SmoothDomain.addHaar_frontier`
   合成，给出 `ν (frontier U.carrier) = 0` 和每个外扩区域的同一结论；
   没有假设 indicator 对全空间 volume 可积。
3. **固定伸缩下的磨光收敛。** `SmoothDomain.mollifiedIndicator_eq_indicator_of_const`：
   若 indicator 在 bump 外半径球上取常值，则磨光值精确等于 indicator。证明用
   `φ.support_normed_eq` 把球外核置零、`φ.normed_neg` 与 `integral_sub_right_eq_self`
   把核积分化为 `φ.integral_normed = 1`，只使用归一化，不需要 Lebesgue 微分定理。
   `SmoothDomain.exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt` 取显式 bump 族
   `rOut = R/(k+2)`、`rIn = rOut/2`，在 frontier 之外由区域开性或闭包补集开性取局部常值半径，
   用 `[0,1]` 控制和概率测度做支配收敛，得到 `L¹(ν)` 误差趋零，再按给定容差取出一项。
   结论同时给出 `rOut < R`，供对角选择使用。
4. **对角选择。** 取 `s j = 1 - 1/(j+2) ↑ 1`。对每个 `j` 用上一步在
   `R = r(1-s j)/s j`、容差 `((j:ℝ≥0∞)+1)⁻¹` 上选 bump `φ j`，于是同时满足
   `s j * (φ j).rOut / (1 - s j) < r` 与磨光误差趋零。
   `u j` 取外扩区域 `U.homothety a (s j)⁻¹` 的磨光 indicator。
   `L¹` 误差用 `enorm_add_le` 与可测函数的 `lintegral_add_left` 拆成磨光项与外扩项，
   外扩项经 `SmoothDomain.indicator_homothety` 与 `inv_inv` 化为已证的
   `RelativePerimeter.tendsto_indicator_homothety` 在 `s j → 1` 处的复合，
   再用 ENNReal 夹逼得到联合收敛；没有把两种收敛直接当作联合收敛。
5. **梯度预算。** 正则性直接取 `mollifiedIndicator_contDiff_lipschitz_mem_Icc`。
   每项的梯度积分由上轮 `lintegral_enorm_gradient_mollified_homothety_le` 界住，系数为
   `s j ^ (1 - finrank ℝ V) * (M/b₀)^((1-s j)/s j)`。底数 `s j → 1 > 0`、
   指数 `(1-s j)/s j → 0`、`M/b₀ > 0`，由 `Real.continuousAt_rpow_const` 与
   `Real.continuous_const_rpow` 得系数趋于 `1`；`ENNReal.Tendsto.mul` 的两个侧条件都由
   极限 `1 ≠ 0, 1 ≠ ⊤` 满足，所以 `ofReal (c j) * P → P` 对 `P = 0` 与 `P = ⊤` 同样成立。
   最后 `limsup_le_limsup` 加 `Tendsto.limsup_eq` 给 `limsup ≤ P`，没有除以相对周长。

## 分层、迁移与删除

* 新模块 `Geometry/PerimeterRecovery.lean` 只导入 `Geometry/RelativePerimeter`，
  本地传递导入闭包为 **30 个模块、零 WIP 导入**。
* `LogConcave/DensityBounds.lean` 只改可见性并新增绝对连续性，没有复制已有证明。
* `KLS/WIP/RelativePerimeter.lean` 因无剩余内容被**删除**；`KLS/WIP/CheegerInfimum.lean`
  改为直接导入 `Geometry/PerimeterRecovery`。没有兼容别名、转发声明或空壳模块。
* 名称、命名空间、`surfaceMeasure` 归一化与 `volume` 基准均未改变。

## 验证

* `exists_smooth_recovery_sequence`、两条磨光引理、`absolutelyContinuous` 与
  `exists_ball_le` 的传递公理均为 `propext / Classical.choice / Quot.sound`，无 `sorryAx`。
* 八个相关无洞模块（DensityBounds、SmoothDomain、SurfaceMeasure、SurfaceHomothety、
  Mollification、MollifiedBoundary、RelativePerimeter、PerimeterRecovery）以
  `lake env lean -DwarningAsError=true` 直接编译通过。
* 独立客户端 `build/audit/RecoveryAudit.lean` 同样严格编译，含 9 个客户端与 14 条公理报告：
  区域、边界与载体同时无界；逐项 Lipschitz 与 `[0,1]`；任意 `L¹` 容差可达；
  零相对周长给 `limsup = 0`；零维；全空间作为无界零周长区域；
  全空间磨光恒为 `1` 而空区域磨光恒为 `0`（核方向与归一化检查）；任意小 bump 半径。
  既有 `DilationAudit` 与 `GaussGreenAudit` 客户端重跑，仍只用标准三条公理。
* 三个 WIP 文件实际普通模式重编译，诊断为 **3/8/5** 个直接洞，仍不是严格模式通过。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 完成后，以
  `build/verification/latest.json` 为最终源码回执；基础设施证据哈希同步刷新，
  删除的 WIP 模块条目移除，新模块条目加入。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 下一项：h_M ≤ h_S 分支还缺什么

恢复序列的唯一消费者是 `KLS/WIP/CheegerInfimum.lean` 的
`minkowskiConstant_le_smoothConstant`。本轮之后该定理的依赖只剩两项，且都与
Sard、加权 coarea 无关：

1. `lintegral_minkowskiContent_superlevel_le`（Minkowski coarea 不等式，
   Ambrosio–Di Marino–Gigli 2017 引理 3.2）：对 `C¹` Lipschitz `u`，
   `∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`。这是独立的分析引理，不需要密度。
   **这是下一项最小目标。**
2. `minkowskiConstant_mul_lintegral_min_superlevel_le`：由第 1 条加上
   “单调函数的开、闭超水平集质量对几乎所有 `t` 相同” 得到。

有了这两条，`minkowskiConstant_le_smoothConstant` 就是纯组装：对每个中间质量的光滑域取本轮
恢复序列，逐项用第 2 条，再用已证明的 `tendsto_lintegral_min_superlevel` 把 `L¹` 收敛传到
超水平集平衡量，取 `limsup` 并对 `iInf` 收尾；`P_ρ(U) = ⊤` 的情形单独平凡。

另一方向 `smoothConstant_le_minkowskiConstant` 仍需 `WIP/AnalyticPrerequisites` 的 Sard 与
加权 coarea，以及 `lintegral_enorm_gradient_distanceCutoff_le`，本轮没有任何进展。
因此不能把恢复序列的完成表述为 coarea、Cheeger 桥接或整条相对周长链已完成。
