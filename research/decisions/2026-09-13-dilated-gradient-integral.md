# 外扩磨光的加权梯度积分界

日期：2026-09-13。承接 [逐点梯度界记录](2026-09-13-mollified-gradient-bound.md)。
起始 HEAD 为 `2965b32`；上轮 passed 回执的 368 个文件与当前快照全部匹配。
保留此前未提交和未跟踪成果，本轮不提交、不推送；历史决定记录不改写。

## 完成的目标及范围

`KLS.RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le` 已证明并从 WIP
迁入 `formalization/FunctionalInequalities/KLS/Geometry/RelativePerimeter.lean`。
声明文本与原目标一致，包括 `hr`、内部闭球、正密度下界、全局密度上界、`0<s<1`、
bump 半径条件和 **Lebesgue volume** 基准；命名空间和声明名保留，没有兼容别名。

对 `H(y)=a+(y-a)/s`、`η=φ.normed volume`、`n=finrank ℝ V`、`Ω=interior ν.support`，

```
∫ ‖∇(η⋆1_{H(U)})‖ dν ≤ s^(1-n) (M/b₀)^((1-s)/s) relativePerimeter ρ Ω U.
```

不要求区域或载体有界，不要求总边界测度有限，也**不要求相对周长有限**；右侧允许为无穷。
零维保留。没有 coarea、Sard、Cheeger 下确界或一般奇异律比较作为前提。
本轮仅把直接洞从 18 降至 **17**：RelativePerimeter **1**、AnalyticPrerequisites **3**、
CheegerInfimum **8**、Energy/WIP/Cheeger **5**。证书仍为 **24**，相对周长链的
infrastructure 仍为 `missing`；`exists_smooth_recovery_sequence` 是本模块唯一剩余洞。

## 实际证明

1. **归一化边界测度换元。** 新模块 `Geometry/SurfaceHomothety.lean` 从 Mathlib
   `map_homothety_hausdorffMeasure` 得到 `map_inv_homothety_surfaceMeasure`：
   `map H⁻¹ σ = |c|^(n-1) • σ`，这里 `H` 是比例 c 的 homothety，指数先用自然数 `n-1`。
   归一化常数通过交换标量作用保留，未把 `surfaceMeasure` 替换成未归一化 Hausdorff。
   `setLIntegral_image_homothety_surfaceMeasure` 利用逆同胚、`setLIntegral_map` 和函数可测性
   得到**任意可测集合、任意可测 ENNReal 权重**上的换元；没有积分有限性的假设。
   `SmoothDomain.setLIntegral_frontier_homothety` 将其应用于 frontier。
   这解决了原有 `hausdorff_frontier_homothety` 只比较总质量、不能换元带权积分的缺口。
2. **Ω 外的零贡献。** `IsBorellDensity.interior_pos_subset` 证明
   `interior {ρ>0} ⊆ interior ν.support`。不必使用连续性：任何落在 positivity set 内部的
   小开邻域 O 都有正 Haar 测度；`withDensity_apply` 和 `setLIntegral_pos_iff` 给 `ν(O)>0`，
   因而所有这些点在支撑内，开性再给支撑内部。与已证的 `interior_support_subset` 组合使用。
   当 `η(x-H(y))≠0`，令 `z=x-H(y)`、`b=a-s/(1-s)•z`。半径条件使 b 落在内部闭球，
   且 `y=s•x+(1-s)•b`。若 `ρ(x)>0`，`convex_pos.combo_self_interior_mem_interior`
   使 y 位于 positivity set 内部，再由新包含得到 `y∈Ω`。
   因此 y 不在 Ω 时核与密度的乘积确实为零；没有直接丢掉 `∂U\Ω`。
3. **核平均权重。** `RelativePerimeter.lintegral_normed_mul_density_le` 使用上一步、
   现有 `IsBorellDensity.le_rpow_mul_of_combination`、核非负性、平移不变性和归一化
   `φ.integral_normed`，给
   `A(H(y)) ≤ ofReal((M/b₀)^((1-s)/s)) * 1_Ω(y) ofReal(ρ(y))`，
   其中 `A(q)=∫⁻x ofReal(η(x-q)) ofReal(ρ(x)) dx`。
   核积分的实数／ENNReal 转换使用了实际的 `φ.integrable_normed` 和非负性。
4. **Tonelli 拼合。** 对外扩区域 W，令 `σ=(surfaceMeasure V).restrict (frontier W.carrier)`。
   由已证的边界局部有限性建立实例，第二可数性给 σ-有限性。连续核的联合可测性给
   Tonelli 的前提；密度换写只用于核的积分，不需要为梯度另设可积性假设。
   逐点梯度界积分后交换 ν 与 σ，再用 `hρ.withDensity_eq` 将内积分换成 A。
   A 的可测性由乘积被积函数的可测性和 `Measurable.lintegral_prod_left` 得到。
   应用边界换元和核平均估计后，indicator 把边界积分严格限制到 `frontier U ∩ Ω`。
5. **指数与零维。** `n>0` 时用 `Nat.cast_sub` 对齐指数，将 `|s⁻¹|^(n-1)` 化为 `s^(1-n)`。
   `n=0` 时从有限维零维得到 `Subsingleton V`，外扩区域 frontier 为空，已积分的逐点界
   直接给左侧为零。没有对 `n=0` 使用错误的实数指数替换。
   `hr` 与闭球中心的密度下界给 `M>0`，用于合并 ENNReal 系数时的非负证据。

## 分层、迁移与消费者

* `Geometry/SmoothDomain.lean` 公开已有的唯一 `homothetyHomeomorph` 及两个 coercion 定理，
  增加 `frontier_homothety`，已有总边界缩放引理改用它；不复制同胚定义。
* `Geometry/SurfaceHomothety.lean` 是新的无洞带权换元层，只依赖光滑区域基础。
* `LogConcave/DensityBounds.lean` 迁入原 WIP 内的 `exists_le`、
  `le_rpow_mul_of_combination` 及其原有私有辅助证明，并新增上述 positivity 内部包含。
  它只导入 `BorellRepresentation`，不导入区域、周长或 WIP。
* `Geometry/RelativePerimeter.lean` 迁入 `relativePerimeter`、空边界零周长接口、
  `tendsto_indicator_homothety`，并放置核平均界与本轮目标；导入 DensityBounds、
  SurfaceHomothety、MollifiedBoundary。其传递本地导入闭包为 **29 个模块、零 WIP 导入**。
* `WIP/RelativePerimeter.lean` 直接导入新模块，仅保留原恢复序列目标。
  `WIP/CheegerInfimum` 仍需要恢复序列，因此继续导入这个 WIP 应用层是有意的。
  原名称各有一个声明位置，没有转发声明或兼容别名。

## 验证

* 新目标、加权换元、密度包含与已迁移关键定理的传递公理均为
  `propext / Classical.choice / Quot.sound`，无 `sorryAx`。
* 十个相关无洞模块以 `lake env lean -DwarningAsError=true` 直接编译。
  独立 `build/audit/DilationAudit.lean` 包含 7 个客户端和 17 条公理报告：Ω 外核平均恰为零；
  零周长给零梯度积分；有限相对周长给有限梯度积分而不要求有限总边界；三维比例 2 的
  任意带权表面积积分系数为 4；一维负比例 -2 的边界权重系数为 1；零维空间；
  一维 s=1/2 的完整梯度积分系数精确为 `M/b₀`。
  既有 GaussGreen 客户端的 22 条报告也重跑，保留符号、半空间、区间端点等检查。
* 四个 WIP 文件实际普通模式重编译，预期诊断是 **1/3/8/5** 个直接洞，仍不是严格模式通过。
* 默认 `lake build` 与根目录 `python3 research/verify.py` 完成后，以
  `build/verification/latest.json` 为最终源码回执；基础设施证据哈希同步刷新。
  具体严格检查日志在 `build/audit/dilation-*`。

验证是固定第三方编译依赖下的本地编译、公理审计和本地内核重放，不代表远端 CI。

## 下一项：恢复序列还需实现的工作

唯一剩余目标为 `RelativePerimeter.exists_smooth_recovery_sequence`，原来有限相对周长的
假设保持。现在其梯度预算已经具备，后续是选择参数与收敛证明：

1. 从一般 IsBorellDensity 取得 Ω 内一点和内部闭球，用
   `exists_bounds_of_isCompact` 取得 `b₀>0`，用已迁移的 `exists_le` 取得 M。
   `DensityBounds` 已有私有 `nonempty_interior_pos`，结合本轮 `interior_pos_subset` 可得
   Ω 非空；下一消费者若需要此接口，应公开／迁移唯一现有证明，不重复证明。
2. 固定 `0<s<1`，证明 bump 半径趋零时外扩 indicator 的磨光在 `L¹(ν)` 收敛。
   对光滑区域，这可以直接用 frontier 外 indicator 的局部常值性和
   `ContDiffBump.normed_convolution_eq_right` 得到最终相等；不必重做 Lebesgue 微分定理。
   卷积次序用已公开的 `mollifiedIndicator_eq` 与交换律对齐。
   用 `addHaar_frontier`、`withDensity_eq` 导出的绝对连续性得到 ν-a.e. 边界外，再以
   `[0,1]` 和概率测度做控制收敛。不要假设 indicator 对全空间 volume 可积。
3. 取 `s_j↑1`，复用 `tendsto_indicator_homothety`；按 j 选 ε_j，同时满足
   `s_j ε_j/(1-s_j)<r` 与磨光误差趋零，用 L¹ 三角不等式合并外扩与磨光两种误差。
4. 用已证的光滑／Lipschitz／`[0,1]` 接口给每项正则性。证明预算系数趋于 1，
   结合本轮单步界及有限相对周长的假设给 ENNReal limsup 界，包含周长为零的情形。

这些步骤仍不需要 coarea 或 Sard。恢复序列尚未证明，因此不能登记整条相对周长链已完成。
