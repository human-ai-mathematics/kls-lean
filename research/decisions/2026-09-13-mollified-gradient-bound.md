# 磨光 indicator 的逐点梯度范数界与无洞模块分层

日期：2026-09-13。承接 [全局 Gauss–Green 记录](2026-09-13-global-gauss-green.md)。
本轮开始时 HEAD 为 `2965b32`，已有多轮未提交修改及未跟踪模块；起始
`build/verification/latest.json` 为 `passed`，覆盖的 364 个文件全部与当前内容匹配。
本轮保留这些成果，不提交、不推送。此前决定记录保持原文。

## 完成范围

`KLS.SmoothDomain.enorm_gradient_mollified_le` 已证明，原声明从
`KLS/WIP/RelativePerimeter.lean` 迁入 `KLS/Geometry/MollifiedBoundary.lean`：

```lean
theorem enorm_gradient_mollified_le (U : SmoothDomain V)
    (φ : ContDiffBump (0 : V)) (x : V) :
    ‖gradient (U.mollifiedIndicator φ volume) x‖ₑ ≤
      ∫⁻ y in frontier U.carrier, ENNReal.ofReal (φ.normed volume (x - y))
        ∂(surfaceMeasure V)
```

数学范围与归一化不变：有限维实内积空间，任何光滑区域、任何归一化光滑 bump、每个点。
不要求区域有界、边界总测度有限、非零维，也不要求右侧先验有限。
新增后果模块不显式携带 `SecondCountableTopology V`，由有限维性自动推导；
迁移后的梯度公式保持原来的实例范围，逐点范数界也无需重复携带这个可推导参数。
没有新增公理、兼容别名或重复证明。正式证书仍为 **24**，没有新增 Blueprint 认证锚点。
`lem:relative-perimeter-smoothing` infrastructure 仍为 `missing`。

证明先将反射平移核 `y ↦ φ.normed volume (x-y)` 的连续性和紧支撑传给
`integrableOn_smul_outwardNormal`，获得真正的 Bochner 可积性。然后使用已证明的
`gradient_mollifiedIndicator_eq`（负的外法向积分），消去范数中的负号，依次应用：

1. `norm_integral_le_integral_norm` 与 `ENNReal.ofReal_le_ofReal`；
2. `ofReal_integral_norm_eq_lintegral_enorm`，其可积性前提由上述证据满足；
3. 在可测 frontier 上逐点使用 `norm_smul`、`norm_outwardNormal` 与
   `ContDiffBump.nonneg_normed`，把法向加权向量的范数化为核本身。

因此没有借不可积 Bochner 积分的全定义零值跳过可积性，也没有用有限总边界测度。
空边界和零维情况走同一个证明；外法向单位长度只在 frontier 上调用。

## 模块迁移与消费者

实际旧依赖是 `GaussGreen → LocalGaussGreen → BoundaryChart → WIP/RelativePerimeter`，
不能从最后一层反向导入 GaussGreen。本轮按消费者拆为：

```text
SurfaceMeasure + Analysis/LevelSet
  → Geometry/SmoothDomain
      → Geometry/BoundaryChart → LocalGaussGreen → GaussGreen
      → Geometry/Mollification
  GaussGreen + Mollification → Geometry/MollifiedBoundary
      → WIP/RelativePerimeter → WIP/CheegerInfimum
Analysis/LevelSet + SurfaceMeasure + Mathlib calculus → WIP/AnalyticPrerequisites
```

* `Geometry/SmoothDomain.lean`：迁入归一化约定检查、`SmoothDomain` 结构、局部定义函数与
  frontier 接口、empty/univ、homothety、边界局部有限性、Haar 零测度与已有 Hausdorff 缩放。
* `Geometry/Mollification.lean`：迁入 `mollifiedIndicator`、卷积表示、indicator 局部可积性、
  光滑性／全局 Lipschitz／`[0,1]` 值域。两个已有私有辅助定理
  `locallyIntegrable_indicator`、`mollifiedIndicator_eq` 改为公开，名称与证明保留。
* `Geometry/GaussGreen.lean`：标量形式
  `setIntegral_gradient_eq_integral_smul_outwardNormal` 从 AnalyticPrerequisites 原样迁入。
* `Geometry/MollifiedBoundary.lean`：迁入 `gradient_mollifiedIndicator_eq`，并证明本轮目标。
  原 AnalyticPrerequisites 内两个复制的私有辅助证明删除，消费者改用上述唯一的公开接口。
* `BoundaryChart` 直接导入 `SmoothDomain`；`RelativePerimeter` 导入 `MollifiedBoundary`；
  `AnalyticPrerequisites` 不再间接引入周长应用，保留 4 条公开定理，其中 coarea 两条和 Sard
  三个直接洞，只有 Sard 的 a.e. 后果填了证明且仍传递依赖 `sorryAx`。
* 独立 GaussGreen 客户端也改为导入 `MollifiedBoundary`；没有留下转发声明。

新后果模块的传递本地导入闭包是 **15 个模块，零 WIP 导入**；基础模块既没有直接 hole，
也不把 coarea/Sard 的环境引进来。全部仍在现有认证闭包之外，没有注册整条周长链。
WIP 直接洞：RelativePerimeter **2**、AnalyticPrerequisites **3**、CheegerInfimum **8**、
Energy/WIP/Cheeger **5**，合计 **18**。

## 下一项：外扩后的梯度积分估计

目标仍是原声明 `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`，
没有证明、没有改题。记 `n = finrank ℝ V`，`H(y)=a+(y-a)/s`，`η=φ.normed volume`，
`C=(M/b₀)^((1-s)/s)`，`Ω=interior ν.support`。精确路线为

```text
∫ ‖∇(η⋆1_{H(U)})(x)‖ dν(x)
 ≤ ∫∂H(U) ∫ η(x-q) ρ(x) dx dσ(q)
 = s^(1-n) ∫∂U ∫ η(x-H(y)) ρ(x) dx dσ(y)
 ≤ s^(1-n) C ∫∂U∩Ω ρ(y) dσ(y).
```

已有输入：本轮逐点界；`hρ.withDensity_eq`、`hρ.measurable`、`hρ.nonneg`；
边界 surfaceMeasure 的局部有限性；`IsBorellDensity.le_rpow_mul_of_combination`；
bump 核的非负、紧支撑和积分为 1；光滑区域 homothety 定义。
下面是仍需实际实现的接口，不是把现有定理名连起来就算完成：

1. **带权边界换元。** 当前 `hausdorff_frontier_homothety` 只比较整条 frontier 的
   **未归一化总测度**。它不足以换元带权积分，尤其两边总测度都可能为无穷。
   需由 Mathlib `hausdorffMeasure_homothety_image` 对任意可测边界片推出归一化测度的
   pushforward／restrict 等式，再推出 `setLIntegral` 换元；归一化因子两侧相同。
   `n≥1` 时将自然数 `n-1` 和实数指数 `n-1` 对齐，缩放因子是 `s^(1-n)`；
   `n=0` 时先用 frontier 为空，不能把实指数 `-1` 的旧引理直接当自然数指数 0 使用。
   私有 `homothetyHomeomorph` 现仅在基础模块内使用；若新消费者需要，迁移／公开唯一接口，
   不复制它。
2. **Tonelli 与密度换写。** 将 `ν` 写成 `volume.withDensity (ofReal ∘ ρ)`，证明联合核
   `(x,q) ↦ ofReal(η(x-q)) * ofReal(ρ x)` 可测，调用非负积分交换。
   surfaceMeasure 限制在 frontier 上局部有限，有限维空间第二可数，故该限制测度 σ-有限；
   与 volume 组合足以应用 Tonelli。无需全局边界有限，也无需先证加权双积分有限。
3. **核支撑内的凸组合与 Ω 外零贡献。** 当 `η(x-H(y))≠0`，令
   `z=x-H(y)`、`b=a-s/(1-s) • z`。核支撑给 `‖z‖<φ.rOut`，半径条件给
   `b∈closedBall a r⊆Ω`，且 `y=s•x+(1-s)•b`。已有密度比较给 `ρ x≤Cρ y`。
   还必须单独证明：若同时 `ρ x>0`，则 `y∈Ω`，从而 `y∉Ω` 时核乘权重为零。
   这不能仅由数值比较推出，也不能简单删除 `∂U\Ω`。
   一个不缩小原 IsBorellDensity 范围的路线是：`convex_pos` 与
   `interior_support_subset` 使该组合点位于 positivity set 的内部；
   `continuousOn_interior_pos` 加 Haar 对开集的正质量，证明 positivity set 内部包含于
   `ν.support` 内部。这个反向内部包含需要补接口；不能只引用 intrinsic log-concave law
   专用的 `convex_support` 而悄悄加强本目标的假设。
4. **核平均与系数整理。** 对固定 y 积分数值比较，用平移不变性与 `φ.integral_normed`
   得平均权重 ≤ `Cρ(y)`，Ω 外为零；再按 frontier∩Ω 积分并合并 ENNReal 的系数。
   `M≥b₀>0` 由中心点的 hball/hM 给出，所有 rpow/ofReal 交换保留非负和非零证据。

这四步均不需要 coarea、Sard、Cheeger 下确界或奇异律比较。

## 距离恢复序列还差什么

即使上面的单步积分界闭合，`exists_smooth_recovery_sequence` 仍需：

* 在一般 IsBorellDensity 的范围内选 `a∈Ω` 及内部闭球。现有
  `interior_support_subset` 的证明中已构造 positivity set 内部非空，但尚不是此选择的
  完整公开接口；结合上面的反向内部包含即可得到 Ω 非空。用
  `exists_bounds_of_isCompact` 取 `b₀>0`，`IsBorellDensity.exists_le` 取全局 M。
* 固定 s，构造外半径趋零的 bump 并证明磨光逼近 `1_{H(U)}` 的 `L¹(ν)` 收敛。
  可用 Mathlib `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`
  （需固定内外半径比、正确的卷积次序），或利用边界外 indicator 局部常值及
  `ContDiffBump.normed_convolution_eq_right`。本轮公开的 indicator 局部可积性可复用。
  `addHaar_frontier` 加 `withDensity_eq` 导出的绝对连续性传递边界零测度，
  再以 `[0,1]` 与概率测度做控制收敛；不能假设整个 indicator 对无限 volume 可积。
* 取 `s_j↑1`，用已有 `tendsto_indicator_homothety` 控制外扩误差；按 j 选择足够小的
  ε_j，同时满足半径条件及磨光 L¹ 误差趋零，以三角不等式合并两项。
* `mollifiedIndicator_contDiff_lipschitz_mem_Icc` 给每项所需正则性与值域；证明
  `s_j^(1-n) (M/b₀)^((1-s_j)/s_j)→1`，结合有限 `relativePerimeter` 的原假设和
  单步界得到 ENNReal limsup 界。包括周长为零的情形，不可除以周长。

因此下一轮可集中证明单步外扩积分界；恢复序列是其后独立的收敛与对角化工作。
coarea/Sard 是后续 Cheeger 应用的开放输入，不是这两项的必要前提。

## 验证记录与边界

* 七个几何模块 `SurfaceMeasure / SmoothDomain / Mollification / BoundaryChart /
  LocalGaussGreen / GaussGreen / MollifiedBoundary` 各自实际执行
  `lake env lean -DwarningAsError=true`，退出码全部为 0，无诊断。
* 忽略目录 `build/audit/GaussGreenAudit.lean` 的严格客户端退出 0，共 22 条公理报告，
  全部仅有 `propext / Classical.choice / Quot.sound`。覆盖迁移的关键基础、磨光正则性、
  两个 Gauss–Green 后果、新目标，以及原来 11 个客户端（内部／外部支撑、无支撑限制的
  半空间、方向符号、一维区间端点、空边界、零维）。本轮加了无界半空间上的范数界
  和核在边界上为零时梯度为零的客户端。
* 四个 WIP 文件以普通模式实际重新 elaborate，全部退出 0，诊断严格为预期的
  2 / 3 / 8 / 5 条 `declaration uses sorry`，没有其他诊断。这不是 WIP 严格模式通过。
* 默认 `lake build` 已通过（3393 jobs）。库构建日志：`build/audit/mollified-library-build.log`；根目录统一验证命令：
  `python3 research/verify.py`。最终快照绑定回执以 `build/verification/latest.json` 为准。
  task infrastructure 的证据哈希按本轮源码刷新，状态保持 missing。

这些是本地 Lean 编译、公理检查和统一回执；第三方依赖使用固定版本的编译产物，
不声称重建 Mathlib、远端 CI 或新的整链证书。
