# 平坦点的一致二阶余项

2026-09-14，承接[低维 Sard](2026-09-14-low-dimensional-sard.md)中精确提出的下一引理。
起始回执 `build/verification/20260913T184752.039532Z/report.json` 为 passed，重新计算确认
全部 387 个文件与 HEAD 完全匹配。HEAD 仍为 `2965b32`；保留此前全部未提交及未跟踪成果，
不提交、不推送，历史决定不改写。

## 完成范围

新增 `formalization/FunctionalInequalities/Analysis/TaylorRemainder.lean`，唯一公开结果为：

```lean
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_uniform_quadratic_remainder {u : V → ℝ} {K : Set V}
    (hu : ContDiff ℝ 2 u) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, fderiv ℝ u x = 0 → iteratedFDeriv ℝ 2 u x = 0 →
        ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ 2
```

完整命名为 `FunctionalInequalities.Analysis.exists_uniform_quadratic_remainder`。
仅依赖 `propext / Classical.choice / Quot.sound`。没有直接洞、隐藏占位或新增公理。

* 同一 δ 对 K 中全部满足两个零导数条件的 x 一致有效。
* 不要求 K 的每个点都平坦；y 可在 K 外，包含 y=x。
* 空 K、零维、常函数均覆盖，正则性恰为 C²，没有升到 C³ 或 C∞。
* 搜索已有 API 后发现有限维性实际上不需要，所以给出**任意实赋范空间**版本。
  不要求完备、内积、定义域测度或额外可测性。这覆盖原定有限维目标，没有缩小适用范围。
* 新模块仅导入 Mathlib 的 ContDiff.Comp、MeanValue、HeineCantor；无本地导入，
  不导入 Sard、KLS 或 WIP，也未迁移任何原有声明。
  它是一般分析估计，不把 Sard 专属名称放进定理或建立额外框架。

## 实际证明与可复用 API

上一轮提出积分型 Taylor 是可行路线；本轮搜索发现所需的非锐常数估计可更短地用两次
`Convex.norm_image_sub_le_of_norm_fderiv_le`，因此没有重复实现 Taylor 积分公式。

1. `hu.continuous_iteratedFDeriv` 给二阶导数连续。
   `IsCompact.uniformContinuousAt_of_continuousAt` 给紧集上的**外部近邻**一致控制；
   它比仅控制 K 内两点的 `UniformContinuousOn` 更强。
   通过 `Metric.mem_uniformity_dist` 得 δ，使 x∈K 且 ‖z-x‖<δ 时二阶导数之差小于 ε。
2. 固定平坦基点 x。由 D²u(x)=0，得到球 `ball x δ` 上 ‖D²u(z)‖≤ε。
   `norm_iteratedFDeriv_one` 与 `norm_iteratedFDeriv_fderiv` 直接把这个范数换成
   `‖fderiv ℝ (fderiv ℝ u) z‖`；没有引入 Hessian、内积或行列式框架。
3. C² 给 u 可微、Du 可微。在该凸球上第一次用均值不等式，并使用 Du(x)=0，
   得 ‖Du(z)‖≤ε‖z-x‖。
4. 对线段 [x,y]，`norm_sub_le_of_mem_segment` 给 ‖z-x‖≤‖y-x‖<δ。
   因而该线段上 ‖Du(z)‖≤ε‖y-x‖。第二次均值不等式得到
   |u(y)-u(x)|≤ε‖y-x‖·‖y-x‖。

这是一致 o(r²) 振幅估计，**没有**断言任何高维像集已经零测。

## 验证与公理边界

* 新模块使用 `lake env lean -DwarningAsError=true` 严格通过，独立模块构建通过。
* `build/audit/QuadraticRemainderAudit.lean` 严格通过：9 个客户端与主定理共 10 条公理报告，
  全部仅含标准三公理。覆盖无有限维/完备/内积/测度实例的一般空间、空 K、零维任意函数、
  常函数；三次函数在零点的一二阶导数为零；K={0,1} 含非平坦点，且另证 x=1 不平坦；
  K={0} 时实际取 y=δ/2≠0，在紧集外满足所需估计。
* `SardLowDimAudit`、`AreaFormulaAudit` 和 `SuperlevelSardScope` 重新严格编译通过。
  前两者无 sorryAx；最后一份分别确认一般 `Analysis.sard`、
  `Analysis.ae_forall_fderiv_ne_zero`、`SmoothDomain.ae_exists_superlevel` 仍继承 sorryAx。
* 三个 WIP 文件逐个实际普通模式编译，诊断仍为 3/3/5 个直接洞警告，无其他诊断。
  **直接洞总数仍为 11**；证书仍为 **24**，perimeter infrastructure 仍为 **missing**。
* 默认 `lake build` 已通过（3393 jobs），日志为 `build/audit/quadratic-lake-build.log`；根目录
  `python3 research/verify.py` 的最终快照回执为 `build/verification/latest.json`。
  独立客户端和日志在忽略的 build 目录，其证据哈希记录于
  `research/explorations/2026-09-14-quadratic-remainder-audit.json`，不冒充正式证书。
* 原一般 Sard 和全部 WIP 源码本轮未改。一般 Sard、加权 coarea、其可测性、
  反方向 Cheeger 比较及常数相等仍未证明。本地回执不等于远端 CI。

## 下一项独立缺口：二维定量覆盖导致像零测

建议下一步建立纯覆盖引理（尚未证明；命名以届时搜索为准）：
对 `A : Set (Fin 2 → ℝ)`、任意 `f : (Fin 2 → ℝ) → ℝ`，假设 A 有界，并且

```lean
∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ 2
```

则 `(volume : Measure ℝ) (f '' A) = 0`。
不要求 A 或其像可测，不要求 f 在 A 外连续或可微。这里**维数二不可省略**。
`build/audit/QuadraticCoverNextStatement.lean` 只检查此命题类型，没有证明声明或占位公理。

可将 A 放入一个方框，分成 O(r⁻²) 个小方格；每个与 A 相交的格子选一个 A 内代表，
用上述估计将其像覆盖在长度 O(εr²) 的区间内，再取 ε→0 控制外测度。
该定量有限覆盖、区间像覆盖和外测度估计仍需证明，单有可数覆盖 API 不足。
本轮结果可把紧集 K 中的二阶平坦点子集送入这个接口，不必先假设该子集可测。

即使完成这个覆盖引理，也只处理二维的二阶平坦层；非平坦层仍需有限阶隐函数图表、
局部降维和可数拼接。更高维还需高阶平坦余项与覆盖，并处理高阶分层下降时的正则性损失。
这不等于一般 Sard 已建立。
