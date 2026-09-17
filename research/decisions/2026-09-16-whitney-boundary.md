# 开始 L6：紧集 jet 的边界拼接

2026-09-16。A 先完成：`20260915T170113.583163Z`，10 gates、190 个本地模块重放，
475 条目，快照 `051483acb993b037ccccd2682cb0c735a9d373ce20cc399defc54a384b10fa09`。
B 开始时 HEAD 与 origin/main 都是 `dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`。
不提交、不推送，原始 FirstOrderJet 两文件、其他既有 Lean 文件和历史决定均不改。

## 已完成的是边界分析步骤

新文件 `formalization/FunctionalInequalities/Analysis/WhitneyExtension.lean`，命名空间
`FunctionalInequalities.Analysis.WhitneyJet`。只经 FirstOrderJet 依赖 Mathlib，不依赖 KLS/WIP。

* `affine f F a y = f a + F a (y-a)`，是给定 jet 的仿射多项式。
* `norm_affine_sub_le`：两个仿射多项式的差由 jet 余项与导数差控制。
* `dist_nearest_le`：若 a 是 y 在 S 上的最近点，x∈S，则 dist(a,x) ≤ 2 dist(y,x)。
* `hasFDerivWithinAt`：余项条件给出集合内的导数；**不**识别稀疏集上的 fderivWithin，
  也**不**声称原函数在环境空间可微。
* `hasFDerivAt_of_nearby_affine`：候选函数在 S 上等于 f，补集上相对最近点仿射 jet
  有 o(dist(y,S)) 误差，则它在 S 的每一点的环境导数正好是 F。
* `continuousAt_of_nearby_field`：导数字段在 S 上等于 F，且补集上与最近点的 F
  之差一致为 o(1)，则字段在 S 的每一点连续。
* `contDiff_of_nearby_jet`：结合补集上的可微性和导数连续性，得全局 C¹ 与精确导数。
* `exists_contDiff_of_compl_approx`：只输入补集上 C¹ 的 w；令 v 在 S 上取 f、在 Sᶜ
  上取 w，导数字段同样分段拼接。上述两种估计确保 v 全局 C¹，且精确实现 f、F。
  **w 在 S 上可以不连续、值可以错误**，所以没有假设已存在全局延拓。

这些局部分析定理仅需要实范数空间和 S 紧；**不需要有限维、非空、有内点、正维**。
紧性用于最近点存在与闭性；边界处只需 F 在 S 上连续。原始 L6 的
`ContinuousOn f S` 无须参与这个步骤（余项已给出集合内可微性），原始目标未改写。
证明在 x∈S 时选最近点 a，并用 dist(a,x) ≤ 2 dist(y,x)。值误差拆成三项：
候选值误差、f 在 x,a 间的余项、F a-F x 作用于 y-a；取各自 ε/4 得总误差 ε dist(y,x)。
导数连续性用三角不等式和 ε/3。最后调用 `contDiff_one_iff_hasFDerivAt`。

## 尚未完成的精确命题

下面只是客户端里的 **命题类型检查**。它不是新公理，不是声明占位，也不是已经证明的引理。
原始 L6 的全部假设保持不变；证明它即可调用 `exists_contDiff_of_compl_approx` 得原始 L6。

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ w : V → ℝ, ContDiffOn ℝ 1 w Sᶜ ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
          ‖w y - WhitneyJet.affine f F a y‖ ≤ ε * infDist y S ∧
            ‖fderiv ℝ w y - F a‖ ≤ ε)
```

## 下一步构造及验收点

在 Sᶜ 上构造 Whitney 球/立方体覆盖，尺度 rᵢ 与到 S 的距离可比；选择最近点 pᵢ∈S，
并构造光滑单位分解 φᵢ。必须证明局部有限性、定量重叠界和导数界 O(1/rᵢ)，
不能只调用没有这些量化估计的一般单位分解接口。
令 `w(y) = ∑ᵢ φᵢ(y) * affine f F pᵢ y`。对 y 的最近点 a，
`∑φᵢ=1` 给值误差；导数比较中用 `∑Dφᵢ=0` 消去共同的 affine f F a y 项。
剩下的两类导数误差是 `∑φᵢ(F pᵢ-F a)` 与
`∑Dφᵢ * (affine f F pᵢ y - affine f F a y)`。
刚证明的 affine 比较、jet 余项和导数连续性分别控制它们，必须得出上述**两项**估计。
空集单独取常数候选；不得增加 S 有内点、凸、有限或 V 正维的假设。

## 检查与状态

`research/audits/WhitneyExtensionAudit.lean` 严格编译并审计 7 条库引理及 6 条客户端定理，
13 条公理报告仅含 propext、Classical.choice、Quot.sound。客户端包含：空集、单点任意
环境导数、零维，以及在 S 上取错值的补集候选。额外反例证明：常数函数在单点内可以
以 id 为 within-derivative，但其环境 fderiv 仍为 0；不能由稀疏集合上值相等推导导数相等。
没有新占位洞、没有新公理，没有扩大证书/Blueprint leanok 范围。

A 已重跑的 20 个客户端和 3 个 WIP 源码均原字节保留；B 的新模块与客户端另行严格编译。
最终默认构建、完整 verification 与 191 个模块的重放以最终回执为准，精确路径和快照核对
存于 `build/audit/whitney-boundary/final-snapshot.json`，逐项证据存于
`research/explorations/2026-09-16-whitney-boundary.json`。

**L6 未完成，L6a/L7/L12/Lipschitz coarea 未完成。** 直接洞仍 9（2/2/5），证书 24，
perimeter infrastructure missing；尖锐有限正则性 Sard、Cheeger 两项比较、维数无关 KLS 均开放。
进度图以 ◐ 表示部分边界工作，不能把它看成完整 L6 或完整 Whitney–Lusin 路线完成。
