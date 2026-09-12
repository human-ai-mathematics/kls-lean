# `prop:weighted-spectator-obstruction` 与 `lem:relative-perimeter-smoothing` 的基础设施核对：均为 `missing`

日期：2026-09-11（Asia/Shanghai）。基线：本地 `main` 提交 `5e5c704`，工作树含 2026-09-10 的四个节点与同日的
`lem:conditional-fiber-form`（见[闭条件纤维形式记录](2026-09-11-conditional-fiber-form.md)）。Lean/Mathlib 为
v4.33.0，Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户给出的顺序是先核对
`lem:conditional-fiber-form`，再核对 `prop:weighted-spectator-obstruction`（预期只需乘积指数律与柱集计算）与
`lem:relative-perimeter-smoothing`（预期 `missing`）。两项核对只读 Blueprint、库内模块与 Mathlib 源码，不改数学状态；
结论写入 tasks.json（`unchecked → missing`，附来源哈希与具体 gaps），不进 ledger、不设证书、不改 Blueprint 与路线配置。

## `prop:weighted-spectator-obstruction`（Blueprint 第 50 章，历史已驳斥的加权包）

Blueprint 陈述：对任意 `C, T₀, γ > 0`、`η ∈ (0, 1/2)`、`δ > 0`，中心化单侧指数律的各向同性乘积中存在平衡柱集，
初始超额 ≤ δ，但在某个 `0 < T ≤ T₀` 违反加权超额估计
`E∫₀^{T∧τ_η} e_t (1 + ‖A_t‖_op)^{5/2} dt ≤ C₂(T e₀ + T^{1+γ})`；从而 `ass:weighted-package` 在其全局量词下为假。

**结论：`missing`。** 与用户预期的差异在于：命题否定的对象是随机局部化过程沿时间的量，不只是初始数据。

- 待否定的 `ass:weighted-package` 本身没有 Lean 陈述：Eldan 随机局部化过程 `μ_t`（Brown 运动驱动的倾斜测度）、
  平衡有限周长割及其沿过程的超额 `e_t`、加权协方差 `A_t` 与其算子范数、停时 `τ_η`、以及"配对的吸收型加权
  Stein-迹估计"都没有定义；后者在本仓库连显示都没有（只在上游 `modules/kls/20-eldan-statements.tex`）。
- 钉住的 Mathlib 只有以有限维分布刻画的 Brown 运动（`IsBrownianReal`，`Probability/BrownianMotion/Basic.lean`）与
  停时、击中时（`Probability/Process/{Stopping,HittingTime}.lean`）；没有随机积分、Itô 公式或 SDE 解的存在唯一性，
  因此过程量目前无法定义。
- 上游证明档 `solutions/prop-weighted-spectator-obstruction.tex`（kls-exploration）不在本仓库；违反发生在正时间
  `0 < T ≤ T₀`，所以指数乘积与柱集的计算必须沿过程重推，不能只算初始数据。

节点保持上游 `proved / checked_by: agent`，不是 Lean 证书；`ass:weighted-package` 保持 `refuted`（`excluded`）。
可行的替代方案（未执行、需用户决定）：先给 `ass:weighted-package` 写一个显式的 Lean 命题（把过程量作为参数或
结构字段抽象出来），再把驳斥写成对该命题的否定；但这需要先取得上游档案确认过程量的精确定义。

## `lem:relative-perimeter-smoothing`（Blueprint 第 60 章，附录 A）

Blueprint 陈述：对每个光滑区域 `U`（开集，局部位于其 C^∞ 边界一侧）且 `P_ρ(U) = ∫_{∂U∩Ω} ρ dH^{n−1} < ∞`，
存在全局光滑 Lipschitz 函数 `0 ≤ u_j ≤ 1`，`u_j → 1_U` 于 `L¹(ν)` 且 `limsup ∫‖∇u_j‖ dν ≤ P_ρ(U)`；区域与凸载体可无界。
证明：向外膀胀后磨光，用对数凹密度比较 `(M/b₀)^{(1−s)/s}` 与曲面测度的膀胀标度 `s^{1−n}` 控制梯度积分。

**结论：`missing`（与预期一致）。**

- 光滑区域与相对周长 `P_ρ(U)` 没有 Lean 定义。Mathlib 有 Hausdorff 测度 `μH[d]` 与标度律 `hausdorffMeasure_smul₀`，
  但没有 C¹ 超曲面的曲面测度理论（面积公式、光滑边界上 `μH[n−1]` 的局部有限性）。
- 指示函数分布梯度等于定向曲面测度（Gauss–Green）及其全变差由 `P_ρ` 控制：Mathlib 的散度定理只对盒子
  （`MeasureTheory/Integral/DivergenceTheorem.lean`）；没有有限周长集或多元 BV 函数（`Analysis/BoundedVariation.lean`
  是一维的）。
- 卷积估计 `∫‖∇(η_ε * v_s)‖ dν ≤ s^{1−n}(M/b₀)^{(1−s)/s} P_ρ(U)`：Mathlib 的卷积可对光滑因子求导，但没有"梯度积分 ≤
  另一因子的全变差"的界；无界边界上的 Tonelli 需要曲面测度局部有限。
- 可用部分：`thm:borell-logconcave-density`（`\uses`）的密度表示、紧子集上的双侧界与支撑内部凸性均已认证；
  磨光后的 `L¹(ν)` 收敛与 `∂U` 的 ν-零测原则上可从中得到。库内 `KLS.Isoperimetry.boundaryContent` 是 Minkowski 边界
  含量，不是 `P_ρ`。

下游 `lem:relative-perimeter-cheeger-infimum`、`thm:klartag-density-frontend-identification`、
`thm:logconcave-cheeger-poincare-comparison` 保持 `blocked`。

## 元数据

tasks.json 两个节点：`mathematics` 不变（`local_argument`），`infrastructure` 改为 `missing`，`mathlib_revision` 为钉住提交，
证据为所读的 Blueprint 章节、库内模块与 Mathlib 源码哈希，gaps 逐条列出上述缺口。HANDOFF 与 `verification.md`
各加一句指向本记录。最终验证收据由 `python3 research/verify.py` 在本记录之后重新生成。
