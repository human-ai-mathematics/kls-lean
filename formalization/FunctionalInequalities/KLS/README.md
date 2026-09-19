# KLS 文件导航

当前语义状态（2026-09-19，Cheeger 线接手后）：**25 个证书；5 个直接洞（0/0/5）**，仅剩 `Energy/WIP/Cheeger.lean`；`KLS/WIP/` 目录已不存在。Cheeger 下确界两洞在 [`Geometry/Cheeger/Equality.lean`](Geometry/Cheeger/Equality.lean) 证出并以逐字节相同的 `pp.all` 签名迁入，`lem:relative-perimeter-cheeger-infimum` 注册为第 25 个证书（`Solutions.LemRelativePerimeterCheegerInfimum.certificate`）；Cheeger 不等式 `C_P^lit(μ) ≤ 4Ψ_KLS(μ)²` 在 [`Geometry/Cheeger/Inequality.lean`](Geometry/Cheeger/Inequality.lean) 证出，Buser 半未证。

历史语义状态（2026-09-19，Cheeger 线接手前）：24 个证书；**7 个直接洞（0/2/5）**，位于两个 WIP 模块（`WIP/CheegerInfimum.lean` 与 `Energy/WIP/Cheeger.lean`）。尖锐 `Analysis.sard` 已在 `Analysis/Sard/Sharp.lean` 证明（Morse 路线，`pp.all` 签名逐字节不变），`WIP/AnalyticPrerequisites.lean` 已删除。

历史语义状态（2026-09-16）：24 个证书；8 个直接洞（1/2/5），仅位于三个 WIP 模块。
恢复序列 `KLS.RelativePerimeter.exists_smooth_recovery_sequence` 已证明，相关基础设施为
available，并已补上现有证明的 Blueprint 链接和完成标记，未新增账本证书。
Cheeger-infimum 基础设施仍 missing，具体是
超水平集积分界和反向比较。coarea、光滑 Sard、Gauss–Green 和恢复序列不再是缺失前提。
下方各轮记录保留当时的状态；当前状态以本段及
[语义对齐记录](../../../research/decisions/2026-09-16-semantic-alignment.md)为准。

历史进度（2026-09-16，L13 轮）：**加权 coarea 推广到局部 Lipschitz**。
[`Geometry/Coarea/LocallyLipschitz.lean`](Geometry/Coarea/LocallyLipschitz.lean) 证明
`KLS.coarea_of_locallyLipschitz`：只假设 `LocallyLipschitz u`，给出同样的加权等式与切片
`AEMeasurable`，不要求 Lipschitz 常数、不要求 C¹，也不加有界、有限体积、可积性或 SFinite。
它是 **L11 与 L12 的共同推广**（两条原定理语句、证明均不变，也没有用它重述）：
`LipschitzWith K u` 与 `ContDiff ℝ 1 u` 都蕴涵 `LocallyLipschitz u`。
推广是**严格**的，客户端证明 `x ↦ x² + ‖x‖` 局部 Lipschitz、对任何常数都不是全局 Lipschitz、
且在 0 处不可微，两条原定理都够不到它。证明用半开环带归约到 L12：闭球上 McShane 延拓成全局
Lipschitz 代表，每片落在**开**球内，故梯度逐点相等、水平集切片一致，再用可数不交可加性拼接。
**本轮不迁洞**，直接洞仍 **8（1/2/5）**，证书仍 **24**，perimeter infrastructure 仍 **missing**。
审计见 `research/audits/LocallyLipschitzCoareaAudit.lean`（10 条报告全标准，不导入任何 WIP），
详见[L13 决定](../../../research/decisions/2026-09-16-locally-lipschitz-coarea.md)。

**对数凹 Cheeger–Buser 线（等周常数几种定义的对齐直到与 Poincaré 常数的双向比较，
含 `WIP/CheegerInfimum.lean` 剩下的两个洞）已于 2026-09-16 交给王浩丞，本轮刻意未触碰。**

上一轮（2026-09-16，T2 迁出轮）：**最后一个原始 coarea 洞已闭合**。
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 从
`WIP/AnalyticPrerequisites.lean` 迁到无洞的
[`Geometry/Coarea/Lipschitz.lean`](Geometry/Coarea/Lipschitz.lean) 末尾，
`pp.all` 签名经**机器逐字节核对**不变（同一 universe 参数 `u`、同样六个实例及顺序，
含语句里 `gradient` 实际使用的 `CompleteSpace V`、同样的 binder 与假设名、同样的结论），
由同文件的 **L12** `KLS.coarea_of_lipschitz` 在 `S = Set.univ` 时证明，不新增兼容 alias，
不重复证明 coarea，也不增加 C¹/正维/有限体积/可积性/SFinite 假设。**本轮未证明新定理。**
直接洞 **9（2/2/5）→ 8（1/2/5）**；`WIP/AnalyticPrerequisites.lean` 只剩尖锐
`C^(finrank)` `Analysis.sard`，它与 `Analysis.ae_forall_fderiv_ne_zero` 的语句和证明原样保留。
T1/T2/T3 三个原始目标现已全部正式接通。证书仍 **24**，perimeter infrastructure 仍 **missing**。
审计见 `research/audits/LipschitzCoareaMigrationAudit.lean`，
详见[迁出决定](../../../research/decisions/2026-09-16-t2-coarea-migration.md)。

上一轮（2026-09-16，L12 完成）：`Analysis/LipschitzJet.lean` 证明 **L6a** 紧 jet 提取，
`Analysis/LipschitzC1Pieces.lean` 证明 **L7** 精确 C¹ 分片，
`Geometry/Coarea/Lipschitz.lean` 证明 **L12** 的 Lipschitz
带权 coarea 等式及切片 AEMeasurable，不假设 C¹、正维、有界、有限体积或有限权重。
原始 L6a/L7/L12/T2 语句的证明均通过新客户端审计，15 条公理报告全标准。
该轮所有旧 Lean 文件保持原字节，直接洞仍 **9（2/2/5）**。

历史轮次（2026-09-16，L6 完成）：[`Analysis/WhitneyConstruction.lean`](../Analysis/WhitneyConstruction.lean)
已证明紧集一阶 jet 的全局 C¹ 延拓，精确保留值和环境导数；含空集、稀疏集和零维。
定量覆盖、光滑单位分解及两项一致误差估计均已构造。新客户端证明原始 L6 全部量词，
13 条公理报告全标准。下一步 **L6a 紧 jet 提取 → L7 精确 C¹ 分片 → L12 Lipschitz coarea**。
直接洞 **9（2/2/5）**、证书 **24**、perimeter infrastructure **missing** 不变。

以下为各轮历史快照；其中“未证明”和“下一步”描述的是当轮状态。

历史轮次（2026-09-16，L6 边界拼接）：`Analysis/WhitneyExtension.lean` 已证明从补集上
具有定量 jet 估计的 C¹ 候选函数拼出全局 C¹ 延拓，保持紧集上的精确值与导数。
**还没有构造满足估计的候选函数，因此 L6 一般存在性仍未证明**；下一步是 Whitney
覆盖、带导数控制的单位分解及仿射 jet 求和估计。新客户端 13 条公理报告全标准。
直接洞 **9（2/2/5）**、证书 **24**、perimeter infrastructure **missing** 不变。

上一轮（2026-09-16，FirstOrderJet 收尾）：紧集上一阶 jet 的一致余项条件已证明为
全局 C¹ 实现的**必要条件**（`Analysis.uniform_jet_remainder_of_contDiff`）。
**L6 的延拓存在性仍未证明**，是下一步；L6a/L7/Lipschitz coarea 仍未完成。
直接洞 **9（2/2/5）**、证书 **24**、perimeter infrastructure **missing**。

上一轮（2026-09-16，C¹ coarea 迁出轮）：**第二个原始 coarea 洞已闭合**。
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 已从 `WIP/CheegerInfimum.lean`
迁出到无洞的 [`Geometry/Coarea/Isoperimetry.lean`](Geometry/Coarea/Isoperimetry.lean)，
`pp.all` 签名**逐字节不变**（机器 `diff` 核对，含未使用的 `CompleteSpace`、
`SecondCountableTopology` 与未使用的假设名 `hK`），由上一轮的 L11 取 `S = univ` 证明，
**不再带 `sorryAx`**。直接洞 **10（2/3/5）→ 9（2/2/5)**；`WIP/CheegerInfimum.lean`
只剩两条 Cheeger 比较。本轮**没有新定理**，也**没有**证明 Lipschitz 情形
（`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 不假设 `C¹`，仍是直接洞，
需要 L12 → L7 → L6）。
详见[迁出决定](../../../research/decisions/2026-09-16-isoperimetry-coarea-migration.md)。

上一轮（2026-09-16，C¹ coarea 轮）：**已证明加权 coarea 路线的 L11**——对**任意** `C¹` 实函数、
任意可测集、任意可测 `ℝ≥0∞` 权重给出带权 coarea 等式与切片积分的 `AEMeasurable`
（[`Geometry/Coarea/Smooth.lean`](Geometry/Coarea/Smooth.lean) 的 `coarea_of_contDiff`）。
`u` 不要求 Lipschitz、有界或紧支撑，`S` 不要求有界或有限体积，`g` 允许恒为 `⊤`，
**对导数无任何非退化要求**（临界集可以是整个空间）。L9 与 L10 在此恰好接上、缺一不可：
临界集是闭集故其补是开集，L9 管 `S ∩ R`；左端临界部分因 `gradient u = 0` 贡献为零；
右端由 L10 使临界切片几乎处处零测，同一条 a.e. 相等又把 L9 的 `AEMeasurable` 搬到完整切片函数。
**目标 T3 随之证明**，它正是直接洞 `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
的语句（该声明本来就假设 `ContDiff ℝ 1 u`，其 `LipschitzWith` 假设用不上）。
**本轮未动 WIP**，故直接洞仍 **10**（2/3/5）；迁出可使 `WIP/CheegerInfimum.lean` 由 3 洞降至 2、
总数降至 **9**，按惯例是单独一轮。**Lipschitz 情形仍未证明**：那需要 L12 → L7 → L6 的闭集
Whitney 延拓，全部未证。
详见[C¹ coarea 决定](../../../research/decisions/2026-09-16-smooth-coarea.md)。

上一轮（2026-09-15，正则 coarea 轮）：**完整证明 L9 的两个分量**。
[`Geometry/Coarea/Regular.lean`](Geometry/Coarea/Regular.lean) 的
`coarea_of_contDiffOn_of_fderiv_ne_zero` 给出正则开域上的 C¹ 带权 coarea 等式，连同截面积分的
`AEMeasurable`。无需全局 C¹/Lipschitz、有界性、有限体积、可积性、非零维或 SFinite。
联合参数 C¹ 隐函数、保体积正交分解、逐纤维 Jacobian 换元、图面积与不交 Borel 拼接均已证明。
[`Geometry/OpenSliceMeasurable.lean`](Geometry/OpenSliceMeasurable.lean) 独立处理局部 C¹ 的
可测性。新结果及客户端共 29 条公理检查只含标准三公理；15 个既有客户端重跑通过。
既有 Lean 文件及 WIP 均未修改，直接洞仍 **2/3/5，共 10**；证书 **24**，perimeter
infrastructure **missing**。L11/L12、L6/L6a/L7、两个原有 coarea 等式洞、尖锐 Sard、
Eilenberg 尖锐常数及 Cheeger 反向比较/相等仍未证明。
详见 [L9 决定](../../../research/decisions/2026-09-15-regular-coarea.md)。

以下为历史轮次记录，其“未证明”描述保留当时的边界。

上一轮（2026-09-15，开域图面积轮）：**已证明加权 coarea 路线的 L8**——带权图面积换元从
"参数函数全局 `C¹`"放宽到"只在开集 `O` 上 `C¹`"
（`Analysis/OpenGraphIntegral.lean` 的 `setLIntegral_image_graphMap_of_contDiffOn`）。
开集上 `ContDiffOn` 的函数一般**不能**延拓成全局 `C¹`（`x ↦ x⁻¹` 于 `(0,∞)`），
所以必须做可数局部化：每点取一个球，球上与某个全局 `C¹` 函数相等（`ContDiffBump` 乘法），
第二可数性取可数子族，`disjointed` 分片，`graphMap` 单射使像不交，两边可数可加。
这是**开集内部**局部化，**不是** L6 的闭集 Whitney 延拓（仍未证明）。
L8 给的是**图**的面积，不是 coarea：L9 还需要带水平参数的 C¹ 隐函数族与同维 Jacobian 换元。
详见[开域图面积决定](../../../research/decisions/2026-09-15-open-graph-area.md)。

上一轮（临界截面轮）：**已证明加权 coarea 路线的 L10**——`C¹` 实函数的临界集
`{x | fderiv ℝ u x = 0}` 与几乎每个水平集的交具有零 `surfaceMeasure`
（[`Geometry/CriticalSlice.lean`](Geometry/CriticalSlice.lean)）。这是 **L1 的第一个真正下游
消费者**：临界集上导数为零，而 Mathlib 分片引理的逼近线性映射取自导数的值，故全为零，
逼近直接变成 `ε`-Lipschitz 估计；在球内对每片用 L1 求和，再令 `ε → 0`、对半径取可数并。
**这不是 Sard 定理，也不蕴含它**：Sard 说的是临界**值**集零测（一般需 `C^(finrank)`，仍是
直接洞 `Analysis.sard`），L10 说的是每个水平集中**临界那部分**的余维一测度为零，仅需 `C¹`。
客户端的 `constant_exceptional_level` 用常数函数说明"几乎处处"不能加强成"处处"。
`u` 不要求 Lipschitz、有界或紧支撑，临界集自动是闭集故无需可测性假设，零维覆盖。
直接洞仍 **10**（2/3/5）；L8/L9/L11/L12 与加权 coarea 等式仍未证明。
详见[临界截面决定](../../../research/decisions/2026-09-15-critical-slice.md)。

上一轮（水平集可测性迁出轮）：**第一个原始 coarea 洞已闭合**。
`Analysis.aemeasurable_lintegral_levelSet` 已从 `WIP/AnalyticPrerequisites.lean` 迁出到无洞的
[`Geometry/LevelSetMeasurable.lean`](Geometry/LevelSetMeasurable.lean)，`pp.all` 签名**逐字节
不变**（机器 `diff` 核对），并由上一轮的 L5 证明，**不再带 `sorryAx`**。
直接洞 **11（3/3/5）→ 10（2/3/5）**；证书仍 24，perimeter infrastructure 仍 missing。
本轮**没有新定理**，只有迁出与接线，**没有**证明加权 coarea 等式：
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` 与尖锐 `Analysis.sard` 仍是直接洞。
详见[迁出决定](../../../research/decisions/2026-09-15-levelset-measurable-migration.md)。

上一轮（Borel 截面与可测权重轮）：**已证明加权 coarea 路线的 L4 与 L5**，
并证明了第一个原始目标 **T1 的完整语句**。
L4（`aemeasurable_surfaceMeasure_inter_levelSet`）把三条已证结果合起来用：内正则性把可测 `S`
拆成递增紧集列加体积零余项，紧集部分用 **L3**，下连续性取上确界，余项用 **L2**；
L5（`aemeasurable_setLIntegral_inter_levelSet`）再用简单函数逼近，把每个简单权重的截面积分
写成可测集 `S ∩ s ⁻¹' {c}` 的截面测度的**有限和**，**不使用任何需要 `SFinite` 的参数积分定理**。
两者都去掉了 `[CompleteSpace V]`，并把全局 Lipschitz 减弱为连续加**只在 `S` 上** Lipschitz；
`S` 不要求有界、非空或有限体积，`g` 允许无界、不可积或恒为 `⊤`。
L4/L5 只给**可测性，不给等式**：加权 coarea 等式本身（L6–L12、目标 T2/T3）完全未动。
详见[Borel 截面决定](../../../research/decisions/2026-09-15-borel-slice-measurable.md)。

上一轮（紧集截面可测性轮）：**已证明加权 coarea 路线的 L3**——对**紧** `S` 与
仅连续的 `u`，`t ↦ surfaceMeasure V (S ∩ {u = t})` 是 Borel 可测函数
（`Geometry/Surface/Slicing.lean` 的 `measurable_surfaceMeasure_inter_levelSet`，底层是只依赖
Mathlib 的新模块 `Analysis/HausdorffContent.lean`）。L3 **不是** L1 的推论：L1 只给构造出来的
支配函数的可测性。证明走两层结构——固定尺度上的**开覆盖** content 对水平上半连续（紧的
`S \ U` 使 `u` 与该水平保持正距离），且开覆盖 content 的尺度极限仍是 `μH[d]`（逐块加厚，
直径增量由余量吸收、成本增量由可和正数列吸收）。固定尺度上 `openCoverCost` 一般严格大于
`coverCost`，所以等式必须经过尺度极限；**没有**宣称 `μH[d]` 自身上半连续（一般不成立）。
**L4（Borel 集）与 L5（可测权重）仍是缺口**：L3 对一般 Borel 集没有任何断言，而第一个原始
coarea 洞是对 `univ` 陈述的，紧集版本填不了它。
详见[紧集截面决定](../../../research/decisions/2026-09-15-compact-slice-measurable.md)。

上一轮（Eilenberg 上界轮）：**已证明加权 coarea 路线的 L1**（带显式正常数），
上一轮的 **L2** 成为其零测特例且语句逐字未变。对只在 `S` 上 Lipschitz 的 `u`，截面函数
`t ↦ surfaceMeasure V (S ∩ {u = t})` 被**可测**支配函数 `F` 控制，且
`∫⁻ F ≤ eilenbergConstant V · K · volume S`，其中 `eilenbergConstant V = 4 ω_{n-1}/ω_n > 0`
（`Geometry/Surface/Slicing.lean`），底层是只依赖 Mathlib、任意 `EMetricSpace`、无维数无环境
测度的 `Analysis.exists_measurable_majorant`（`Analysis/HausdorffSlicing.lean`，Mathlib 直径
规范下常数 `2`）。不声称常数尖锐；客户端算出线上为 `2`、零维为 `4`。
不要求 `S` 可测、有界、非空或有限体积，不要求 `u` 全局 Lipschitz、可微或可测，
`K = 0` 与 `volume S = ⊤` 是显式分支，零维与 `[CompleteSpace V]` 均无需假设。
可测性**只**对构造出的支配函数成立：截面函数本身的可测性（L3–L5）仍是缺口。
三个原始 coarea 洞、尖锐 Sard、反方向比较、乘积超水平集界与两个 Cheeger 常数相等仍未证明；
证书 24、perimeter infrastructure missing（该轮直接洞 3/3/5，已由迁出轮降为 2/3/5）。
详见[Eilenberg 上界决定](../../../research/decisions/2026-09-15-eilenberg-majorant.md)、
[零集切片决定](../../../research/decisions/2026-09-15-null-slicing.md)与
[加权 coarea 路线](../../../research/decisions/2026-09-15-weighted-coarea-route.md)。

本目录组织 KLS 目标使用的定义、对数凹工具和具体路线对象。数学来源写在各 Lean 模块开头；
证明状态由[ledger](../../../research/a-series/ledger.yaml)与当前声明、证明共同记录。

## 阅读入口

| 文件或目录 | 职责与边界 |
| --- | --- |
| [Definitions.lean](Definitions.lean) | 紧集对数凹定义、局部斜率、文献测试域和常数；共享定义入口 |
| [Statement.lean](Statement.lean) | 协方差归一化的 KLS 猜想命题；没有 KLS 证明 |
| [Target.lean](Target.lean) | `theorem kls : Conjecture := by sorry`——KLS 断言本身，仓库唯一有意保留的直接洞；只被聚合根 import，不进任何证书闭包与 Blueprint `\lean` 标签（2026-09-19，见 `research/decisions/2026-09-19-kls-target-theorem.md`） |
| [LogConcave/](LogConcave/README.md) | 对数凹传输、紧集/Borel 等价、内禀绝对连续性、Borell 密度表示、仿射协方差常数的对数凹契约与闭形式、环境平移下的对数凹性与重心、KLS 的仿射/各向同性归约、实轴上的一维 `4·Var` Poincaré 界（`LogConcave/Line/`，Bobkov 的 `12·Var` 作为推论保留） |
| [LocalSlope/Gradient.lean](../Energy/LocalSlope/Gradient.lean) | 局部斜率与梯度关系，以及绝对连续性前提下的能量和测试域识别；已证明 |
| [Isotropic.lean](Isotropic.lean) | 有限二阶矩、零均值和单位协方差的定义；白化在 `Probability/CovarianceWhitening.lean`，仿射/各向同性归约在 `LogConcave/Isotropic.lean` |
| [Isoperimetry.lean](Isoperimetry.lean) | 仿射载体上的边界含量、等周常数及逆尺度定义；不提供 Cheeger 比较 |
| [ConditionalFiber/Basic.lean](ConditionalFiber/Basic.lean) | 条件纤维能量的构造及六条已证明的良定义性契约；本文件不提供闭性、Markov 性或框架界 |
| [ConditionalFiber/Closed.lean](ConditionalFiber/Closed.lean) | 条件纤维形式的两点跳跃表示、两点测度的交换不变性、Lipschitz 界 `d·L²`、稠密定义域、下半连续与 Markov 性，合成 `Energy.Dirichlet`；对任意 Borel 律与方向律成立，不提供与梯度能量的比较或框架界 |
| [ConditionalFiber/EnergyComparison.lean](ConditionalFiber/EnergyComparison.lean) | 纤维 Poincaré 输入 `FiberBound μ ρ κ` 下，条件纤维能量与局部斜率（梯度）能量的比较 `energy_le_of_fiberBound`（`D_{μ,ρ}(f) ≤ κ·∫‖∇f‖²`，有限）及形式差界 `C` 到 `C_P^lit(μ) ≤ κC` 的传递 `literatureConstant_le_of_fiberBound`；要求 `μ ≪ Haar` 与可容许框架，不固定 `κ` 的取值，不提供纤维对数凹性或框架界 |
| [ConditionalFiber/SliceKernel.lean](ConditionalFiber/SliceKernel.lean) | 给定 Haar 密度 `p` 时沿直线的显式切片核 `sliceKernel`（密度 `t ↦ p(z+tθ)/Z(θ,z)`，坏基点取狄拉克律）；`compProd_baseLaw_sliceKernel`（`baseLaw ⊗ₘ sliceKernel = jointLaw`）与 `ae_sliceKernel_eq`（与所选条件核几乎处处相等）；不假设对数凹，只要一个 Haar 密度 |
| [LogConcave/ConditionalFiber.lean](LogConcave/ConditionalFiber.lean) | 全维对数凹律的条件纤维几乎处处对数凹 `ae_conditionalFiber_logConcave`，由此得 `FiberBound μ ρ 4`、`D_{μ,ρ}(f) ≤ 4·∫‖∇f‖²` 与 `C_P^lit(μ) ≤ 4C`（Blueprint 的 `12` 版本带 `_of_four` 后缀保留）；不提供框架界，`q:conditional-fiber-frame` 仍开放 |
| [Geometry/Surface/Homothety.lean](Geometry/Surface/Homothety.lean) | 无洞带权换元：归一化 surfaceMeasure 在逆 homothety 下的 pushforward，任意可测集合及 frontier 上的带权 lintegral 换元，无测度有限性要求 |
| [LogConcave/DensityBounds.lean](LogConcave/DensityBounds.lean) | 无洞密度界：由 WIP 迁入的全局上界、凸组合密度比较；positivity set 内部包含于测度支撑内部，供 Ω 外零贡献使用；公开的下界球 `exists_ball_le` 与绝对连续性 `absolutelyContinuous` |
| [Geometry/RelativePerimeter.lean](Geometry/RelativePerimeter.lean) | 无洞相对周长应用：周长定义、indicator 外扩 L¹ 收敛、核平均密度界及已证明的 `lintegral_enorm_gradient_mollified_homothety_le`；不要求区域有界、边界总测度有限或相对周长有限，覆盖零维 |
| [Geometry/PerimeterRecovery.lean](Geometry/PerimeterRecovery.lean) | 无洞恢复层：磨光的局部常值精确公式 `mollifiedIndicator_eq_indicator_of_const`、半径趋零的 `L¹(ν)` 选择 `exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt`，以及已证明的 `RelativePerimeter.exists_smooth_recovery_sequence`；逐项 `C^∞`／Lipschitz／`[0,1]`，不要求区域、边界或载体有界，不要求 Lipschitz 常数一致，覆盖零维与零周长 |
| [Geometry/MinkowskiContent.lean](Geometry/MinkowskiContent.lean) | 无洞坐标空间含量层（本地导入闭包为空，只依赖 Mathlib）：`minkowskiContent` 定义、`measure_closure_eq_of_minkowskiContent_ne_top`、局部上确界 `ballSup` 及其 Lipschitz 传递与近邻见证 `thickening_superlevel_subset`，以及已证明的 Minkowski 余面积不等式 `lintegral_minkowskiContent_superlevel_le`；任意概率律（含奇异、原子），`u` 只要 `C¹` 与全局 Lipschitz，不要求密度、绝对连续性、有界值域或非零维数 |
| [Geometry/MinkowskiConstant.lean](Geometry/MinkowskiConstant.lean) | 无洞 Cheeger 下确界层（本地导入闭包只有无洞的 `Geometry/MinkowskiContent.lean`）：由 WIP 原样迁入的 `minkowskiConstant` 与 `minkowskiConstant_eq_top_of_subsingleton`（`pp.all` 签名逐字节不变）、下确界的乘积形式 `minkowskiConstant_mul_min_le`（零质量与满质量由 `⊤ * 0 = 0` 收尾，不代入下确界）、开闭超水平集质量的几乎处处一致 `ae_measure_superlevel_lt_eq_le`（任意 `SFinite` 测度、任意可测 `u`）、平衡量可测性 `measurable_min_measure_superlevel`（任意 `u`），以及已证明的 `minkowskiConstant_mul_lintegral_min_superlevel_le`；任意概率律（含奇异、原子），不要求密度、非原子性、非零维数或 `h_M` 有限 |
| [Geometry/DistanceCutoff.lean](Geometry/DistanceCutoff.lean) | 无洞距离截断层（**本地导入闭包为空**，只依赖 Mathlib）：由 WIP 原样迁入的 `distanceCutoff` 定义、`distanceCutoff_mem_Icc`、`lipschitzWith_distanceCutoff`、两条边界取值引理与 `L¹(ν)` 收敛 `tendsto_distanceCutoff_indicator`（`pp.all` 签名逐字节不变），以及已证明的梯度积分估计 `lintegral_enorm_gradient_distanceCutoff_le`；`B` 任意（不要求非空、可测、闭、有界），右端保留 `ν (closure B)`，`m`／Haar／`hac` 原样保留但证明不使用。**逐点**结论：截断在两个常值集上取全局极值，`IsLocalMax/IsLocalMin.fderiv_eq_zero` 无需可微性假设，故不用 Rademacher、Lebesgue 密度定理或水平集梯度一般引理 |
| [Geometry/Cheeger/Equality.lean](Geometry/Cheeger/Equality.lean) | 无洞等式层（2026-09-19）：由已删除的 `WIP/CheegerInfimum.lean` 原样迁入的七条公开声明（`exists_smooth_approximation_lipschitz`、两个前洞、`minkowskiConstant_eq_smoothConstant`、三条内禀传输，`pp.all` 逐字节相同），加 `smoothConstant_mul_min_le`、`relativePerimeter_le_lintegral_levelSet`、`lintegral_enorm_gradient_eq_lintegral_levelSet_density`、`lintegral_enorm_distanceCutoff_sub_indicator_le`、`min_measure_le_lintegral_min_superlevel_add`；不依赖 `sorryAx`。 |
| [Geometry/Cheeger/Inequality.lean](Geometry/Cheeger/Inequality.lean) | 无洞 Cheeger 不等式层（2026-09-19）：`L¹` Cheeger `minkowskiConstant_mul_lintegral_le`、正部平方界、有界 `C¹` Lipschitz 与全部可容许测试的 `h_M² Var ≤ 4∫‖∇g‖²`、`smoothTest_constant_le`（`C_P^smooth(ν) ≤ 4/h_M²`，任意 Borel 律）、`LogConcave.literatureConstant_le_four_mul_inverseScale_sq`（对数凹律）；Buser 半未证。 |
| [Geometry/Median.lean](Geometry/Median.lean) | 中位数存在 `exists_median`（分布函数的左右连续性）。 |
| [Geometry/Cheeger/Infimum.lean](Geometry/Cheeger/Infimum.lean) | 无洞单向比较层（**无 WIP**）：由 WIP 原样迁入的 `smoothConstant`、`smoothConstant_eq_top_of_subsingleton`、`lintegral_measure_symmDiff_superlevel`、`min_measure_le_add_measure_symmDiff`、`tendsto_lintegral_min_superlevel`（`pp.all` 签名逐字节不变），以及已证明的 `minkowskiConstant_le_smoothConstant`；零维、无可取光滑域、单个域相对周长为 `⊤`、常数为 `⊤` 均被覆盖，不要求支撑或区域有界、边界总测度有限、常数有限或相对周长有限。**只证一个方向**：反方向与等式仍在 WIP |
| [Geometry/SmoothDomain.lean](Geometry/SmoothDomain.lean) | 无洞基础：光滑区域结构、frontier 定义接口、归一化约定检查、`empty`／`univ`／homothety、局部边界有限性、Haar 零测度与总边界 Hausdorff 缩放；2026-09-14 新增正则超水平集构造 `ofSuperlevel` 与 `ofSuperlevel_carrier`——`C∞` 函数的**严格**超水平集 `{x | t < u x}` 在 `fderiv ℝ u` 于 **`frontier`** 上非零时即为光滑域，定义函数按负子水平约定取 `φ = t - u`，邻域取 `{y | fderiv ℝ u y ≠ 0}`；不要求整条水平集正则、不要求全空间非零、不要求正维数或有界，空边界／空载体／全载体／零维由构造自然覆盖 |
| [Geometry/Mollification.lean](Geometry/Mollification.lean) | 无洞磨光接口：`mollifiedIndicator`、indicator 局部可积性、卷积表示、光滑性／Lipschitz／`[0,1]` 值域 |
| [Geometry/MollifiedBoundary.lean](Geometry/MollifiedBoundary.lean) | 无洞后果：`gradient_mollifiedIndicator_eq` 与已证明的 `enorm_gradient_mollified_le`；向量积分可积、核非负、外法向单位长度，不假设区域有界或边界总测度有限 |
| [Geometry/BoundaryChart.lean](Geometry/BoundaryChart.lean) | 应用层（无 `sorry`）：由 `WIP/AnalyticPrerequisites.lean` 迁入的外法向 `outwardNormal` 及 `outwardNormal_eq`、`norm_outwardNormal`、`continuousOn_outwardNormal`、`measurable_outwardNormal`（名称与陈述不变）；切超平面 `tangentSpace`/`tangentEmbedding`/`tangentCoord`、正交分解 `isGraphSplitting_tangent`、`finrank_tangentSpace`；局部边界图表 `BoundaryChart` 与 `exists_boundaryChart`（柱内边界恰为图、区域恰为图下方、沿图的外法向 `(ι(-∇g)+ν)/√(1+‖∇g‖²)`）；面积等式 `BoundaryChart.surfaceMeasure_image`。直接导入无洞基础 `Geometry/SmoothDomain.lean`，没有 WIP 依赖 |
| [Geometry/LocalGaussGreen.lean](Geometry/LocalGaussGreen.lean) | 应用层（无 `sorry`）：图表局部 Gauss–Green `BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`——对满足 `tsupport F ⊆ C.cylinder` 的紧支撑 `C¹` 向量场，`∫_U div F = ∫_{∂U} ⟪F, ν⟫ ∂surfaceMeasure`；两条局部化引理 `integral_divergence_carrier`（体积分退化到全局子图，柱外 `F` 与 `divergence F` 同时为零）与 `integral_inner_outwardNormal_frontier`（通量退化到单张图片，Jacobian 与单位法向分母逐点抵消）。**不是**任意紧支撑场的全局定理，全局拼接在 `Geometry/GaussGreen.lean`；不假设边界总测度有限 |
| [Geometry/GaussGreen.lean](Geometry/GaussGreen.lean) | 应用层（无 `sorry`）：**全局** Gauss–Green `SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`——对任意紧支撑 `C¹` 向量场，`∫_U div F = ∫_{∂U} ⟪F, ν⟫ ∂surfaceMeasure`，不假设区域有界、边界总测度有限、`F` 更光滑或 `V` 非平凡；三类局部块引理 `…_of_tsupport_subset_carrier`（内部块）、`…_of_tsupport_subset_compl_closure`（外部块）与图表块（调用 `LocalGaussGreen`）；由 `WIP/AnalyticPrerequisites.lean` 迁入的 `isLocallyFiniteMeasure_surfaceMeasure_frontier`、`integrableOn_smul_outwardNormal`（名称与陈述不变），以及有限求和交换所需的 `norm_outwardNormal_le_one`、`integrableOn_inner_outwardNormal` |
| [Geometry/Surface/Slicing.lean](Geometry/Surface/Slicing.lean) | L1–L5：显式非尖锐 Eilenberg 上界、零集切片、连续函数的紧集截面 Borel 可测性，以及连续且在可测集合上 Lipschitz 时的截面与可测 ENNReal 权重积分的 a.e. 可测性。无有限体积、权重有限或正维假设；不假设 surfaceMeasure 为 SFinite。零维使用 ℋ⁰，而非零测度。这里只给可测性与上界，coarea 等式由后续模块证明 |
| [Geometry/Surface/Measure.lean](Geometry/Surface/Measure.lean) | 基础定义层（无 `sorry`）：单位球体积 `unitBallVolume`、归一化 Hausdorff 测度 `hausdorffNormalized` 与面积测度 `surfaceMeasure`；不含定理，供 `Analysis/LevelSet.lean` 与周长层共用 |
| [Geometry/RegularSuperlevel.lean](Geometry/RegularSuperlevel.lean) | 无洞正则超水平集层：由 `WIP/CheegerInfimum.lean` 迁入的 `SmoothDomain.frontier_superlevel_subset` 与 `SmoothDomain.ae_exists_superlevel`（`pp.all` 签名逐字节不变）。后者现由**已证明**的光滑 Sard `Analysis.sard_smooth` 经 `Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top` 得到，**不再继承 `sorryAx`**；不用尖锐 `C^(finrank)` 的 `Analysis.sard`。`Geometry/SmoothDomain.lean` 刻意保持与 Sard 无关，故打包放在其上一层 |
| [Geometry/Coarea/Isoperimetry.lean](Geometry/Coarea/Isoperimetry.lean) | 无洞 C¹ coarea 交付层：由 `WIP/CheegerInfimum.lean` 迁入的 `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`（`pp.all` 签名逐字节不变，机器 `diff` 核对），现由 L11 `coarea_of_contDiff` 取 `S = univ` 证明，**不再带 `sorryAx`**；未使用的 `hK`、`CompleteSpace`、`SecondCountableTopology` 一律保留以固定接口。**不含** Lipschitz 情形 |
| [Geometry/Coarea/Smooth.lean](Geometry/Coarea/Smooth.lean) | 无洞 C¹ coarea 层：`isOpen_regular` 与 `coarea_of_contDiff`（L11）——任意 `C¹` `u`、任意可测 `S`、任意可测 `ℝ≥0∞` 权重的带权 coarea 等式加切片 `AEMeasurable`；不要求 Lipschitz、有界、有限体积，`g` 允许恒 `⊤`，临界集可为全空间。由 L9（正则开域）与 L10（临界切片零测）拼成，两者缺一不可。**目标 T3 即其 `S = univ` 特例**；**不含** Lipschitz 情形（需 L12/L7/L6） |
| [Geometry/CriticalSlice.lean](Geometry/CriticalSlice.lean) | 无洞临界截面层：`isClosed_critical`、`exists_lipschitzOnWith_critical_cover`（临界集上导数为零使 Mathlib 分片引理的逼近变成 `ε`-Lipschitz 估计，分片两两不交且可测）与 `ae_surfaceMeasure_critical_inter_levelSet_eq_zero`（L10）。**L1 的第一个下游消费者**；`u` 不要求 Lipschitz、有界或紧支撑，零维覆盖。**不是 Sard**：对临界**值**集无任何断言 |
| [Geometry/LevelSetMeasurable.lean](Geometry/LevelSetMeasurable.lean) | 无洞水平集可测性层：由 `WIP/AnalyticPrerequisites.lean` 迁入的 `Analysis.aemeasurable_lintegral_levelSet`（`pp.all` 签名逐字节不变，机器 `diff` 核对），现由 L5 `KLS.aemeasurable_setLIntegral_inter_levelSet` 取 `S = univ` 证明，**不再带 `sorryAx`**。保留 `Analysis` 命名空间是为了公共名不变；文件放在 `KLS/Geometry/` 是因为语句出现 `KLS.surfaceMeasure`。**不含**加权 coarea 等式 |
| （已无 `WIP/` 目录）| 2026-09-19 删除 `AnalyticPrerequisites.lean`（尖锐 Sard 已证，迁入 `Analysis/Sard/Sharp.lean`）与 `CheegerInfimum.lean`（两洞已证，七条声明迁入 `Geometry/Cheeger/Equality.lean`）；以下为历史描述：`CheegerInfimum.lean` 有超水平集积分界与反向比较的 2 个直接洞，等式及其内禀推论仍继承 `sorryAx`。原始 T1/T2/T3 均已迁到无洞几何模块；这些 WIP 文件不进库根聚合或证书导入闭包 |

两个 KLS WIP 文件共 3 个直接 `sorry`，另有 `Energy/WIP/Cheeger.lean` 的 5 个，合计 8；
先前几轮接入并证明了三条已有数学输入的接口（Hausdorff 归一化、边界局部有限性、光滑 Lipschitz 逼近），
并证明了余维一面积公式（`Analysis/AreaFormula.lean`）、把标量形式 Gauss–Green 归约到向量形式。
### 历史构造记录

以下按轮次保留当时的证明边界；洞数、未证明项和待迁移项不代表当前状态。当前以页首及文件表为准。

2026-09-13 一轮证明了局部 `C^∞` 边界图表示、区域侧别与外法向公式，并把面积公式接到
`surfaceMeasure`（`Analysis/ImplicitGraph.lean` 与 `Geometry/BoundaryChart.lean`，均无 `sorry`）。
同日后一轮证明了光滑子图上的散度公式与带权边界积分换元（`Analysis/SubgraphDivergence.lean`、
`Analysis/GraphIntegral.lean`），并接通图表交付**图表局部** Gauss–Green
（`Geometry/LocalGaussGreen.lean`，均无 `sorry`）。同日第三轮用有限光滑单位分解
（`Analysis/PartitionOfUnity.lean`）把图表块、内部块与外部块拼成**全局**向量形式 Gauss–Green
（`Geometry/GaussGreen.lean`，无 `sorry`，只依赖标准三条公理），标量形式与磨光 indicator 梯度公式随之闭合；
本轮进一步证明逐点磨光梯度范数上界并移除所有几何基础到 WIP 的导入边；
标量形式已迁入 `Geometry/GaussGreen.lean`，磨光后果在 `Geometry/MollifiedBoundary.lean`。
外扩积分估计与光滑恢复序列现已闭合，`WIP/RelativePerimeter.lean` 随之删除；
前一轮又证明了 Minkowski 余面积不等式并把 `minkowskiContent` 迁入无洞的
`Geometry/MinkowskiContent.lean`（本地导入闭包为空）；前一轮证明了乘积余面积界
`minkowskiConstant_mul_lintegral_min_superlevel_le` 并把 `minkowskiConstant` 迁入无洞的
`Geometry/MinkowskiConstant.lean`；前一轮证明了**单向**比较 `minkowskiConstant_le_smoothConstant`
并把 `smoothConstant` 与层积分辅助引理迁入无洞的 `Geometry/Cheeger/Infimum.lean`；
本轮证明了距离截断的梯度积分估计 `lintegral_enorm_gradient_distanceCutoff_le`
并把整套截断基础迁入无洞、零本地依赖的 `Geometry/DistanceCutoff.lean`。
低维基础情形 `Analysis.sard_of_finrank_le_one` 已在 `Analysis/Sard.lean` 无洞证明，
只用标准三公理，涵盖一般实赋范空间的零维 C⁰ 与一维 C¹，不需要定义域测度。
`C^∞` 的 Sard 已在 `Analysis/SmoothSard.lean` 证明，`ae_exists_superlevel` 随之迁出 WIP 并
**不再继承 `sorryAx`**；尖锐 `C^(finrank)` 的 `Analysis.sard`、加权 coarea、
水平集积分可测性与**反方向**比较仍开放。
两个 Cheeger 常数相等**未证**，证书仍为 24。见
[距离截断梯度积分记录](../../../research/decisions/2026-09-13-distance-cutoff-gradient-integral.md)、
[路线与状态勘误](../../../research/decisions/2026-09-13-cutoff-route-audit-correction.md)、
[单向 Cheeger 比较记录](../../../research/decisions/2026-09-13-cheeger-infimum-one-sided.md)、
[Minkowski 常数记录](../../../research/decisions/2026-09-13-minkowski-constant-coarea-product.md)、
[Minkowski 余面积记录](../../../research/decisions/2026-09-13-minkowski-coarea-inequality.md)、
[恢复序列记录](../../../research/decisions/2026-09-13-smooth-recovery-sequence.md)、
[外扩积分界与恢复序列路线](../../../research/decisions/2026-09-13-dilated-gradient-integral.md)、
[逐点梯度界与下一步路线](../../../research/decisions/2026-09-13-mollified-gradient-bound.md)、
[全局 Gauss–Green 记录](../../../research/decisions/2026-09-13-global-gauss-green.md)、
[子图散度记录](../../../research/decisions/2026-09-13-subgraph-divergence-and-local-gauss-green.md)、
[边界图表记录](../../../research/decisions/2026-09-13-boundary-chart-and-area-interface.md)、
[Gauss–Green 进展记录](../../../research/decisions/2026-09-12-gauss-green-area-formula.md)、
[接口接入记录](../../../research/decisions/2026-09-12-perimeter-interface-integration.md)、
[证明记录](../../../research/decisions/2026-09-12-outward-normal-interfaces-proofs.md)。部分完整证明体仍传递依赖 `sorryAx`；
历史审计与保留策略见[当时记录](../../../research/decisions/2026-09-12-status-audit-and-wip-retention.md)。

先读 `Definitions` 和 `Statement` 确定目标；对数凹分析沿子目录的阅读顺序展开。
文献常数比较的结论位于
[KLS/LogConcave/Poincare.lean](../KLS/LogConcave/Poincare.lean)，
完整使用说明见[Poincaré 比较指南](../Poincare/Euclidean/README.md)。

## 文件放置

对数凹性质及其表示定理放在 `LogConcave/`；共享目标定义和其余路线对象保留在本层。
`LogConcave` 谓词目前仍定义在 `Definitions.lean`，子目录直接导入该定义。
目录名不表示证明完成；每个节点的证明状态以 ledger 与证书为准，不能从根模块编译成功推断。

声明命名空间继续使用 `FunctionalInequalities.KLS`，模块路径按主题组织。
后续文件按数学职责放置，证明完成不触发文件移动。旧路径与新路径的对应关系见
[迁移记录](../../../research/explorations/2026-09-07-logconcave-module-layout.md)。

一致二阶余项 `Analysis.exists_uniform_quadratic_remainder` 已在 `Analysis/TaylorRemainder.lean`
无洞证明：任意实赋范空间、C²、紧集中的平坦基点、可在紧集外的近邻，均由同一 δ 控制。
这不证明像集零测。洞仍为 11，证书 24，详见
[决定记录](../../../research/decisions/2026-09-14-uniform-quadratic-remainder.md)。

二维定量覆盖 `Analysis.volume_image_eq_zero_of_quadratic_oscillation` 与二阶平坦层
`Analysis.volume_image_flat_eq_zero` 已在 `Analysis/QuadraticCover.lean` 无洞证明：
有界平面集上的一致二次振幅控制推出像集零测，不需要任何可测性或正则性；
接上余项定理即得平面紧集中**二阶平坦子集**的像零测（不是整个紧集平坦）；
再经可数穷竭得到全平面版本 `Analysis.volume_image_flat_univ_eq_zero`，不留紧性或可测性假设。
详见[覆盖决定记录](../../../research/decisions/2026-09-14-planar-quadratic-cover.md)。

非平坦层 `Analysis.volume_image_nonflat_eq_zero` 与**平面 Sard** `Analysis.sard_plane`
已在 `Analysis/PlanarSard.lean` 无洞证明：C² 函数在 `Fin 2 → ℝ` 上的临界值零测，
临界集不假设可测、有界或紧。非平坦层用带线性主部的中值不等式把临界集变成某坐标上的
Lipschitz 图，**不用隐函数定理**，再塌到一维覆盖引理。这只是二维：
一般 `Analysis.sard`（任意有限维）仍是直接洞，两个消费者仍继承 `sorryAx`；
加权 coarea 与反方向比较仍未证明。详见
[平面决定记录](../../../research/decisions/2026-09-14-planar-sard.md)。

阶数与维数现已参数化：`Analysis.exists_uniform_pow_remainder` 给任意阶一致余项，
`Analysis.volume_image_eq_zero_of_oscillation_pow` 给任意维覆盖引理，
`Analysis.volume_image_flat_pow_eq_zero` 及其全空间版本给 `Fin n → ℝ` 上 `C^n` 函数的
**全平坦层**零测。二阶与平面版本改为语句不变的推论。这只是 `n` 维的顶层：
中间各层、`n` 维 Sard 与一般 `Analysis.sard` 仍未证明。洞仍为 11，证书仍为 24，详见
[决定记录](../../../research/decisions/2026-09-15-higher-order-flat-layer.md)。

`Analysis/SmoothSard.lean` 收集 `C^∞` Sard 降维的三块拼图（分层、平坦方向、正则零集的局部
`C^∞` 图），均无洞、仅标准三公理。这只是拼图：Sard 本身未证，未解除任何 `sorryAx`，
尖锐 `C^n` 的 `Analysis.sard` 语句与直接洞身份不变。详见
[决定记录](../../../research/decisions/2026-09-15-smooth-sard-ingredients.md)。

在此之上，`Analysis/SmoothSard.lean` 已**证明 C^∞ 实值函数的 Sard 定理**
（`sard_smooth_pi`、`sard_smooth`、`ae_forall_fderiv_ne_zero_of_contDiff_top`），
任意有限维、任意维数，临界集不假设可测，仅标准三公理。
审计客户端由它重证 `ae_exists_superlevel` 的语句且不含 `sorryAx`；
但本轮**未改动任何 WIP 文件**，所以该声明仍继承 `sorryAx`，洞仍为 11，
尖锐 `C^n` 的 `Analysis.sard` 仍是直接洞。详见
[决定记录](../../../research/decisions/2026-09-15-smooth-sard.md)。
