# Borell 等价、基础定义与 Claude 证明交接

日期：2026-09-07（Asia/Shanghai）。基线：`0451f2e`，开工时工作树干净，
本地 `main` 与 `origin/main` 跟踪引用一致。Lean/Mathlib 为 v4.33.0，实际 Mathlib
提交为 `db584cd6d46c92f209a44c0f1c829460d327499d`。

用户批准上一轮分析后明确追加：“可以，就这么走，然后依旧留sorry，我让Claude证”。
本决定采用这一较新的要求：定义与已有 Dirac 障碍落地，Borell 等价和 conditional-fiber
良定义性保留七个显式 `sorry`。没有向 Claude 或其他 agent 派发任务。
这是可编译的证明交接，不是 Borell 根节点的证明完成或认证解锁。

## 阅读顺序与状态

1. [HANDOFF](../../HANDOFF.md)、[验证流程](../verification.md)、[命名](../naming.md)。
2. [LogConcaveBorel.lean](../../formalization/FunctionalInequalities/KLS/LogConcaveBorel.lean)：
   `innerMeasure`、`BorelLogConcave` 和唯一待证主定理 `LogConcave.borel_iff`。
3. [Isotropic.lean](../../formalization/FunctionalInequalities/KLS/Isotropic.lean)、
   [Isoperimetry.lean](../../formalization/FunctionalInequalities/KLS/Isoperimetry.lean)、
   [RawEnergyObstruction.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/RawEnergyObstruction.lean)。
4. [ConditionalFiber.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber.lean)：
   先读定义，再读六个待证合同。
5. [StatementChecks](../../solutions/StatementChecks.lean)、
   [Borell 草稿入口](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) 和
   [任务元数据](../tasks.json)。

ledger 新增一个 `drafted / checked_by: null` 节点，原有十个 proved 节点逐项相同。
Borell 草稿入口纳入默认 Solutions 目标，目前没有 `certificate` 包装，未加入只接受
proved 节点的 `check_blueprint.CERTIFICATES` 映射。两个定义和 Dirac 障碍有 Blueprint
锚点及 `leanok`；Borell 等价与 conditional-fiber 整体只有锚点，没有 `leanok`。
没有更改现有路线配置、已证声明的数学内容或任何历史决定文件。

## 文献核对与证据边界

- Bobkov, *Isoperimetric and Analytic Inequalities for Log-Concave Probability Measures*,
  Ann. Probab. 27 (1999), 1903–1921，
  [作者提供的原文](https://www-users.cse.umn.edu/~bobko001/papers/1999_AOP_Isop.pdf)，
  第 1917 页式 (5.1) 明确使用内测度处理可能不可测的 Minkowski 组合。交换两个集合
  或以 `1-t` 替代参数后与本仓库的指数顺序一致。其后针对非 Dirac 律的讨论不成为
  本等价定理的假设。第 1903 页定义使用外扩集合的质量增量下极限。
- Borell, *Convex measures on locally convex spaces*, Ark. Mat. 12 (1974), 239–252，
  [出版社记录](https://link.springer.com/article/10.1007/BF02384761) 核实作者、题名、
  年份、页码及 DOI `10.1007/BF02384761`。完整 PDF 在本次获取中未能读取：
  清华公开镜像返回 HTTP 500，出版社返回订阅预览，Project Euclid 返回访问检查页。
  因而没有声称重新核实其某个定理逐字覆盖完整密度、局部界和矩的组合结论。
  历史接受记录把绝对连续性归于 Theorem 1.1；完整代表元和矩的精确原文段落对应仍应
  在后续密度工作中补核。这一读取限制不是 Mathlib 基础设施缺口，也不改变 mathematics 分类。
- 阶段 A 的具体证明路线是可独立检查的紧集内逼近论证，不以完整 Borell 密度表示为前提。

## Borell 等价：精确合同和基础设施

空间是带 Borel 结构的任意有限维实赋范空间，概率律允许奇异、零维和非满维仿射支撑。
`innerMeasure μ S` 是所有紧子集质量的 ENNReal 上确界，包括空紧集；它是集合函数，
不被包装为可数可加测度。`BorelLogConcave` 对两个 Borel 集和 `0 < t < 1` 量化，
组合一侧仅使用这个内测度。没有二阶矩、绝对连续性或支撑内部非空的额外前提。

当前 Mathlib 起点已核对，具体文件 SHA256 登记在 tasks.json 的 infrastructure.evidence：

| 工作 | 已有 API / 文件 |
| --- | --- |
| 紧集内正则 | `Measure/Regular.lean` 的有限维可用 `InnerRegular` 实例、`InnerRegularCompactLTTop`；`MeasurableSet.measure_eq_iSup_isCompact` 及 `_of_ne_top` |
| 更一般的内正则实例 | `Measure/RegularityCompacts.lean` 的有限测度、第二可数完全可度量空间实例 |
| 紧性与可测性 | 紧积集经 `(x,y) ↦ t • x + (1-t) • y` 的连续像；`IsCompact.prod`、`IsCompact.image`、`IsCompact.measurableSet`，本地 `KLS/LogConcave.lean` 已使用同一表示 |
| 包含关系 | `Set.image2_subset`；`Set.smul_subset_smul` 等是相同 image2 单调性的特化；组合也可直接逐个存在量词传递包含关系 |
| 幂与上确界 | `ENNReal.orderIsoRpow t ht` 的 `map_iSup`，要求 `t > 0`；同样用于 `1-t` |
| 两个独立上确界的乘积 | `ENNReal.iSup_mul`、`ENNReal.mul_iSup`，不需把质量转成实数 |

临时探针实际检查了紧集像的紧性/可测性、内正则实例和上下确界运算；永久具名检查
`borell_innerRegular` 使用主定理的赋范空间假设，`borell_rpow_iSup` 和
`borell_mul_iSup` 保留最关键的序运算验证。`Fin 0` 与一般 `Fin n` 也有类型检查。
评估为 **available**；这只表示实现前提齐备。唯一主证明洞仍在 `LogConcave.borel_iff`。

Claude 建议先在模块内建立内测度单调性及可测集上与原测度相等，再处理两个方向：
紧集特化；紧集内部逼近后的两重上确界。保持原 `LogConcave` 的定义不动，避免引入
等价循环。空集或零质量由正指数的 ENNReal 零值处理，不加非空或正质量假设。

## 已实现的定义与障碍

- `KLS.Isotropic` 明确包含 `MemLp id 2`、向量积分为零及本地中心化
  `Covariance.operator = ContinuousLinearMap.id`。没有使用未中心化二阶矩算子。
  `zero_dimension_isotropic` 实际证明零维概率律满足该结构。
- `KLS.Isoperimetry.carrierMeasure` 通过已有可测 retraction 把概率律送到实际仿射支撑
  的 subtype，采用诱导距离。`boundaryContent` 使用 `Metric.thickening` 和 `𝓝[>] 0`；
  正半径时质量增量非负。结果、除法及逆均留在 ENNReal。
  `constant` 的零维分支检查仿射支撑方向维数，返回 `⊤`，`inverseScale` 返回零。
  已检查零维环境，以及环境为实直线而支撑为单点的 Dirac 律。
  没有 BV、密度 Cheeger、Poincare 比较、原点独立性或 Cheeger 能量认定。
- 原 Dirac examples 保留不动，库中新增 `dirac_raw_energy` 和
  `dirac_toLp_zero_eq_id`：前者打包 a.e. 相同与原始能量 `0`、`1`，后者实际打包
  两个 `MemLp` 证明与 `toLp` 类相等。二者加入 FoundationAxiomAudit 的标准公理守卫，
  不增加 ledger 节点。现有 examples 的基础设施哈希因此不需要迁移。

## Conditional-fiber：构造与六个证明洞

Mathlib 已有 `Measure.condKernel` 的联合可测 Markov kernel、`Measure.disintegrate`、
条件积分公式及条件 kernel 的 a.e. 唯一性。这里 `disintegrate` 是分解恒等式，
构造由 `condKernel` 给出。固定产品基空间使用 `Direction E × E`；
`coordinates (θ,x) = ((θ, x - ⟨x,θ⟩ θ), ⟨x,θ⟩)` 的联合推前律只析取一次。
从而不需要为每个方向分别选择可能不联合可测的条件版本。

`Admissible` 包含正维、μ 的二阶矩、ρ 的偶对称性及双线性形式写出的 frame 恒等式。
积分函数本身是总定义；Blueprint 的有效输入范围由该 predicate 描述。方向空间在零维
为空，没有构造零维球面概率律；具名零维检查表达 admissibility 不可能成立。

`GoodFiber` 显式检查 `z ⟂ θ`、标量坐标的 `MemLp 2` 和非零条件方差。
不满足时 `fiberEnergy` 返回零，避免在无限二阶矩纤维上借助全定义化实积分制造数值。
`energy` 取 ENNReal 积分；`form` 使用 Mathlib `Lp` 已选取的强可测代表元；
`domain` 是该扩展值函数的有限域。这些定义无 `sorry`。给出一个选定的函数表达式
尚不意味着原 Blueprint 声明的所有代表元和版本都已识别。

| 顺序 | 待证声明 | 具体义务 |
| --- | --- | --- |
| 1 | `lintegral_baseLaw` | 固定产品基测度积分等于对方向及投影律的迭代积分 |
| 2 | `ae_memLp_id` | 从 μ 的二阶矩推出条件标量坐标几乎处处属于 L² |
| 3 | `measurable_fiberEnergy` | 分支、条件方差和扩展除法组成的函数联合可测 |
| 4 | `energyWith_eq` | 任意满足同一分解恒等式的 Markov 版本给出同一积分 |
| 5 | `energy_congr_ae` | 两个 Borel L² 代表元 a.e. 相等时能量相同 |
| 6 | `form_toLp` | 选定 L² 代表元函数与原 Borel 测试函数公式相等 |

证明时还可在这些合同内部建立 a.e. 重构、正交基点支持及条件测试函数 L² 的辅助结果。
全部六条目前 `by sorry`；节点评估为 **missing**，具体缺口是这些本地适配证明，
没有声称 Mathlib 缺少析取理论。定义节点的可选 infrastructure 使用同一证据/版本
校验与调度逻辑；新增三个回归测试保护这一扩展和原 published 节点的强制字段要求。
没有附带证明闭形式、Markov 性、梯度比较或长路线结论。

## 密度表示只评估

tasks.json 把缺口分为代表元、局部正下界、各阶矩三项。已有
`LogConcave.intrinsic_absolutelyContinuous` 和 `intrinsic_frontier_support`，
小球下界与全局小球质量上界也在本地。Mathlib RN 工具提供可测扩展密度、a.e. 有限性
及 `withDensity` 恢复恒等式，`IntegrableExpMul` 提供指数可积性到矩可积性的工具。

仍需从现有数据构造处处有限、上半连续且对数凹的密度版本，建立内部紧集上的统一正下界，
以及从对数凹性推出尾部估计/指数范数可积性。`rnDeriv.toReal` 本身不提供这些性质。
本批未新建或证明任何完整密度表示定理，也未改动其数学分类或加入额外解析假设。

## 检查事实、golden 和后续认证

预检收据：`build/verification/20260906T181000.073185Z/report.json`，状态 **failed**。
预检源码快照 SHA256：`e51165ee9a812237e95b82c4220762ea678e072f855ede960a09774bca1ee595`。
这是写入本决定及当前指南更新之前的快照，不是交付快照。

该次实际完成：结构/ledger/Blueprint/atlas gate 通过；100 个 Python 测试通过；
默认 `lake build` 通过；statement snapshot 和原 golden 比较通过。
共收到 143 条公理报告，原十个 certificate 均只含 `propext`、`Classical.choice`、
`Quot.sound`。二十个具名 StatementChecks 及两条 Dirac 结果另外实际接受了标准公理审计。
最终接受被且仅被上述七个草稿的 `sorryAx` 拒绝；该次没有进入 kernel replay。
编译通过在这里表示声明和已写定义可编译，不是七条目标已证明。

原 statement golden 的 26 个声明和 221 个外部叶子保持一致；新定义不在该旧根闭包中。
没有更新 golden，也没有假称新增定义已纳入该快照。新增对象由 Blueprint 锚点、具名
typed checks 和相应公理守卫覆盖。今后若要扩展根闭包，应新建单独的 baseline 决定，
再运行 verification.md 的显式 update 命令。

完成本决定后应再次执行完整 `python3 research/verify.py`，随后 `atlas.py export` 和
`atlas.py ready`。最后一次生成收据记录自己的实际源码 SHA；不把它写回本决定以免失效。
验收器继续审计所有 Blueprint 锚点，包括未标 leanok 的草稿；没有放宽公理白名单或隐藏
草稿锚点。当前失败收据会让 ready 要求验证，而不会把完成定义等同于完成证明。

基线 ready 有 17 个 blocked，其中 14 个处于 Borell 等价的下游。当前 Borell 根因保留
`sorry` 仍不提供依赖证明，密度及后续路线继续阻塞；conditional-fiber 因六个合同未证
也不解除两个直接消费者的阻塞。已实现定义的检查状态与全仓验证状态要分开报告。

Claude 完成等价证明后：在指定 Solutions 文件提供唯一 certificate，加入
`check_blueprint.CERTIFICATES`，补标准公理守卫，同步 ledger 与 Blueprint，重新验证。
完成六个良定义性合同后才能给 conditional-fiber 整个节点 leanok。没有先冻结接口的要求。
本交接不做 commit/push、远端 CI、CL 或 Pages 部署；先交还可检查的本地草稿。

## 源文件 SHA256

下表记录本批实现/检查源文件；全部基础设施来源的逐文件哈希另见 tasks.json。

| Source | SHA256 |
| --- | --- |
| `formalization/FunctionalInequalities/KLS/LogConcaveBorel.lean` | `5660f390c133f093e7f913e3024bd60b9357338507c2e8f96abc34d3ce6e8044` |
| `formalization/FunctionalInequalities/KLS/Isotropic.lean` | `dd0d5ca09b40742ce0bc9f59b292a1d7903ce5f936fa654525164163534a3962` |
| `formalization/FunctionalInequalities/KLS/Isoperimetry.lean` | `db185cf4fe869347881fff739e0dd0808a6ad7dd8a160c28b5aa0b74bc4e4248` |
| `formalization/FunctionalInequalities/KLS/ConditionalFiber.lean` | `618996843d53d904ec7b34688fb2a3b608e2d7796b9253d5f582cbcfcedfd205` |
| `formalization/FunctionalInequalities/Poincare/Euclidean/RawEnergyObstruction.lean` | `9b70f06c372a3387a63798444714e1cc1f7929ea3de4927da9e51711c790e5c6` |
| `solutions/ThmCompactBorellLogconcavityEquivalence.lean` | `b6ee0bc34ada93951d9f636e8870944ca233399f7e49a5a644e8918ff2df84d8` |
| `solutions/StatementChecks.lean` | `27fd9cd6cb8ddf123cdff17f6aab76ebabe1b513f3160847ed230532a3c0a59f` |
| `solutions/FoundationAxiomAudit.lean` | `178e51727ecf18ffe589727c46cd84998bba4fca02bdf2c0754cdf55bfb90841` |
