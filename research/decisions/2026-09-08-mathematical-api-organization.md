# 数学对象命名空间与参数组织迁移

基线：`main`，`19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`，开始时工作区干净。
用户批准直接实施；交付本地改动，不 commit 或 push。既有 decisions/explorations 保持原记录。

## 迁移前清单与证据

完整声明映射见 [机器可读映射](../api-migration/2026-09-08-name-map.json)。
`build/api-refactor/baseline/` 保存全部 233 个跟踪文件及 SHA256；
`baseline-build.log` 记录原默认构建通过（3349 jobs），`baseline-golden.log`
确认原有 26 个声明的 golden 与该基线一致。`before-raw.json` 保存从 882 个公共声明入口
展开的 1088 个本地声明类型及定义闭包；定理证明由编译、公理审计和最终 kernel 重放验证。
原 StatementSnapshot 的 pretty printer 在长内在类型上截断，所以另存不截断的 `Expr` 表示；
逐声明无损压缩文件位于 `baseline-expressions/`。不能把打印截断当成等价证据。

## 对象与承载空间

- `Poincare.SmoothTest`：全局光滑、L² 且梯度平方可积的测试常数。
- `Energy.SmoothGradient`：普通梯度预能量与松弛；`Intrinsic.energy` 通过内在坐标拉回原 L² 空间。
- `Energy.CovarianceGradient`：协方差加权测试 `Test`、`Test.energy`、`preEnergy`、`relaxation`；
  `Intrinsic.energy` 留在内在律的 L² 空间。对应常数在 `Poincare.CovarianceGradient.Intrinsic`。
- `Energy.WeightedGradient`：外部选择 `B` 的 `B ∇`、`IsTest`、`operator` 和闭包，不假定 B 是协方差因子。
- `Energy.LocalSlope`：点态局部斜率和平方积分；`Poincare.LocalSlope.Holds` 在给定坐标律上，
  `Poincare.LocalSlope.Intrinsic.constant` 先取 intrinsicMeasure。
- 概率推前在 `Probability`；L² 的 `Translation`、`LinearIsometry`、`ContinuousLinearEquiv`
  分别提供 `pullback`、`pullbackInv` 和 `pullbackEquiv`。复用 Mathlib 的
  `ProbabilityMeasure.map` 与 `Lp.compMeasurePreservingₗᵢ`，不建立另一套一般运输抽象。

## 参数调整清单

第一阶段仅替换声明名称、命名空间与引用；构造所选择的测度、算子、参考 Haar 测度保持显式。
`WeightedGradient.IsTest.memLp` 支持 `hf.memLp`，两种测试支持 `f.energy`、`f.toL2`。
对数凹结论保留 `hμ.定理名` 的性质证明调用。随后对 section 作用域及冗余假设的任何调整，
必须独立列出并对照实际 elaborated 参数，不能计入纯重命名比较。

## 数学契约

协方差因子只断言 `∃ B, ∀ v, ⟪Σ v,v⟫ = ‖B v‖²`，故名为
`Covariance.exists_inner_eq_norm_sq`；不增加平方、自伴、正性或唯一性结论。
直接的环境律平移不变性获得 `constant_translateLaw`，内在表达式比较明确标出 intrinsicMeasure。
普通梯度与协方差加权能量、环境空间与内在空间、闭二次形式与 Dirichlet 性质、
零维与退化支撑、无限最优常数的区别保持。稳定节点 ID、证书入口、来源标签保持。


## 已审查的最终接口变化

完整的实际参数顺序、显隐及实例清单在
[parameters.json](../api-migration/2026-09-08-parameters.json)。比较来自迁移前完整 `Expr`
和迁移后 `forallTelescope` 的实际声明；并非从 `variable` 文本推测。
882 个库内源码声明入口合并为 881 个，其中 305 个入口的参数有变化：

- 214 个仅删除冗余实例；68 个同时删除实例并调整参数排列。
- 22 个仅调整排列。显式数学输入（概率律、权重、参考测度及证明）的用途不变。
- 1 个是实数二阶矩引理与一般版本的合并：
  `ConditionalFiber.memLp_id_two_iff` 和 `memLp_id_two_iff'` 统一为
  `Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top`。
  实数特化获得任意宇宙的 Borel 范数空间载体；一般版本删去不需要的 Hilbert/有限维条件。

除该实数特化外，没有改变公共声明的宇宙参数个数，也没有改变非实例参数的显隐。
`WeightedGradient.IsTest.smul` 和 `IsTest.weightedGradient_smul_ae` 的两个隐式参数
从 `… m g …` 调整为 `… g m …`；完整参数序列（含实例的排列）见清单。
从 `LogConcave`、绝对连续性、有限矩、可积性推论的证明参数都保留。
三个证书入口（内在绝对连续性、Borell 密度、闭协方差形式）也删除了冗余的
`[CompleteSpace E]`；有限维条件仍在，原带完备性假设的使用场景仍然覆盖。
其余证书入口名称及全部 guards 保留。

新的分层模块包括 `Probability.Transport`、`Probability.IntrinsicTranslation`、
`Probability.LocalDomination`、`Probability.Moments`、`L2.Transport`、
`Energy.CovarianceGradient.IntrinsicTranslation` 和 `Poincare.CovarianceGradient.Transport`。
协方差范数分解（包括内在版本）属于 `Probability.CovarianceFactorization`。
完整模块移动与拆分分别见 [module-map.json](../api-migration/2026-09-08-module-map.json)
和 [module-splits.json](../api-migration/2026-09-08-module-splits.json)。旧模块没有转发包装。

原有 22 处 `unusedSectionVars` 关闭项全部移除；最终默认构建没有这类警告。
WeightedGradient 按微分、可测测试、Haar/Rademacher 分组；局部测度支配独立；
AffineSupport 按几何、闭性、满测度和内在坐标分组；LipschitzApproximation
把核的纯微分性质与 Haar 归一化分开。个别相邻引理假设较弱时保留局部 `omit`，
检查器始终开启。没有打包环境假设的新结构或 typeclass。

## 语义比较结果

[审计总览](../api-migration/2026-09-08-review.json) 与逐声明记录提供以下证据：

1. **纯命名阶段**：1088 个本地声明的类型与定义闭包，经明确名称映射和绑定变量
   alpha 重命名后全部相同；没有遗漏、新增或未解释差异。
   独立的阶段映射保留在 `2026-09-08-renaming-stage-name-map.json`，避免用最终泛化映射
   重新解释这一阶段。
2. **最终源码**：189 个定义/结构的主体，经 `.ilean` 解析引用映射后全部相同。
   882 个源码签名中，876 个相同；其余 6 个逐项审查：实数二阶矩合并、
   内在范数分解把 section 中的显式 `μ` 写进定理头、一个完备性及三个有限维实例
   从 section 移入对应定理头。没有改动公式、测试字段、能量归一化或松弛构造。
3. **最终 elaboration**：保存 1085 个当前本地声明类型及定义闭包。
   严格 `Expr` 比较中 708 个仍相同，375 个变化分别由实际参数调整（335）、
   依赖这些接口的调用调整（36）、编译器生成证明重编号（4）解释。
   另有 5 个旧生成证明辅助名不再出现、3 个新生成辅助名出现；这些都是 `._proof_N`
   编译产物，不是公共数学入口的遗漏。二阶矩两个入口合并为一个单独记录。
   不能把这些接口泛化称为整库“仅重命名”。
4. **Statement golden**：基线 26 个声明先与原 checkout 核对通过，最终仍为 26 个；
   roots、外部信任边界、toolchain 和 Lake 依赖锁定不变（roots 仅按名称映射）。
   模块归属和同类型生成证明编号先对齐，剩余 10 个差异来自内在坐标辅助定义删除
   冗余实例及其调用；`KLS.Conjecture` 的量词与源码主体未变。
   详见 [golden-review.json](../api-migration/2026-09-08-golden-review.json)。

原始 `Expr` JSON 与逐声明无损压缩记录在 `build/api-refactor/`，包括
`baseline-expressions.json`、`renamed-raw.json` 和 `final-expressions.json`。
声明比较工具用于检查，不能代替 Lean 内核验证；定理证明体由完整构建、公理审计和
最终 kernel 重放负责。

基础设施原有 134 个来源哈希已核对（82 个仓库源条目、52 个外部依赖条目），没有基线
不一致。根据实际声明的模块归属扩展拆分后的来源清单，再刷新 94 个条目；
不是先重算哈希再跳过差异审查。71 份既有 decisions/explorations 逐字节保持不变。

## 验收与最终收据

已完成的预验收：默认 `lake build` 通过（3359 jobs）；Python 测试 100 项全部通过；
405 个旧公共名的 `#check_failure` 检查全部通过；Blueprint 结构检查为 87 个标签、
4 条 active routes、0 错误，PDF/Web/checkdecls 均通过。37 页 PDF 已检查全页缩略图，
并放大检查更新的前端、比较标题和 conditional-fiber 认证边界页面。
默认构建新增 `examples.ApiOrganization`，覆盖 `f.energy`、`f.toL2`、`hf.memLp`、
`hμ.定理名`、任意有限维载体、零维、零权重和运输方向；现有退化支撑、无限常数
与全部证书示例继续构建。

本记录审查并批准本轮 golden 与基础设施哈希更新。最终从根目录运行
`python3 research/verify.py`；其不可变运行目录中的 `report.json` 是最终构建、
声明/传递公理审计及全部当前模块 kernel 重放的验收依据。
[`build/verification/latest.json`](../../build/verification/latest.json) 指向该最新尝试。
本记录在最终验证前定稿；收据必须与包含本记录及全部控制文件的最终源码快照一致。
不以 `git diff --check` 代替任何语义检查。

有意保留稳定 ledger/Blueprint ID、证书入口中的历史拼写、Borel/Borell、L1/L2、
weighted、ae、紧支撑和边界限定词。Blueprint 的 `C_P^can` 等既有数学记号仍用作
对应对象的简写；公共 Lean API 以数学对象和承载空间命名。
此次交付仅为本地工作区，不 commit、push 或发布网站；没有新增数学认证状态。
