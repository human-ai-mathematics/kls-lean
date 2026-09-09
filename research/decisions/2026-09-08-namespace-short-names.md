# 声明短名不重复命名空间

用户在上一轮公共 API 迁移后明确要求：命名空间已经表达的内容，不再放进声明短名。
本次在已验证的本地工作区上继续修改；基线是
`271f002b9a9a9d762d39dc268b643e7627818e65d99ca6a41dedf5d6b76810b6`，
对应 `build/verification/20260908T115953.150706Z/report.json`。
分支仍为 `main`，HEAD 仍为 `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`。
没有从 Git HEAD 恢复源码，也没有覆盖上一轮未提交的工作。

## 命名规则与完整范围

迁移 32 个公共声明；[完整映射](../api-migration/2026-09-08-short-name-map.json)
记录本轮开始时的名称到新名称。上一轮的映射与审计保持历史原样，两份映射依次应用。
命名空间和模块路径不变，也没有旧名兼容别名或包装。

| 命名空间 | 旧短名 | 新短名 |
| --- | --- | --- |
| `Covariance` | `covarianceBilin_intrinsic` | `bilin_intrinsic` |
| `Energy.WeightedGradient.IsTest` | `memLp_weightedGradient` | `memLp_apply` |
| 同上 | `weightedGradient_add_ae`、`weightedGradient_smul_ae` | `apply_add_ae`、`apply_smul_ae` |
| `Energy.LocalSlope` | `slope` 及四个 `slope_*` 引理 | `apply` 及 `apply_*` |
| `Energy.Euclidean.LipschitzApproximation` | 四个 `exists_*_approximation` | 对应的 `exists_*` |
| `KLS.ConditionalFiber` | `OrthogonalFiniteNonzeroVarianceFiber` | `Nondegenerate` |
| 同上 | `fiberEnergy` 及三个相关引理 | `energyAt` 及相应引理 |
| 同上 | `ae_fiber_congr` | `ae_restrict_congr` |
| `Poincare.SmoothTest` | `linearTest` 及七个相关引理 | `linear` 及相应引理 |
| `ProductVariance` | `integrable_variance_left/right` | `integrable_left/right` |
| 同上 | `variance_decomposition`、`variance_integral_le`、`variance_le` | `decomposition`、`integral_le`、`le` |

`Nondegenerate` 的三个条件仍然是正交基点、有限二阶矩、非零方差；文档明确说明全部
条件，不把字段枚举拼进名称。`energyAt κ b f` 在一个基点处计算，`energy μ ρ f`
仍对基点律积分。两者没有合并。`LocalSlope.apply` 仍是原来的点态局部斜率。

`f.energy`、`f.toL2`、`hf.memLp`、`hμ.定理名` 保持可用，新增 typed applications
验证 `hf.memLp_apply` 和 `LocalSlope.apply_const`。普通梯度、加权梯度、协方差梯度，
环境与内在承载空间，以及常数比较另一侧的数学对象仍然区分。
`WeightedGradient` 下关于普通 `gradient` 的辅助引理保留 `gradient`；
`ContinuousLinearEquiv.pullbackEquiv` 中两个等价分别作用于底层空间与 L² 空间。
这些不是同一对象的重复前缀。没有机械删除 L1/L2、weighted、ae、紧支撑或边界条件。

## 基线、语义与证据

开始时逐文件核对当前源码快照与上一份通过的收据一致，再保存
`build/api-shortnames/baseline/`、源码哈希及原 `.ilean` 声明/引用位置。
原始 elaborated 类型与定义闭包沿用该已验证源码的
`build/api-refactor/final-expressions.json` 及同名目录内的无损压缩记录。
本次编辑依据解析后的引用和 UTF-16 源码位置，不把重载名称或普通英文单词全局替换。

本次不调整 section、参数排列、显隐、实例假设或宇宙，也没有接口泛化。
源码比较确认 881 个公共声明签名、189 个定义/结构主体，以及包含证明在内的
885 个具名声明主体，在名称映射和格式归一化后全部一致，没有遗漏或未解释差异。
1085 个本地声明的原始 Lean Expr 类型与定义闭包，经精确名称映射和绑定变量 alpha
归一化后全部一致。模块、宇宙、依赖、参数排列与显隐不变；32 个重命名入口的匿名
实例参数含有不同的编译器 hygiene 哈希，逐项核对后确认只有该哈希变化，模块及局部
hygiene 序号仍相同，显式参数名没有变化。原始比较与这些元数据差异都保留在
[本轮审计](../api-migration/2026-09-08-short-name-review.json)。
声明类型和定义闭包比较不替代定理证明的内核验证。

现有 statement golden 仍覆盖 26 个本地声明、221 个外部依赖叶子。
按本轮名称映射后完全一致；没有调整模块归属或生成证明编号，也没有更新数学公式。
toolchain、依赖锁和外部信任边界均不变。
本记录批准将已经比较通过的候选写入新 golden，不能通过重写旧记录绕过审查。

先核对原有基础设施来源哈希，再依据源码比较刷新 29 个受影响条目，涉及 15 个源码文件；
路径、基础设施评价、ledger 生命周期、证书身份与数学认证状态不变。
见 [来源哈希审查](../api-migration/2026-09-08-short-name-evidence.json)。
此前的 decisions、explorations 和上一轮迁移证据共 86 份文件逐字节保持不变。

## 验收边界

预验收默认构建通过（3359 jobs）；32 个旧名全部通过 `#check_failure`，32 个新名
全部解析。原有 guards、证书、一般有限维和零维、退化承载空间及运输应用继续构建。
没有新增 `sorry`、`axiom`、兼容包装或 linter 关闭项。

Blueprint PDF、Web、checkdecls 通过；结构检查保持 87 个标签、4 条活动路线、0 错误。
37 页 PDF 已检查全页缩略图，并放大复核局部斜率与条件纤维页面。
当前指南、下游引用、公理消息、Blueprint 锚点和 statement roots 同步新名。

本记录与审计定稿后，从仓库根目录运行 `python3 research/verify.py`，保留全部测试、
statement snapshot、声明/传递公理审计和所有本地模块 kernel 重放。
最终结果以 `build/verification/<UTC timestamp>/report.json` 为准；
`build/verification/latest.json` 保存最新尝试。最终收据必须对应包含本记录的实际源码。
`git diff --check` 仅检查格式。本次交付本地工作区，不 commit、push 或发布。
