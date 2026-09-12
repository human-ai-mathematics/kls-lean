# 2026-09-12 — 当前状态审计、文档同步与 WIP 保留

Owner 在本轮 statement/数学语义审计后明确要求：现有 `sorry` 继续保留，先更新文档，再提交。
此次提交整理已经核验的当前成果与文档；本轮不填证明、不改变 Lean statement、定义或证明体，
不把 WIP 登记为已证节点，不推送远端。既有决定记录保留为各自日期的历史快照。

## 当前可认证范围

`research/a-series/ledger.yaml` 有 24 个 `proved / checked_by: lean` 节点。核心 KLS 定义的
量词是先选统一有限常数，再覆盖所有维数和测度；协方差使用中心化的 `covarianceBilin`。
局部斜率测试域保留 L² 与有限能量条件，零能量和零维情形没有被排除。

新增成果的使用边界：

- 一维对数凹证书给出 `C_P^lit(ν) ≤ 4 Var_ν(id)`，包含 Dirac。证书只证明系数 4 的上界，
  未另外形式化“系数不可改进”；不表示每个一维律都有等号，也不证明一般高维 KLS。
- 条件纤维形式已闭且 Markov，纤维对数凹性与一维界给出 `D(f) ≤ 4 ∫‖∇f‖²`。
  要得到 `C_P^lit(μ) ≤ 4 C`，仍需输入所有有限形式域测试上的 `Var(f) ≤ C D(f)`。
  对所有维数/各向同性对数凹律，存在一个独立于测试函数的框架及统一有限 C，仍是开放问题。
- 内禀律 Haar 绝对连续时，光滑梯度松弛等于局部斜率松弛，因此 `E^can = 2 Ch`；
  所有对数凹律都满足这个内禀绝对连续条件。此范围已登记为
  `cor:absolutely-continuous-relaxation-two-cheeger`。
  一般奇异律上的无条件比较、渐近 Lipschitz convention 的等价以及等周 Cheeger–Buser
  比较是不同问题，不能由这个证书一并宣告完成。

## 保留的证明工作

| 文件 | 直接 `sorry` 数 | 当前边界 |
| --- | ---: | --- |
| `KLS/WIP/RelativePerimeter.lean` | 5 | Hausdorff 归一化、边界局部有限性待接回；Gauss–Green 后的卷积与恢复序列仍待完成 |
| `KLS/WIP/CheegerInfimum.lean` | 9 | Sard、coarea、Minkowski coarea、光滑逼近接入和下游下确界比较 |
| `KLS/WIP/AnalyticPrerequisites.lean` | 5 | coarea 可测性与公式、Sard、两种 Gauss–Green statement |
| `Energy/WIP/Cheeger.lean` | 5 | 两个主要奇异律比较及三个派生目标 |
| 合计 | 24 | 全部保留；直接 hole 数不等于独立数学难题数 |

这些文件均不被正式聚合入口或 24 个证书导入。`AnalyticPrerequisites` 原有 17 条义务，
其中 12 个证明体已经填写：Prékopa–Leindler、两种 Brunn–Minkowski、等周直径、Hausdorff
比较与归一化、局部 Lipschitz 图、正则水平集局部有限性、外法向一致性及单位长度共 10 项
只有标准公理；另外两个已填证明体 `ae_forall_fderiv_ne_zero` 与
`gradient_mollifiedIndicator_eq` 仍通过 Sard 或 Gauss–Green 传递依赖 `sorryAx`。
“证明体已填”和“传递依赖无 sorry”必须分别表述。

几何输入已经存在于 companion 文件，不应继续记为“17 条仅陈述”。但该文件目前导入
`RelativePerimeter`，不能反向 import 接回这些引理而形成环。后续可按依赖拆分基础定义和
通用几何定理；本轮不进行拆分，也不因此消除任何 placeholder。

`CheegerInfimum.exists_smooth_approximation_lipschitz` 的输入实际上已经足够：正式库的
`Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1` 同时给出函数与梯度
的 L¹ 收敛以及 `[0,1]` 范围和 Lipschitz 性。把梯度序列实现到 `Lp V 1 ν`，用
`Lp.tendsto_Lp_iff_tendsto_eLpNorm''` 得到收敛，再用 `Filter.Tendsto.enorm`、
`Lp.enorm_toLp` 和 `eLpNorm_one_eq_lintegral_enorm` 得到所需的梯度范数积分收敛。
本地独立审计客户端已在 warnings-as-errors 下证明该蕴含，只依赖标准三公理，未导入 WIP。
源码中的 `sorry` 依 owner 指示保留，状态记录为待接入。

两条历史 distance-cutoff 缺陷已经在此前工作中修正：非空前提阻止空集反例，indicator
收敛另含可测性及闭包不增质量前提。本轮复核它们的当前证明没有 `sorryAx`，不再修改签名。

## 核验边界

文档更新前的审计回执为 `build/verification/20260912T104945.225719Z/report.json`：
103 项 Python 测试、默认 Lake 构建、26 个本地依赖声明的 KLS statement golden、
349 个选定声明的传递公理检查、149 个本地模块的内核回放均通过。另一次环境级检查覆盖
正式聚合入口和全部证书导入的 2,042 个本地声明（其中 1,631 个 theorem，含生成辅助项），
没有非标准公理、unsafe 或 partial 声明。人工审查覆盖 24 个证书类型、关键定义与 24 个
显式 WIP hole 的陈述；未逐行人工检查所有辅助证明。

四个 WIP 文件在隔离的完整本地模块视图中重新 elaboration：普通模式退出 0，恰有上述
24 条 `declaration uses sorry` 警告；`-DwarningAsError=true` 将它们升级为 error，退出 1，
没有其他诊断。因此历史记录中“warningAsError 无警告通过”的文字不能按字面作为证据。
内核回放本身可接受依赖 `sorryAx` 的项；只有结合传递公理检查才能确认无 hole 的范围。

所有证据都信任固定版本的第三方编译依赖，不代表独立从零重建 Mathlib、远端 CI 或
Blueprint PDF/网页排版通过。文档和任务元数据更新后，应重跑 `python3 research/verify.py`
取得最终工作区的一致快照回执。审计脚本、日志和生成缓存留在忽略的 `build/`，不随提交打包。

审计时本地 HEAD 为 `5e5c704`，实时 `origin/main` 为 `12f828f`；二者分别独有 2 和 3 个
提交。本轮只授权本地提交，不合并或改写远端历史。KLS 的维数无关界仍然开放，不能用
ledger 的 24/24 已证比例表示整个 KLS 计划的完成度。
