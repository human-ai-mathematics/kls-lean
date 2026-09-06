# 加权光滑逼近：statement 与 Claude 证明交接

日期：2026-09-06。用户要求“推进第一个数学任务，只写 statement，留 sorry，我让 Claude
去解决 sorry”。本批只准备 `lem:covariance-test-core-density` 的四条候选陈述；没有编写
证明或向其他 Agent 发送任务。节点为 **`drafted / checked_by: null`**，四个证明体均为
`by sorry`。这不是证明验收，也不要求先冻结接口。

## 阅读入口与来源

1. 先读仓库 [HANDOFF](../../HANDOFF.md)，尤其是权威层级、接口演进与追加式记录规则。
2. 数学来源是本地 [Blueprint Appendix A](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex)
   的 `lem:covariance-test-core-density` 及其紧随的证明。它是已有的本地分析论证，
   `tasks.json` 仍将数学状态标为 `local_argument`，没有将其冒充某篇已核对论文的定理。
3. 主合同和四个证明洞位于
   [LipschitzApproximation.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean)。
4. 默认构建入口
   [LemCovarianceTestCoreDensity.lean](../../solutions/LemCovarianceTestCoreDensity.lean)
   只导入该模块并 `#check` 四条完整签名，没有 `certificate` 包装。

声明均位于 `FunctionalInequalities.Energy.Euclidean.LipschitzApproximation` 命名空间。
先读主结果 `exists_smooth_weighted_L2_approximation`，证明时按以下顺序推进。

## 四个证明义务

| 顺序 | 声明 | 输入与输出 | 建议路线 |
| --- | --- | --- | --- |
| 1 | `exists_compactSupport_weighted_L2_approximation` | 局部 Lipschitz 的 g，g 与 B∇g 属于 L²(ν)；得到紧支撑、全局 Lipschitz 的序列，函数与加权梯度均在 L² 中收敛 | 光滑截断 χ_R g；估计截断梯度误差与 L² 尾项 |
| 2 | `exists_smooth_compactSupport_L2_approximation` | 紧支撑且 Lipschitz 常数为 K 的 g；得到 C∞ 紧支撑序列，保持 K，函数与完整梯度均在 L² 中收敛 | 非负归一化紧支撑卷积核、梯度的几乎处处收敛、有界控制收敛 |
| 3 | `exists_smooth_weighted_L2_approximation` | 与步骤 1 相同的输入；得到 C∞ 紧支撑序列，同时逼近 g 与 B∇g | 用 B 的连续性把步骤 2 转为加权估计，再与步骤 1 作对角选取 |
| 4 | `exists_smooth_bounded_L1_approximation` | 全局 K-Lipschitz 且 a ≤ g ≤ b；得到同一区间、同一 K 的 C∞ 序列，函数与梯度均在 L¹ 中收敛 | 不截断，直接作非负归一化卷积；不要求紧支撑 |

步骤 2、4 同时将原函数及原梯度的 `MemLp` 作为结论；它们应从全局 Lipschitz 性、
有界性与概率测度推出。所有步骤都明确要求逼近项的相应 `MemLp`。
收敛用差值的 `eLpNorm` 趋于零表达，不通过可能被全定义化为零的实积分表示。

## 数学范围与用法

空间 E 是任意有限维完备实内积空间，带 Borel 可测结构及第二可数拓扑；ν 是概率律，
m 是满足 `Measure.IsAddHaarMeasure m` 的参考测度，并假设 ν ≪ m。这里采用任意正归一化
的 Lebesgue/Haar 参考测度，避免把声明局限于坐标实现。卷积核需相对于实际 m 归一化。
零维也在量化范围内，不增加正维前提。

主 L² 陈述只要求 B∇g 平方可积。B 是任意连续线性自映射，允许零算子和有核算子；
有限维中这覆盖数学来源中的任意线性映射。不能为了套用已有光滑测试接口而给原函数
增加完整梯度的 L² 假设，也不能要求 B 可逆或正定。ν 不要求对数凹、二阶矩有限、
密度有正下界，证明不依赖平移前后的密度比较。

例如，B 取恒等映射得到通常的函数及梯度 L² 逼近；B 取正交投影保留退化权重情形。
步骤 4 取 a=0、b=1 得到 Blueprint 的保值域版本。任意有界全局 Lipschitz 函数都可
选择一个包含其值域的闭区间。保留同一个 K 和任意 [a,b] 是对卷积步骤的明确局部规格，
不是给主结论附加更强的输入假设。

`gradient` 沿用 Mathlib 的标准 Hilbert 梯度，不可微处按其定义为零。局部 Lipschitz
函数的几乎处处可微性，以及其与卷积/弱导数的对应，仍是需要证明的内容。
`open scoped ContDiff` 下的 `ContDiff ℝ ∞` 表示普通 C∞；不要换成解析性的
`ContDiff ℝ ⊤`。本批没有定义新的梯度、能量或测试类。

## Mathlib 起点与尚缺的拼接

当前工具链为 Lean/Mathlib v4.33.0，Mathlib commit 为
`db584cd6d46c92f209a44c0f1c829460d327499d`。以下名字已在本地源码中核对，供定位使用；
它们不是四条目标已经有现成证明的声明：

- `Mathlib/Analysis/Calculus/Rademacher.lean`：`LipschitzWith.ae_differentiableAt`，
  以及 `integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul` 系列。
- `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`：
  `ContDiffBump.convolution_tendsto_right_of_continuous` 与
  `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`。
- `Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`：
  `HasCompactSupport.hasFDerivAt_convolution_right` 的可微性结论有其自身正则性假设；
  单独调用它不能替代把导数转移到仅 Lipschitz 的函数上的分析论证。
- `Mathlib/Analysis/Calculus/BumpFunction/` 提供光滑截断与归一化核的基础设施；
  `SmoothApprox.lean` 中的函数值逼近本身不提供所需的梯度逼近。

关键工作包括：截断函数的全局 Lipschitz 控制、可测性与 a.e. 梯度恒等式、
Lipschitz 平滑化的梯度收敛、通过 ν ≪ m 转移零测集，以及带权 L²/L¹ 的控制收敛。
这不是对整个 Mathlib 的“缺失定理”穷举；可继续寻找更直接的现有 API。
`tasks.json` 的基础设施仍为 `missing`，仅追加了本次交接位置的说明。

## 给 Claude 的任务边界

完成上述四个定理体，可添加有明确用途的证明辅助引理。不要把“存在所需逼近序列”
改为一个输入假设，不要削弱主陈述以换取编译成功。若实际发现陈述需要改动，应记录
数学原因、变化后的输入输出及原目标是否仍被覆盖，并同步 ledger；接口不要求永久冻结。

本批不处理下一个 `lem:covariance-core-closure`，也不证明局部斜率与梯度的对应、
文献 Poincaré 常数比较、Dirichlet 性质或 KLS。本模块未加入已认证库的聚合导入，
已有六个证书的声明与导入未变。Blueprint 标签、路线状态、数学分类与 golden 未改动。

证明完成后，应编译相关模块及默认目标，检查新增声明与证书的传递公理、移除本批
四个 `sorry`，再按实际覆盖范围建立节点证书和追加验收记录。草稿入口通过 ledger
和默认 Lake target 导航；当前没有添加草稿的 Blueprint `\lean{}` 锚点。验证器会审计
所有这些锚点，不能把草稿声明链接过去后忽略其 `sorryAx`，也不能为本任务放宽检查器。

## 本地检查记录

Git HEAD：`70ca1c19c4d207a31716c2e589c0b096521a5490`。以下检查针对已有未提交修改加上
本批 statement/登记/指南修改的工作树，记录文件自身写入前的 source SHA256 为
`56a786c6abb35d83567e06c801005c59afb011b6e0eb8e23f44ee170101dd965`。
逐文件哈希保存在 `build/draft-statements/20260906-weighted-approximation/checked-source.json`。

| 检查 | 实际结果 |
| --- | --- |
| `lake build solutions.LemCovarianceTestCoreDensity`（在 formalization 下） | 最终通过，2889 jobs；四条完整签名保留有限维、Haar 与绝对连续等预期参数 |
| `python3 research/check_ledger.py` | 通过，7 个 ledger 节点，其中 6 proved、1 drafted |
| `python3 research/check_blueprint.py` | 通过，86 标签、4 条活动路线 |
| `python3 research/atlas.py check` | 通过，73 个数学节点、6 个证书，无环 |
| `python3 -m unittest discover -s research/tests -p 'test_*.py'` | 97 项通过 |
| `lake build`（在 formalization 下） | 通过，3247 jobs；本批恰好四条 `declaration uses sorry` 警告 |
| 对四条声明执行 `#print axioms` | 全部包含 `sorryAx`，明确为未证明 |
| `python3 research/statement_snapshot.py check` | 通过，公开陈述及定义闭包与原 golden 一致 |

日志位于 `build/draft-statements/20260906-weighted-approximation/`，为忽略的本地输出。
最初的模块编译暴露了 Haar 类命名空间及 C∞ notation scope 问题；已修正，再运行上述
目标及默认构建通过。编译通过在本批只表示陈述 elaboration 成功。

本次没有运行完整 `verify.py`、全模块 leanchecker 重放、隔离重建或远端 CI。
上一轮完整验证收据 `build/verification/20260906T115425.436083Z/report.json` 的源码快照
先于本次修改，不能用于认证当前工作树。没有 commit/push，也没有更新先前暂存内容。
历史 decisions/explorations 保持原样。
