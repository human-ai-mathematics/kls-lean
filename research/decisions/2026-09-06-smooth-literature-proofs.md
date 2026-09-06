# 光滑测试与文献常数：八条证明及本地认证

日期：2026-09-06。用户在八条 statement 交接之后明确要求“你直接连 sorry 一起解决了吧”。
本批完成全部八条证明，并将 `thm:smooth-lipschitz-constant-equivalence` 登记为
`proved / checked_by: lean`。本地 HEAD 为 `70ca1c19c4d207a31716c2e589c0b096521a5490`，
工作树含此前未提交的工作。本次未 commit/push，未改写历史 decisions/explorations，
也未改变原有暂存区内容。

## 来源和阅读顺序

1. [原 statement 记录](2026-09-06-smooth-literature-statements.md)：原八条目标、坐标约定及来源。
2. [局部斜率与梯度](../../formalization/FunctionalInequalities/KLS/LocalSlopeGradient.lean)：
   点态恒等式、a.e. 恒等式、扩展能量恒等式和有限能量测试域。
3. [常数比较](../../formalization/FunctionalInequalities/Poincare/Euclidean/LiteratureComparison.lean)：
   有限常数等价、坐标下确界、环境/内禀/文献常数链及 selected 常数推论。
4. [汇总证书](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean)：逐项全称量化的
   八项合取；证书与八条可复用声明各有一个默认构建公理 guard。

数学来源仍是本地 Blueprint 的书面论证和原有定义。证明复用已认证的加权光滑逼近、
内禀限制/法向常值延拓、L² 方差连续性及 legacy/relaxed 比较，不引入新的数学假设。

## 证明内容和范围复核

- 点态斜率：由 Frechet 导数的余项给出上界，由局部差商界给出导数算子范数下界；
  再用 Hilbert 梯度范数恒等式。证明不选择单位向量，因此包含零空间和无限维空间。
- a.e. 与测试域：Rademacher 加绝对连续转移零测集，随后用 lintegral 的 a.e. 不变性及
  梯度可测性识别能量和 L² 条件。扩展能量等式允许无穷，不使用 totalized 实积分冒充有限性。
- 有限常数：取已认证逼近定理的 B 为恒等映射，得到函数与梯度的 L² 收敛；方差和梯度
  平方范数积分连续，把同一个 C 的光滑测试界传到文献测试域。反向由光滑性推出局部
  Lipschitz。没有额外假设待证的能量等式或收敛结论。
- 最优值：直接比较两个有限有效常数集合的扩展下确界，允许 C=0、空集合和无穷最优值，
  不要求下确界取到。坐标下确界显式写出，避免对已经内禀化的测度重复取内禀坐标。
- 坐标比较：限制不增能量，法向常值延拓保持能量，测度保持重构保方差。最后组合既有
  selected/legacy 等式。只有内禀测度需要对其方向空间上的 Haar 测度绝对连续；环境
  测度可以奇异。零维仿射支撑保留，没有加入二阶矩、正密度下界或 raw/core agreement。

公开签名有两处轻微推广：`localSlope_ae_eq_norm_gradient` 和
`literatureEnergy_eq_lintegral_gradient` 省去多余的 `SecondCountableTopology E` 实例参数。
有限维实赋范空间本身可提供该性质；原有显式数学假设与结论均保留，原目标仍被覆盖。
其余六条保持原数学签名。证书分别量化各分量，未为了打包而给点态定理增加有限维或
绝对连续前提。私有辅助引理不增加平行的常数定义或兼容别名。

这仍不证明一般对数凹测度的内禀绝对连续性。`thm:borell-logconcave-density` 以及
不显式假设绝对连续的 `thm:selected-literature-constant-equivalence` 保持未认证；
Cheeger 能量识别、Dirichlet 性质、长路线和 KLS 也未因此得到证明。

## 登记和保护范围

证书映射沿用原 Blueprint 节点，加入对应 statement/proof 的 `leanok`，没有新增图节点。
ledger 现有八个已证明节点；原七个节点对象逐项不变。`tasks.json` 的数学分类全部不变，
仅将本节点的已实现适配评估为 `available`，清空已解决的基础设施缺口并更新证明源哈希。
路线状态、KLS Definitions/Statement、golden 和历史记录均保持原样。当前指南同步认证状态；
`StatementChecks.lean` 只更新已过时的说明文字，未加入 Gaussian 专门化证明或占位。

## 已核实的预检与最终验证边界

本记录写入前的源码快照 SHA256 为
`f129aab7e1ef351df40f990b17d9cee977dc234be388c4375ac55eb1d50f967d`，HEAD 如上。
该阶段 ledger、Blueprint 和 atlas 结构检查通过：8 个证书、73 个数学节点、86 个导航
标签、4 条活动路线，无依赖环；97 项 Python 单元测试通过。
`lake build solutions.ThmSmoothLipschitzConstantEquivalence` 通过，3094 jobs，无警告。
八条声明及汇总证书的传递公理均恰为 `propext`、`Classical.choice`、`Quot.sound`；
新证明模块和证书本地导入闭包的逃逸标记检查通过。
预检日志位于 `build/smooth-literature-proofs/certificate-preflight.log`、
`build/smooth-literature-proofs/structural-checks.log` 和 `build/smooth-literature-proofs/python-tests.log`。

写完本记录后运行 `python3 research/verify.py`，覆盖最终源码的默认构建、Python 测试、
公共定义 golden、公理覆盖和全部本地模块 kernel 重放。实际逐门结果及最终源码 SHA256
由生成的 `build/verification/<UTC timestamp>/report.json` 记录，成功后再导出 atlas。
本记录不预先声称该完整运行成功，也不将运行后的最终哈希回写到源码而使收据失效。

本地重放信任钉住的第三方编译导入；未进行外部独立检查或隔离源码重建，未运行远端 CI，
未发布。当前证明认证、最终快照验证和远端发布是分别核实的事实。
