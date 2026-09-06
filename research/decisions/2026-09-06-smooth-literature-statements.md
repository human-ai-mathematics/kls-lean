# 光滑测试与文献常数：八条 statement 与 Claude 交接

日期：2026-09-06。用户同意“验收加权逼近，并为下一批常数比较写 statement，留 sorry”。
本批为 `thm:smooth-lipschitz-constant-equivalence` 添加八条声明，全部保留 `by sorry`。
ledger 为 **`drafted / checked_by: null`**。七个已证明节点与本批草稿分开登记。

## 阅读入口和来源

1. [HANDOFF](../../HANDOFF.md)：当前范围、证明认证及追加式记录规则。
2. [Blueprint 共享分析桥](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex)：
   `thm:smooth-lipschitz-constant-equivalence` 的原陈述与证明；随后
   `thm:selected-literature-constant-equivalence` 仍有独立的 Borell 输入。
3. [KLS/LocalSlopeGradient.lean](../../formalization/FunctionalInequalities/KLS/LocalSlopeGradient.lean)：
   斜率、梯度、能量及测试域的四个证明洞。
4. [Poincare/Euclidean/LiteratureComparison.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/LiteratureComparison.lean)：
   有限常数、最优值及内禀坐标比较的四个证明洞。
5. [默认构建入口](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean)：只 `#check` 八条
   完整签名，没有新证书。本批未导入已认证库的聚合根或旧证书，也未给 Blueprint 添加
   未证明声明的 `lean` 锚点。

精确数学来源是本地书面论证和既有定义，数学分类仍为 `local_argument`。点态斜率识别、
测试域刻画和坐标下确界是把原证明中隐含的步骤显式化的本地接口，不归给未经核对的论文。

## 证明顺序

下表前四条位于 `FunctionalInequalities.KLS`，后四条位于
`FunctionalInequalities.Poincare.Euclidean`。

| 顺序 | 声明 | 精确用途 |
| --- | --- | --- |
| 1 | `localSlope_eq_norm_gradient_of_differentiableAt` | 可微点处，既有单点移动的 localSlope 等于 `ENNReal.ofReal ‖gradient f x‖`；不要求有限维或正维 |
| 2 | `localSlope_ae_eq_norm_gradient` | 有限维、ν ≪ Haar 下，局部 Lipschitz 函数满足上述等式 ν-a.e. |
| 3 | `literatureEnergy_eq_lintegral_gradient` | 把斜率能量识别为扩展梯度平方积分，允许无限能量 |
| 4 | `literatureAdmissible_iff_memLp_gradient` | 原 LiteratureAdmissible 精确等价于局部 Lipschitz、函数 L²、梯度 L² |
| 5 | `holds_iff_literatureHolds` | 对每个 C : NNReal，光滑测试与原文献测试的有效常数条件等价 |
| 6 | `constant_eq_literatureInfimum` | 在同一个坐标测度 ν 上，两组有效有限常数的 ENNReal 下确界相等 |
| 7 | `constant_eq_intrinsic_and_literature` | 对内禀测度绝对连续的 μ，给出原测度光滑常数 = 内禀测度光滑常数 = literatureConstant μ |
| 8 | `intrinsicAffineSmoothGradientRelaxationConstant_eq_literatureConstant` | 结合既有 legacy/selected 证书，把上述等式接到项目所选常数，保留相同的内禀绝对连续假设 |

步骤 1 从 Frechet 可微余项及导数算子范数的上下估计展开已有 `localSlope` 的 inf/sup；
Hilbert 梯度范数等于导数范数。特别处理零空间时不能依赖单位向量存在。
步骤 2 复用刚证明的局部 Lipschitz Rademacher，再用 ν ≪ m 转移零测集。
步骤 3、4 应完成 a.e. 能量转换、可测性和平方可积性，不额外假设目标能量恒等式。

步骤 5 的一个方向由光滑测试是局部 Lipschitz 得到；另一个方向对文献测试使用已认证的
加权逼近定理，取 B 为恒等映射。逐项应用同一个 C，再用函数 L² 收敛下的方差连续性
和梯度 L² 收敛下的能量连续性过极限。不要把这些收敛结论作为新的未经证明输入。
步骤 6 比较有限有效常数的集合，不需要最优值取到。

步骤 7 还需要把原测度和内禀测度的光滑测试不等式接起来：既有测试限制不增能量，
法向常值延拓保持能量，内禀 L² 等距映射保持方差。随后对内禀测度用步骤 6。
步骤 8 是这一结论与已有 `constant_eq_intrinsicAffineSmoothGradientRelaxation` 的组合。
即使是直接组合，本批也按用户要求保留证明体给 Claude。

## 坐标、量词和边界

`KLS.LiteratureHolds ν C` 直接在 ν 上测试函数，但 `KLS.literatureConstant μ` 的定义已经
先取了 `Probability.intrinsicMeasure μ`。因此步骤 6 显式写出
`⨅ C : {C : NNReal // KLS.LiteratureHolds ν C}, (C.1 : ENNReal)`，而不是错误地把它
替换成 `literatureConstant ν` 后再次进入内禀坐标。没有添加平行的常数定义或别名。

步骤 7、8 中 m 的类型是 `Measure (Probability.affineSupport μ).direction`，绝对连续
前提明确施加在 `intrinsicMeasure μ` 上。原测度 μ 可在环境空间中奇异，例如支撑在直线
上的概率律；不能给它偷偷增加环境 Lebesgue 绝对连续性。

常数 C 包含零，最优值留在 ENNReal 中，允许无穷及不存在有效有限常数。能量没有额外
的二分之一因子，测试包含零能量函数。除步骤 1 的更一般点态结论外，均在有限维 Borel
第二可数的完备实内积空间中进行。零维及零维仿射支撑保留。

不要求二阶矩、密度正下界、对数凹性或 raw/core agreement。尤其步骤 8 是显式绝对连续
条件下的比较，不能因此把 `thm:selected-literature-constant-equivalence` 的一般对数凹
版本或 Borell 节点标为已证明。当前 KLS 定义、Statement 和 golden 均未修改。

## 已有工具与证明边界

- `Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz` 与
  `measurable_gradient`：a.e. 可微性及规范梯度可测性。
- 同模块 `exists_smooth_weighted_L2_approximation`：取 B 为恒等映射；函数和梯度均有
  明确的 L² 成员条件及差值 eLpNorm 收敛，不能只使用函数值逼近。
- `MeasureTheory.memLp_two_iff_integrable_sq_norm`：转换梯度 L² 与平方范数可积，须保留
  其 a.e. 强可测性前提。
- `FunctionalInequalities.L2.continuous_variance`、`variance_toLp` 及
  `ProbabilityTheory.ofReal_variance`：连接 L² 方差与点态 extended/real 方差。后者须
  在原函数属于 L² 的条件下使用，不能从 totalized real variance 倒推可积性。
- `Energy.Euclidean.SmoothGradientTest.exists_intrinsic_restriction` 与
  `exists_ambient_extension`，以及 `Probability.measurePreserving_reconstruct`：坐标桥。
  不要使用 `intrinsicMap` 的仅可测支撑外分支充当全局光滑延拓。

这些名字在当前钉住的本地源码中核对。缺口是它们与已有 KLS 定义之间的本地证明适配。
`tasks.json` 因而将该节点的基础设施从 `unchecked` 细化为 `missing`，附源文件哈希和
具体缺口；已有逼近节点是 `available`。未改任何节点的 mathematics 分类或长路线状态。

Claude 可以添加有用途的辅助引理，也可在发现问题后调整公开接口；若改变数学范围，
须追加说明并同步 ledger，核对原目标是否仍被覆盖。不要增加“存在所需逼近”这样的
循环前提，不要改写 Definitions/golden 来让目标更容易，不要放宽公理检查。
未来证明完成后再创建此节点的证书并登记认证；本次不发送任务、不提交或推送。

## 本地证据与两次快照

首先已完成加权逼近的正式本地验收，收据为
`build/verification/20260906T142018.550602Z/report.json`，status 为 passed，source SHA256 为
`1a8ab75311a665296ff29a7c1b1be2d3d427fdd615016b7246c7f868afb6aa6c`，HEAD 为
`70ca1c19c4d207a31716c2e589c0b096521a5490`。97 项测试、默认构建、26 项定义 golden、
102 份声明公理报告及 61 个本地模块 kernel 重放通过。该快照还未包含本批八条草稿。
证书中不在结论里使用名字的全称前提随后改为匿名 binder，清理 linter 警告；前提仍保留，
是变量命名清理，不改变数学内容。本批最终验证将覆盖这个最终证书版本。

本批 `lake build solutions.ThmSmoothLipschitzConstantEquivalence` 通过，3094 jobs，八条
预期占位警告；完整打印的签名保留了上述坐标、Haar、绝对连续和有限维条件。分别检查
八条声明的传递公理应包含 `sorryAx`，不得当作证明验收。原声明打印和检查输出位于
忽略目录 `build/density-acceptance/`，不是新的真源或 golden。

本记录完成后对最终工作树再次运行 `verify.py`。最终收据的 source SHA256 和日志说明
七个已认证节点的验收与默认构建中草稿的 elaboration；普通草稿模块可含占位，完整验证
通过不代表本批八条声明已证明。最终收据结果不预先写成通过，也不回写哈希到源码。
本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI 或发布。
