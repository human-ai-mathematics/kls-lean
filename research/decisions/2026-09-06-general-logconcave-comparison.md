# 一般对数凹测度：内禀绝对连续与文献常数比较

日期：2026-09-06。用户要求“先推广到一般的对数凹测度”，沿用此前直接完成证明的授权。
本批在本地完成一般有限维版本，没有向原定理追加绝对连续、密度、正维数或矩假设。
HEAD 是 `70ca1c19c4d207a31716c2e589c0b096521a5490`；工作树含此前未提交内容。
未 commit/push，未运行远端 CI，原暂存区逐字节不变。

## 结论、来源和阅读顺序

1. [仿射支撑](../../formalization/FunctionalInequalities/Probability/AffineSupport.lean)：
   新增任意概率律的内禀测度具有全仿射支撑的定理。
2. [对数凹几何](../../formalization/FunctionalInequalities/KLS/LogConcave.lean)：
   仿射等距重构保留紧集对数凹性；等半径闭球质量满足对数凹不等式；支撑及质量超水平集凸。
   内禀支撑内部非空，边界为 Haar 零测集。
3. [球平均](../../formalization/FunctionalInequalities/Probability/BallAverages.lean) 与
   [测度控制](../../formalization/FunctionalInequalities/Probability/BallDomination.lean)：
   支撑紧子集上的邻域质量有统一正下界，Tonelli 给出球平均总积分和局部下界；
   Besicovitch 覆盖将小球质量比上界转为测度控制。
4. [内禀绝对连续](../../formalization/FunctionalInequalities/KLS/LogConcaveDensity.lean)：
   从上述紧集不等式完整推出内禀绝对连续，并推出内禀支撑边界的概率质量为零。
5. [一般常数比较](../../formalization/FunctionalInequalities/Poincare/Euclidean/LogConcaveComparison.lean)：
   组合已认证的光滑/文献与 legacy/relaxed 比较，得到任意对数凹概率律的
   ambient legacy、intrinsic legacy、literature 常数链，以及 selected/literature 等式。

绝对连续结论属于 Borell (1974), *Convex measures on locally convex spaces*, Theorem 1.1
的有限维表示内容。本地证明采用下面的球平均路线，直接使用本仓库紧集定义；不声称
逐行翻译原论文证明，也不引用未证明的 Borel 集对数凹桥作为前提。常数比较的数学规格
是原 Blueprint `thm:selected-literature-constant-equivalence`，现在完整覆盖。

## 绝对连续证明和边界复核

令内禀律为 ν，Haar 参考为 m，q_r(x)=ν(closedBall x r)，b_r=m(closedBall 0 r)。

- 仿射支撑的最小性及等距重构推出内禀支撑的仿射包是全空间。结合凸性得到非空内部。
- 在内部选取较大的紧球。对固定 δ>0，紧性给出各中心的 δ 球质量统一下界 γ>0。
  Tonelli 表明较大球上的 q_r 积分至少为 γ b_r，因此在每个邻域内能找到
  q_r≥c b_r 的点，其中 c>0 与小半径 r 无关。
- q_r 的超水平集凸。分离定理将邻域中高质量点的存在强化为一个固定球 B(a,R)
  上处处 q_r≥c b_r。非零分离泛函的单位方向仅在实际产生分离时使用，未要求空间非平凡。
- 对任意 x，中点不等式在 B((x+a)/2,R/2) 上给出
  q_r≥sqrt(q_r(x)c b_r)。其总积分为 b_r，积分后平方并消去正且有限的 b_r，得到
  q_r(x)≤b_r/(c m(B(0,R/2))²)。该常数依赖于测度；不是维数无关的 KLS 常数。
- 使用源测度 ν 的 Besicovitch Vitali family，所需的绝对连续前提是 ν≪ν 的反身性。
  因而覆盖论证没有循环假设 ν≪m。最后得到 ν≤C m，进而 ν≪m。

所有 Haar 体积的正性与有限性均在 Lean 中证明；全部除法消去显式处理零与无穷。
内禀空间可为零维，环境测度可以奇异。最优常数等式在 ENNReal 中成立，允许零和无穷，
不要求最优值取到、不要求二阶矩，也不改变测试域或归一化。
新增证书含与 `Conjecture` 相同的任意 `Fin n` 欧氏空间应用，并单独检查 `Fin 0`。

## 认证与图谱登记

新增精确节点 `lem:logconcave-intrinsic-absolute-continuity`，由
`Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate` 认证；原
`thm:selected-literature-constant-equivalence` 由
`Solutions.ThmSelectedLiteratureConstantEquivalence.certificate` 认证。
两者均为 `proved / checked_by: lean`。沿用 ledger 现有 schema 的 `kind: lemma`
分类约定，包括 `thm:` 标签节点；不更改校验器的种类规则。

完整 `thm:borell-logconcave-density` 的陈述和任务分类保留，其上半连续对数凹密度代表、
内部局部正界及所有阶矩仍未证明。常数比较真正使用的是绝对连续子结论，故其 Blueprint
依赖改为新增精确节点。route sidecar 仅将已实际证明的 selected/literature 共享适配声明
登记为 proved，并绑定本地 ledger 证据；KLS 目标、各长路线、其条件及 AND/OR 组合不变。

ledger 原八个节点对象逐项不变，全部既有 `mathematics` 分类不变。新增节点归为
`published`，本地基础设施评估为 available；常数比较及旧比较文件注释的来源哈希同步。
新证明、公理 guards 和两份证书纳入默认构建。当前指南同步为 74 个数学节点、87 个导航
标签、10 个证书、4 条活动路线。Python 测试夹具现在允许同一节点兼任已认证结果和
路线适配声明，避免重复标签，同时提供校验器要求的实际本地证据。

KLS Definitions、Statement、golden 及全部既有 decisions/explorations 的 57 个受保护
文件与进入本轮时的哈希一致。`LiteratureComparison.lean` 仅修正文档指向新的推广模块，
原八条证明和签名不变。未引入任何证明占位或额外公理，也未证明 KLS、Cheeger 能量
识别或具体 Dirichlet 性质。

## 本地检查与最终验证边界

进入本批时的源码快照是
`af64ebc752ef58d682a1b747f2853b4c6f775ddbeac4bafff605ba56f10b6372`。
本记录写入前的预检快照是
`fb690033bfc84e7a4e8f4759f75982004fc8dc8c92d926ab6c52849d257ba87a`；
该快照的 ledger、Blueprint 和 atlas 结构检查通过，无依赖环。
本阶段已完成默认 `lake build`（3268 jobs）、两份证书构建（3107 jobs）、最后的欧氏族
与零维 typed check 构建（3106 jobs），以及 97 项 Python 测试。测试初次因旧夹具的重复
标签失败，修正夹具后全部通过。23 个新增传递公理 guards 均严格得到
`propext`、`Classical.choice`、`Quot.sound`。相关日志是：

- `build/logconcave-extension/default-build.log`
- `build/logconcave-extension/certificates-build.log`
- `build/logconcave-extension/typed-checks-build.log`
- `build/logconcave-extension/python-tests.log`
- `build/logconcave-extension/change-audit.json`

本记录写完后运行 `python3 research/verify.py`，在包含本记录的最终源码快照上再次核实
测试、默认构建、公共陈述 golden、传递公理和全部本地模块 kernel 重放。
实际结果、各门日志、最终源码 SHA256 与 HEAD 由
`build/verification/<UTC timestamp>/report.json` 记录，成功后导出 atlas。
本记录不提前声称最终运行通过，也不回写最终哈希而使其收据失效。

第三方编译导入仍被信任；没有外部独立检查、隔离源码重建或远端 CI 结果。
本地证明、最终快照验证和远端发布是不同事实。
