# 加权光滑逼近：本地验收与证书登记

日期：2026-09-06。用户在“先验收这批证明，再准备常数比较 statement”的建议后回复
“可以”。本记录接受 `lem:covariance-test-core-density` 当前四条证明，并接通已有验收流程。
起点 HEAD 为 `70ca1c19c4d207a31716c2e589c0b096521a5490`，包括此前未提交工作。
本次不 commit/push，不改写历史 decisions/explorations 或先前暂存内容。

## 来源与范围复核

读取 [statement 交接](2026-09-06-weighted-approximation-statements.md)、
[证明完成记录](2026-09-06-weighted-approximation-proofs.md)、Blueprint Appendix A，以及
四条公开声明和实现。此次未修改四条声明的签名，也未添加数学输入；实现仅移除三个
经当前 Lean linter 确认无效的 `beta_reduce`。不禁用 linter。

主结论仍只要求 g 与 B∇g 属于 L²(ν)，B 允许退化；ν 对任意正归一化 Haar 参考测度绝对
连续，包含零维。辅助结论保留紧支撑、同一 Lipschitz 常数以及 bounded-L1 的任意闭区间。
完整梯度平方可积没有被添加为主结论的前提。局部斜率、文献常数及闭算子结论不在本批中。

实现使用 Rademacher、缩放截断、非负归一化核与控制收敛。卷积梯度收敛通过可微点的
仿射模型及核导数质量估计实现；它不需要按原书面路线额外构造弱导数。实现路线变化
不改变目标数学范围。

## 登记

- `solutions/LemCovarianceTestCoreDensity.lean` 的唯一
  `Solutions.LemCovarianceTestCoreDensity.certificate` 显式合取打包全部四个合同，
  每个分量直接使用相应库定理。保留四条库声明的检查，并为新证书加传递公理 guard。
- ledger 中该节点改为 `proved / checked_by: lean`；只更新已过时的草稿措辞与验收来源，
  原六个节点不变。已有 `lem:covariance-test-core-density` Blueprint 标签直接承载证书
  链接及 `leanok`，不增加导航节点。
- 在 `check_blueprint.py` 既有显式映射中登记新证书，没有改变验证算法或放宽验收条件。
  `tasks.json` 的数学分类仍是 `local_argument`，基础设施改为 `available`，带已实现库与
  证书源码哈希；TeX 证据哈希随新增认证锚点更新。没有修改任何长路线状态。
- 当前指南同步为七个证明证书，并保留未证明的文献常数比较及 Borell 密度输入。

## 已核实与最终收据

本地复核四条声明的传递公理均恰为 `propext`、`Classical.choice`、`Quot.sound`。
对入口及本地导入闭包的逃逸标记扫描通过。移除无效 tactic 并增加证书后的
`lake build solutions.LemCovarianceTestCoreDensity` 通过，3032 jobs；新证书 guard 通过。
ledger、Blueprint、atlas 检查通过：7 个已证明 ledger 节点、7 个证书、73 个数学节点、
86 个导航标签、4 条活动路线，无依赖环。

本记录及指南编辑完成后运行 `python3 research/verify.py`。其生成的
`build/verification/<UTC timestamp>/report.json` 才记录最终实际结果、逐门日志、完整证书
打印、公理覆盖、局部 kernel 重放及源码 SHA256。本记录不预先声称该完整运行成功，
也不将生成后的最终源码哈希回写到本文件。后续新增 statement 会改变工作树，必须把
验收快照与后续草稿快照区分；若再次运行验证，以相应收据的源码哈希为准。

这里的重放仍信任钉住的第三方编译导入，不是隔离源码重建或外部独立检查。
没有运行远端 CI，也没有发布。
