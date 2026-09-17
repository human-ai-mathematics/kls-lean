# Analysis/ 重组：家族词从文件名移进目录

2026-09-17（同日，在文件管理那一轮之后）。本轮**不证明任何定理，也不改任何声明**：
把 `formalization/FunctionalInequalities/Analysis/` 的 50 个平铺模块中的 **32 个**
按数学家族移进子目录，basename 去掉家族词。
规则来自上一轮补进 `research/naming.md` 的「家族词归目录，不进文件名」。

**这是纯文件层改动。** 没有任何声明被改名、新增、删除或重证；没有任何 namespace 变动。
不迁洞，不提交、不推送。直接洞仍 **8（1/2/5）**，证书仍 **24**。

起点 `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`；
上一轮收尾 passed 回执 `build/verification/20260917T101245.968268Z/report.json`，
10 个门、224 个本地模块内核重放、611 条目，快照
`52d3c1c3f3c115e85b1413681603573777cfe83a587446a703261579eb85095a`，drift 为空。
本轮期间并发会话未改动工作区，也未提交。

## 边界

对数凹 Cheeger–Buser 线归合作者**王浩丞**，本轮未触碰；
尖锐有限正则 Sard、Energy 的五个洞、无量纲 KLS 也都未触碰。
本轮**与任何数学内容无关**。

## 为什么声明名不受影响

50 个模块里 **43 个**用扁平的 `namespace FunctionalInequalities.Analysis`；
另外三个嵌套 namespace（`Analysis.WhitneyCover`、`Analysis.WhitneyJet`、`Analysis.LipschitzJet`）
**一个字都没动**。namespace 与目录无关，所以声明全名不随目录变化。
因此 ledger 节点、Blueprint 声明、statement snapshot 的 golden、
以及全部公理报告都**不受重组影响**——这一点由公理报告数不变直接验证。

特别注意 `WhitneyCover` 既是模块名又是 namespace 名：
模块 `Analysis.WhitneyCover` 迁到 `Analysis.Whitney.Cover`，
而 namespace `FunctionalInequalities.Analysis.WhitneyCover` 保持原样。
重写脚本因此**只改 `import` 行**与文档里的 `Analysis/<File>.lean` 路径串，
不做任何全局标识符替换；改前统计的 148 处 `FunctionalInequalities.Analysis.<被迁模块>`
中，126 处在 import 行，其余 22 处全是该 namespace 及其声明，逐条核对后原样保留。

## 分组

* **`Whitney/`**（5）Bump、Construction、Cover、Extension、Partition
* **`Sard/`**（4）Basic、Planar、Smooth、Equidimensional
* **`Vector/`**（11）CriticalSlice、FiberIntegral、HausdorffSlicing、LocalCoarea、
  RegularChart、RegularCoarea、SliceMeasurable，外加再嵌一层的
  `Vector/Graph/{Basic,Area,Integral,Sandwich}`
* **`RankDeficient/`**（8）Stratification、RightInverseBound、TangentialLipschitz、
  RegularFibreFinite、TargetSplitFubini、StratumSlicing、Coarea、ExponentObstruction
* **`Graph/`**（4）Integral、Jacobian、Implicit、OpenIntegral

**`Sard/Equidimensional` 是按数学对象分的，不是按出身。** 它是路线义务 `R10`，
但它讲的是同维 Sard 引理，而 `naming.md` 要求「文件按主要数学对象归属」。
这一取舍如实记在这里。

**18 个留在平铺**：AreaFormula、CoareaGraphJacobian、CoareaJacobian、Divergence、
FiberIntegral、FirstOrderJet、HausdorffContent、HausdorffSlicing、LevelSet、
LipschitzC1Pieces、LipschitzJet、LocalInverse、NormDetContinuity、PartitionOfUnity、
QuadraticCover、RegularChart、SubgraphDivergence、TaylorRemainder。
其中 `CoareaGraphJacobian` **故意不进 `Graph/`**：叫 `Graph/CoareaJacobian` 会造出
第二个 basename 为 `CoareaJacobian` 的模块，读起来比它消掉的重复更糟。
`Divergence`/`SubgraphDivergence`、`HausdorffContent`/`HausdorffSlicing`、
`LipschitzC1Pieces`/`LipschitzJet` 都只有两个模块，不到规则的三个门槛。

## 路径映射表

`research/api-migration/2026-09-17-analysis-module-map.json`，32 条模块映射 + 32 条文件路径映射。
它存在的理由：**约 434 处历史 decision 与 exploration 按旧路径引用这些文件，本项目不改写历史记录**，
映射表让那些引用保持可解析。做法照搬 2026-09-08 那两次
（`2026-09-08-module-map.json`、`2026-09-08-library-naming-module-map.json`）。

## 改了哪些文件

* 移动 **32** 个模块。
* 重写 **70** 条 `import` 行与 **44** 处文档路径串，共 **61** 个 `.lean` 文件
  （`formalization/`、`research/audits/`，以及 `build/audit/` 里**每轮重跑的那 7 个活客户端**）。
* `build/audit/` 里 38 个 `.before.lean` 与历史路线评审**保持冻结**，旧 import 原样保留：
  它们是历史快照，不参与重跑。
* `research/tasks.json`：29 条 evidence 路径改写，59 条哈希刷新。

## 一处必须如实说明：路线语句文件不再字节不变

`research/audits/RankDeficientRouteStatements.lean` 此前各轮都记为**字节不变**。
本轮它**变了 5 行**：1 行 `import`（`Analysis.VectorCriticalSlice` → `Analysis.Vector.CriticalSlice`）
与 4 处文档里的路径串。这是模块搬家对**任何**引用者的不可避免影响。

**15 条 `#check` 命题逐字未变**，已用脚本逐块与 `HEAD` 对比确认全部 byte-identical。
文件顶部那条过时的状态说明也未改动，仍归其维护者。
此前各轮记录里「字节不变」的说法对**那些轮**依然成立，本轮在此更正其现状。

## 验证

* 默认 `lake build` 通过（3426 jobs）。
* 重跑 **52 个**审计客户端，全部 `-DwarningAsError=true` 严格通过，**0 失败**。
* 全库公理报告 **672 条**、`sorryAx` **12 条**，与重组前**逐数字一致**——
  这是「没动数学」最直接的证据。
* 三个 WIP 逐个实际编译，直接洞 **1/2/5，总数 8**；`check_ledger.py` 报 **24** 个证书。
* 根目录 `python3 research/verify.py` 通过；本地日志在 `build/audit/analysis-regrouping/`，
  最终核对另存 `build/audit/analysis-regrouping/final-snapshot.json`。
* **没有提交、没有推送**，真实 Git index 未改动。
