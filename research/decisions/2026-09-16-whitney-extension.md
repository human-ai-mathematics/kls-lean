# L6：紧集一阶 Whitney jet 的 C¹ 延拓完成

2026-09-16。本轮起点 HEAD/origin/main 均为
`dcc158d7d3b9e91f17d2ee0fd49b30cdb6f4f7d8`。起点回执
`20260915T171518.856116Z` 通过，479 条目，快照
`b531c9e4be6397d1d3e5893b4c57eb166ae63ded45f9064f1c4d5c039bb7f124`，与起点源码一致。
保留所有既有 Lean 文件和历史决定的原字节；不提交、不推送，不改真实 Git index。

## 精确结论

`FunctionalInequalities.Analysis.WhitneyJet.exists_contDiff_extension`，位于
`formalization/FunctionalInequalities/Analysis/WhitneyConstruction.lean`：有限维实内积空间中，
S 紧、F 在 S 上连续，且 (f,F) 满足原始 L6 的一致一阶余项条件，则存在全局 C¹ 函数 v，
在 S 上精确等于 f，且每一点的**环境导数** `fderiv ℝ v x = F x`。

没有增加非空、正维、内点、凸性、有限集假设。公开定理甚至不需要原始语句的
`ContinuousOn f S`（余项已蕴涵此连续性），也不需要额外列出 CompleteSpace、
MeasurableSpace、BorelSpace。`research/audits/WhitneyConstructionAudit.lean` 的
`original_L6` 逐字保留原始 L6 的命题文本和全部实例、假设，并给出证明。
这是原路线所要求的**紧集**延拓；没有另外声称任意非紧闭集上的局部 Whitney 条件版本。

结合既有 `Analysis.uniform_jet_remainder_of_contDiff`，原始一致余项条件的必要性与
充分性现在都有证明。旧 FirstOrderJet 和 WhitneyExtension 审计客户端中的“未证明”文字
是各自历史轮次的快照，不改写那些已经绑定哈希的来源；当前状态以本决定及新客户端为准。

## 构造与估计

四个新模块均只通过分析模块依赖 Mathlib，不导入 KLS 或 WIP。

1. **WhitneyCover**：令 `r(x)=min(1,dist(x,S))/20`。Vitali 抽取得到两两不交的小球，
   五倍球覆盖整个补集。八倍闭球仍在补集内，并在补集的子空间拓扑上局部有限。
   与 `ball y (r(y))` 相交的八倍球，其中心 z 满足
   `r(y)/2 ≤ r(z) ≤ 2r(y)`、`dist(z,y) ≤ 20r(y)`。
   Haar 体积比较给局部基数界 `N=81^finrank`。封顶半径允许处理无界补集；不声称常数尖锐。
2. **WhitneyBump**：缩放一个内半径 5、外半径 8 的光滑 bump。
   值在 [0,1]，五倍球内为 1，支撑在八倍闭球内；存在统一 M>0，导数范数 ≤M/r。
   由基础 bump 导数的紧支撑和连续性取界，链式法则给缩放；零维也适用。
3. **WhitneyPartition**：按上述覆盖求和并归一化。和至少为 1；得到非负光滑权重 φ，
   局部有限、和为 1，且存在 K>0，`‖Dφ_z(y)‖ ≤ K/r(y)`。明确证明局部邻域上等于
   一个至多 N 项的有限和，再求导；没有把点态有限重叠误当成局部有限性。
4. **WhitneyConstruction**：对每个中心选 S 上最近点 p_z，令
   `w(y)=∑ φ_z(y) (f(p_z)+F(p_z)(y-p_z))`。补集上 w 光滑。
   当 d=dist(y,S)<1/2 时 r(y)=d/20；相关 p_z 距 y 至多 3d，距 y 的最近点 a 至多 4d。
   F 的紧集上一致连续性和 jet 余项给仿射差 ≤7ηd。
   值误差用非负权重和 1；导数误差用 `∑Dφ_z=0` 消去公共仿射值。
   两项分别得到 `7ηd` 和 `η+140NKη`，取 `η=ε/(8+140NK)`，即给出所需
   `εd` 和 `ε` 两项一致估计。既有边界拼接定理据此构造全局 C¹ 延拓。
   空集分支直接取常数 0，不使用不存在的最近点。

## 验证与证据

四个新模块及新客户端用 `-DwarningAsError=true` 编译；新客户端 13 条公理报告仅有
`propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。客户端含原始完整 L6、空集、
单点任意环境导数、零维，以及平方函数在无限紧区间上的 jet。
22 个审计客户端全部重跑（research/audits 15 个，已有 build/audit 7 个），三个 WIP
逐个重编译仍为 2/2/5。LevelSetMeasurableAudit 的 4 个、IsoperimetryCoareaAudit 的 6 个、
SuperlevelSardScope 的 2 个 sorryAx 报告是刻意保留的开放洞审计。

逐项日志、命令、哈希和源码保持核对记录在
`research/explorations/2026-09-16-whitney-extension.json`。最终默认构建、完整验证、
195 个本地模块内核重放及精确源码绑定以
`build/audit/whitney-extension/final-snapshot.json` 指向的回执为准。
进度图使用临时 Git index 和临时对象目录生成，真实 index 不变。

## 后续边界

**L6 已完成；L6a、L7、L12 和 Lipschitz coarea 未完成。** 下一步是原始 L6a：
从 Lipschitz 函数提取可数紧集，覆盖几乎处处的点，每片同时保留可微性、导数连续性和
一致一阶余项。然后逐片调用本轮 L6 得 L7 的精确 C¹ 分片，再接 L12。
L6a 的精确量词仍见原始 weighted-coarea-route 决定；Lusin–Souslin 并不是所需的 Lusin 提取。

直接洞 **9（2/2/5）**，证书 **24**，perimeter infrastructure **missing**，均不变。
尖锐有限正则性 Sard、两个 Cheeger 比较、维数无关 KLS 仍开放。进度图 WHIT 合并节点
还包含未完成的精确 C¹ 分片，因此保持 ◐，不把整个 Whitney–Lusin 路线标成完成。
