# 比较定理短名不复述完整类型

用户从全量命名清单中指出三条协方差松弛比较定理仍然过长。本轮精简这三条及同类
Poincaré 前端比较，共 12 个公共定理；命名空间、模块、定义和参数接口不变。
沿用已验证的本地工作区，基线快照为
`192ddba6daa0f0d0f0bdc3fdab82bb5bc180414f1c3f4809c73f3cf4c4229684`，
对应 `build/verification/20260908T122939.817508Z/report.json`。
分支仍为 `main`，HEAD 为 `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`；
此前未提交的改动作为基线完整保留。

## 名称与契约

完整映射在 [comparison-name-map.json](../api-migration/2026-09-08-comparison-name-map.json)。
短名中的共同操作只写一次，比较对象使用当前 namespace 内足以区分的短称。
类型和文档保留全部前提及精确等式；不为缩短名称改动数学契约。

| namespace | 原短名 | 当前短名 |
| --- | --- | --- |
| `Energy.CovarianceGradient` | `relaxation_eq_lipschitzGradient_relaxation_of_covariance_eq_id` | `relaxation_eq_lipschitz` |
| 同上 | `relaxation_eq_sequentialRelaxation_ofLinearPMap` | `relaxation_eq_ofLinearPMap` |
| 同上 | `relaxation_le_opNorm_mul_lipschitzGradient_relaxation` | `relaxation_le_mul_lipschitz` |
| `Poincare.SmoothTest` | `holds_iff_smoothGradient_preEnergy` | `holds_iff_preEnergy` |
| 同上 | `holds_iff_ambient_smoothGradient_holds` | `holds_iff_ambient` |
| 同上 | `constant_eq_ambient_smoothGradient_constant` | `constant_eq_ambient` |
| 同上 | `holds_iff_intrinsic_smoothGradient_holds` | `holds_iff_intrinsic` |
| 同上 | `constant_eq_intrinsic_smoothGradient_constant` | `constant_eq_intrinsic` |
| 同上 | `constant_eq_lipschitzGradient_constant` | `constant_eq_lipschitz` |
| 同上 | `holds_iff_localSlope_holds` | `holds_iff_localSlope` |
| `Poincare.LipschitzGradient` | `holds_iff_localSlope_holds` | `holds_iff_localSlope` |
| `Poincare.SmoothGradient.Intrinsic` | `constant_eq_localSlope_constant_of_ac` | `constant_eq_localSlope` |

第一条仍要求协方差等于恒等算子、绝对连续性及支撑边界为零。
第二条右侧仍是 `PreEnergy.ofLinearPMap` 所构造预能量的 sequential relaxation，
不是未松弛的算子平方范数。
第三条仍是协方差算子范数乘以 Lipschitz 松弛的上界，且要求该点 Lipschitz 松弛有限；
名称保留 `mul`，不暗示无系数的直接支配。
内在最优常数比较也保留原有的绝对连续性假设。没有通过去掉名称中的条件删除类型中的条件。

## 语义审查

开始时核对整个源码快照与上一份通过的收据一致，保存当前源码及 `.ilean` 声明和
引用位置到 `build/api-comparison-names/baseline/` 与 `ileans.json`。
迁移依据解析后的声明身份替换引用，更新源码、所有消费者、guards、Blueprint 锚点与指南。
没有别名、包装、参数泛化、假设删减或 linter 关闭。

源码比较覆盖当前全库：881 个公共声明签名、189 个定义/结构主体、包含证明在内的
885 个具名声明主体，在名称映射与格式归一化后全部一致，没有缺失或未解释差异。
另外从 12 个受影响定理出发，比较其 132 个本地声明的原始 Lean Expr 类型与定义闭包；
名称映射与绑定变量 alpha 归一化后全部一致，291 个外部依赖叶子不变。
模块、宇宙、参数顺序、显隐与依赖也不变。
12 个改名入口的匿名实例参数仅有编译器 hygiene 哈希变化；模块和局部 hygiene 序号
逐项核对一致，显式参数名没有变化。原始差异和审查在
[comparison-name-review.json](../api-migration/2026-09-08-comparison-name-review.json)。

现有 26 项 statement golden 检查通过，golden 及其既有 decision 均未修改。
本轮定理不改变该定义闭包，不能为每次改名无条件重生成 golden。
此前 90 份历史 decisions、explorations 与迁移证据保持原样。
158 条基础设施来源哈希先与基线核对，再根据源码比较刷新 7 个文件涉及的 13 条哈希；
路径、评价和认证状态不变。详见
[来源审查](../api-migration/2026-09-08-comparison-name-evidence.json)。

## 验收

预验收默认构建通过（3359 jobs）；12 个旧名全部通过 `#check_failure`，12 个新名
全部解析。现有证书、性质证明调用、一般有限维和零维应用保持构建通过。
Blueprint PDF/Web/checkdecls 通过；PDF 仍为 37 页，全部页面绘制内容与前次已检查版本相同。
命名清单重新从当前公共声明导出，供用户继续审阅。

记录定稿后运行根目录 `python3 research/verify.py`，保留全部 Python 测试、构建、
statement snapshot、声明与传递公理审计、当前全部本地模块 kernel 重放。
最终结果以 `build/verification/<UTC timestamp>/report.json` 为准，最新尝试保存于
`build/verification/latest.json`。最终收据须对应包含本记录的实际源码；
`git diff --check` 仅作为格式检查。本轮不 commit、push 或发布。
