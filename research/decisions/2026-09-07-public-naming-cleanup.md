# 公共命名整理与全库检查

日期：2026-09-07。用户批准将冗长构造名整理为数学角色命名，并要求检查其他部分。
本次直接迁移现有声明与调用，没有新增兼容别名，没有移动目录、模块、证书文件或
Blueprint 节点。仅本地修改，未 commit/push，未运行远端 CI。

## 范围与取舍

扫描 Lean 库中 498 条具名公共定义、结构和定理声明（另有 36 条私有声明），并检查
solutions、examples、Blueprint 与当前文档。重复构造串主要集中在所选能量与常数，
以及 ambient/selected、legacy/relaxed、general log-concave 比较。通用 L² 优化器也有
相同的前缀重复，统一纳入 `Poincare.L2Energy`。

实际迁移 29 个公共声明。`Energy.Canonical.energy` 保留原来的内禀仿射光滑梯度松弛
定义；`Poincare.Canonical.constant` 是所选最优值，`Poincare.Ambient.constant` 是环境
松弛最优值，`Poincare.L2Energy.constant μ energy` 是参数化优化器。名字本身没有加入
Cheeger、Dirichlet、谱隙或 KLS 结论。

其余部分的审核结果与长期规则见 [命名约定](../naming.md)。恢复序列的有限性条件、
Gaussian 半直线与密度权重、逼近的紧支撑/加权/L¹/L²、测度论的支撑/内部/闭球条件
均有实际区分作用，保留其描述性名称；没有按字符数统一截短。

## 精确映射

下表省略共同前缀 `FunctionalInequalities`。原模块文件路径不变。

| 旧声明 | 新声明 |
| --- | --- |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationConstant` | `Poincare.Canonical.constant` |
| `Poincare.Euclidean.IntrinsicAffineSmoothGradientRelaxationHolds` | `Poincare.Canonical.Holds` |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationHolds_iff_constant_le` | `Poincare.Canonical.holds_iff_constant_le` |
| `Poincare.Euclidean.smoothGradientRelaxationConstant` | `Poincare.Ambient.constant` |
| `Poincare.Euclidean.SmoothGradientRelaxationHolds` | `Poincare.Ambient.Holds` |
| `Poincare.Euclidean.smoothGradientRelaxationHolds_iff_constant_le` | `Poincare.Ambient.holds_iff_constant_le` |
| `Poincare.Euclidean.smoothGradientRelaxationHolds_iff_intrinsicAffine` | `Poincare.Ambient.holds_iff_canonical` |
| `Poincare.Euclidean.smoothGradientRelaxationConstant_eq_intrinsicAffine` | `Poincare.Ambient.constant_eq_canonical` |
| `Poincare.Euclidean.holds_iff_smoothGradientPreEnergy` | `Poincare.Euclidean.holds_iff_preEnergy` |
| `Poincare.Euclidean.holds_iff_smoothGradientRelaxation` | `Poincare.Euclidean.holds_iff_ambient` |
| `Poincare.Euclidean.constant_eq_smoothGradientRelaxation` | `Poincare.Euclidean.constant_eq_ambient` |
| `Poincare.Euclidean.holds_iff_intrinsicAffineSmoothGradientRelaxation` | `Poincare.Euclidean.holds_iff_canonical` |
| `Poincare.Euclidean.constant_eq_intrinsicAffineSmoothGradientRelaxation` | `Poincare.Euclidean.constant_eq_canonical` |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationConstant_eq_literatureConstant` | `Poincare.Canonical.eq_literature_of_ac` |
| `Poincare.Euclidean.constant_eq_intrinsic_and_literature_of_logConcave` | `KLS.LogConcave.legacy_eq_intrinsic_and_literature` |
| `Poincare.Euclidean.constant_eq_literatureConstant_of_logConcave` | `KLS.LogConcave.legacy_eq_literature` |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationConstant_eq_literatureConstant_of_logConcave` | `KLS.LogConcave.canonical_eq_literature` |
| `Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation` | `Energy.Canonical.energy` |
| `Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation_apply` | `Energy.Canonical.energy_apply` |
| `Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation_closedQuadratic` | `Energy.Canonical.closedQuadratic` |
| `Energy.Euclidean.smoothGradientRelaxation_eq_intrinsicAffineSmoothGradientRelaxation` | `Energy.Euclidean.smoothGradientRelaxation_eq_canonical` |
| `Poincare.constantOfL2Energy` | `Poincare.L2Energy.constant` |
| `Poincare.HoldsL2Energy` | `Poincare.L2Energy.Holds` |
| `Poincare.holdsL2Energy_iff` | `Poincare.L2Energy.holds_iff` |
| `Poincare.holdsL2Energy_iff_constant_le` | `Poincare.L2Energy.holds_iff_constant_le` |
| `Poincare.l2EnergyRayleighMap` | `Poincare.L2Energy.rayleighMap` |
| `Poincare.constantOfL2Energy_anti_mono` | `Poincare.L2Energy.constant_antitone` |
| `Poincare.HoldsL2Energy.of_energy_le_mul` | `Poincare.L2Energy.Holds.of_energy_le_mul` |
| `Poincare.constantOfL2Energy_le_mul_of_energy_le_mul` | `Poincare.L2Energy.constant_le_mul_of_energy_le_mul` |

## 数学内容与调用约定

三个 `KLS.LogConcave` 比较定理将概率律参数 `μ` 从显式改为隐式，直接从
`hμ : KLS.LogConcave μ` 推断；量词、假设和结论保持不变。默认构建中的证书现在实际
使用 `hμ.canonical_eq_literature`，并保留一般 `Fin n` 和 `Fin 0` 的 typed applications。

重命名前后分别用现有 `StatementSnapshot` 工具展开 29 个入口的本地依赖闭包。
`build/naming/compare.py` 对全部 123 个声明检查类型与定义体：仅替换精确名称（含生成
的从属名字）、规范打印空白及依赖排序，并单独允许上述三个 μ 参数的推断标记变化。
其余内容、宇宙参数、模块位置和外部依赖全部一致。定理证明体不属于这个文本快照；
它们由默认构建与最终 kernel 重放验证。

`build/naming/RemovedNames.lean` 对全部 29 个旧名执行 `#check_failure`，进程成功退出；
日志中的 `Unknown identifier` 是预期结果，确认导入当前库后旧名没有作为别名存续。
当前 Lean 调用及公理 guards 均已迁移。

## 同步与保护

Blueprint 声明锚点、公理 guards、examples 和当前指南同步新名。三条 ledger statement
只替换其中引用的 Lean 符号；节点数量、生命周期、checked_by、数学分类与证书入口不变。
8 条基础设施来源哈希更新到已审查的迁移文件。route sidecar 完全不变。

进入本轮时的 KLS Definitions、Statement、golden、route sidecar 和全部既有
 decisions/explorations 共 59 个受保护文件，哈希逐一不变。原暂存区补丁逐字节不变。
保护检查见 `build/naming/change-audit.json`；名字映射和展开输入在同目录。

## 验证事实

HEAD：`70ca1c19c4d207a31716c2e589c0b096521a5490`。
进入本轮的源码快照：
`91762f2379b2b510176237d0b9c3d0192e55320fe0582cd0add724cea613927a`。
本记录写入前的预检快照：
`2b4cc8a837e7bc23cdd967daf83b8f5e82aab666dbccaac87597b73670b801d0`。

本阶段实际通过：ledger、Blueprint、atlas 结构检查；97 项 Python 测试；默认
`lake build`（3268 jobs）；123 项展开声明比较；29 个旧名移除检查；`git diff --check`。
图谱保持 74 个数学节点、87 个导航标签、10 个证书、4 条活动路线，无依赖环。
对应日志和比较结果位于 `build/naming/build.log`、`tests.log`、`semantic-audit.json`
及 `removed-names.log`。

初次迁移构建发现公理消息中的旧全限定名和一个跨命名空间的未限定引用；已修复，
未通过删除公理 guard 或加入兼容别名处理。后续默认构建已通过。

完成本记录后运行 `python3 research/verify.py`，对包含本记录的最终快照验证默认构建、
全部测试、KLS golden、公理审计与所有本地模块 kernel 重放。实际最终结果和源码
SHA256 记录在生成的 `build/verification/<UTC timestamp>/report.json`，随后导出 atlas。
本记录不预先宣称该最终运行通过，也不回写最终哈希而使验证收据失效。

本地重放信任钉住的第三方编译导入；未做外部独立检查或隔离源码重建，未核实远端 CI。
