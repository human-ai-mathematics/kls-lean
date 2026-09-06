# Lean 基础清理与 Blueprint 边界修正

日期：2026-09-05。用户授权修正审阅发现的问题，清理现有 Lean 代码，保持数学正确性和一般性，
并参考 formech 的书写风格。本记录只覆盖本轮修改，追加于此前 Blueprint 修复记录之后。

起点 HEAD：`70ca1c19c4d207a31716c2e589c0b096521a5490`。开始时已有未提交的 Blueprint、checker
及其测试修改；这些工作保留在原工作树。本轮未 commit、push 或执行远程 CI。

## 修正的数学接口

`formalization/blueprint/src/chapters/50-kls-routes.tex` 的 conditional-fiber 路线现在明确：

1. frame 构造要求 `d ≥ 1`。零维单位球面为空，没有概率 frame；零维 KLS 直接用零方差处理。
2. 量词顺序是一个有限常数对所有维数和测度成立，再为每个测度选择一个与测试函数无关的 frame：
   `∃ C ≥ 0, ∀ d ≥ 1, ∀ μ, ∃ ρμ, ∀ f`。
3. 纤维能量的积分取扩展非负值，最大形式域是其有限能量的 `L²` 类。有限梯度能量的 locally
   Lipschitz 测试属于该域，因此形式上的 gap 才能作用到文献 Poincaré 定义的全部测试。
4. 形式本身与 factor-four 界保留一般的有限二阶矩测度／log-concave 测度范围，不给 `μ`
   添加 isotropic 假设。框架的方向平均需要的是 frame 的 isotropy；路线的存在性问题才对
   isotropic `μ` 提问。
5. 正维 isotropic 结论通过命名的 affine/isotropic bridge 覆盖全部 affine supports；该 bridge
   已列入 sidecar 中 conditional-fiber 分支的 `all_of`。

这些是 Blueprint 表述和依赖的修正，未变更上游 source pin、上游 ledger 状态、本地 `leanok`
或 `notready` 状态，也未声称新的局部 Lean 证明。纤维形式的公式来源与本地接口澄清已分别注明。

另将 smooth-gradient 的“quadratic dense core”标题改为“quadratic pre-energy with dense
realization”，避免把 `L²` 稠密性解释成 graph-norm core；线性下界的证明说明采用实际已用的
covariance Rayleigh characterization，没有宣称本地已经提供最大特征值与算子范数相等的 API。

PDF 原先把共享 theorem counter 的部分交叉引用都显示为 “Theorem”。打印宏现在保留共享编号，
同时在各环境内部为 cleveref 指定正确类型；Assumption、Lemma 等引用与被引用对象一致。

## Lean 清理

新增 `Energy/RelaxationApproximation.lean`，仅提取现有证明重复使用的两步：

- `PreEnergy.exists_test_near_of_relaxation_lt`：在任意正半径内选出能量低于严格上界的测试。
  严格上界避免要求最优测试存在。
- `PreEnergy.DenseRealization.nonempty_approximatingSequence`：由稠密 realization 和 Mathlib
  的 `mem_closure_iff_seq_limit` 提供逼近序列。

下半连续性与 finite-energy recovery 共用第一步；infinite-energy recovery 共用第二步。有限／
无限能量分支、密度前提、非二次情形和伪度量一般性保留。原有公开声明不改名，不改变参数、
typeclass 前提或结论。没有合并 legacy 与 relaxed-energy 常数，没有引入未经证明的数学桥接。

补全 `TestFamily` 字段说明，并纠正将 extended Rayleigh quotient 称为 finite quotient 的注释。
Foundation 仍是面向应用的显式 aggregate；可复用底层模块没有反向导入它。

## 阅读体验和持续验证

书写参考为 `lyw-ops/formech@d0bb1913acc1f710ba6eadf1244b633abbc75fb9` 的 README 和两个 Lean
入口。采用其从数学含义进入、给出具体例子、明确模型边界与构建命令的方式，不引入其领域模型
或全局记号。

- 重写 Poincaré 基础指南，先给阅读入口与可直接使用的接口，再解释一般性、闭包、仿射支撑、
  四种常数接口与未证明边界；完整文件树统一由 `formalization/README.md` 维护。
- 新增 `examples/PoincareFoundation.lean` 的 12 个编译示例，覆盖能量比较、任意概率律、零维
  Euclidean 实例、Dirac 原始能量反例、空测试类以及 Gaussian 值。它们进入默认 `Examples`
  target，不增加公共数学定理或 ledger 节点。
- 新增 `solutions/FoundationAxiomAudit.lean`，默认构建固定八个核心声明的传递公理集，补充
  原有 Gaussian audit 与四个节点证书。
- 同步 Lake targets、当前说明文档，以及 CI 对 examples 直接 Mathlib imports 的缓存扫描。
  Lean、Mathlib 与 checkdecls 的版本固定值不变。

## 验证结果

| 检查 | 结果 |
| --- | --- |
| 完整 `lake build` | 成功，3234 jobs |
| 8 个新增或修改的 Lean 模块，`-DwarningAsError=true` | 全部通过 |
| 原有项目命名空间声明的类型与公理比较 | 665 个全部保留，类型打印输出无变化，公理依赖无增加 |
| 新增公共声明 | 仅上述两个逼近引理；比较后共 667 个声明 |
| 默认使用示例 | 12 个全部编译通过 |
| 基础公理 guards | 8 个全部通过，仅 `propext`、`Classical.choice`、`Quot.sound` |
| Ledger checker | 4 nodes，0 errors |
| Blueprint checker | 73 labels，4 active routes，0 errors |
| Python tests | 63 项通过 |
| Blueprint PDF、web、checkdecls | 全部构建通过，PDF 27 页 |
| PDF 最终日志 | 无 undefined references/citations、重复 label 或 overfull box；8 条 underfull 提示 |
| PDF 修改页面 | 物理页 9、14、24、25 逐页渲染并检查 |
| 修改后 Markdown 相对链接 | 无缺失目标 |
| `git diff --check` | 通过 |

声明比较在修改前后导入 library aggregate 与四个 certificate，以 `Meta.ppExpr` 打印类型、
`Lean.collectAxioms` 收集传递公理，按完整声明名比较。665 个包含结构字段和自动生成的公开
声明，不是 665 个独立数学定理。比较器要求非空且至少 400 条记录，避免空解析产生假通过。
类型比较与逐项源码 diff 审阅共同检查了原有数学接口；Lean 构建验证修改后的证明。

本轮本地验证材料位于：

```text
/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-cleanup-20260905-y_qb33wj/
```

其中 `api-before.txt`、`api-after.txt` 为声明文本快照，`api-comparison.json` 为结构化比较结果。
两个文本快照的 SHA-256 分别为：

```text
before  9ece29407b9e96c146940be9b076db60d99c95e571aa86fb23b9c2fec03305e4
after   df74034328b375e459f79b1f5edc475c9d519565d4d335b658ed89e8569e9be4
```

开始时存在的 49 个受保护文件（历史记录、四个证书、ledger、toolchain／manifest，以及无关的
` 2` 副本）逐个 SHA-256 比较均未改变。上述临时验证材料不是新的生产控制文件。

后续 KLS statement、常数桥接、whitening 和长路线证明仍按原来的数学边界推进。
