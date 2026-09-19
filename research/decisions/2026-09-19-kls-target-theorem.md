# KLS 目标改为带 `sorry` 的 theorem；规则：未证断言不得只以 `def : Prop` 存在

2026-09-19。owner 决定。起点工作区含当日未提交的半群模块（`S1`–`S5`）。

## 决定

1. 新增叶子模块 `formalization/FunctionalInequalities/KLS/Target.lean`：
   `theorem FunctionalInequalities.KLS.kls : Conjecture := by sorry`。
   这是仓库**唯一有意保留的直接洞**，作用是让最终目标在 Lean 里可见，而不只在 Blueprint 里。
2. `def KLS.Conjecture : Prop`（`KLS/Statement.lean`）**保留**，作为这句话的名字，
   供以它为结论或假设的已证定理引用（`conjecture_of_affineBound`、证书 `ThmAffineIsotropicReduction`、
   `StatementChecks`、golden 语句快照）。四处引用与证书均不改动。
3. **规则**（自本记录起）：
   * `def X : Prop` 只允许用来给一句话命名，它零断言。
   * 任何未证的**断言**必须以 `theorem … := by sorry` 出现在 Lean 里，不得只以 def 的形式「存在」。
   * 带 `sorry` 的目标定理必须是叶子模块，只被聚合根 import。

## 为什么不是「删掉 def」

`def : Prop` 不是在假设 KLS 成立；Mathlib 对 `RiemannHypothesis`、`FermatLastTheorem` 用的是同一写法。
引用它的四处全是 `… → Conjecture`，KLS 在**结论**位置：这些是无条件已证的约化，
即便 KLS 为假它们也为真（那时它们说的是 `AffineBound K` 对一切 `K` 为假）。
仓库里没有任何 `Conjecture → …` 形式的条件结果。
删 def 会迫使四处把整句公式内联复制，失去单一来源并需要重建 golden 快照，代价更大且更容易走样。

## 门禁约束（决定了文件放哪、标签怎么写）

* `research/check_ledger.py` 禁止任何证书的 import 闭包出现 `sorry`，所以 `Target.lean` 不能被
  库内任何模块或证书 import；只有聚合根 `FunctionalInequalities.lean` import 它。
* `research/verify.py` 的 `declaration-audit` 门对 Blueprint 每个 `\lean{…}` 里的声明做公理审计，
  出现 `sorryAx` 即失败。所以 `conj:kls` 的 `\lean` 仍只列 `KLS.Conjecture`，`kls` 只在正文提及。
* `lake build` 通过：lakefile 未开 `warningAsError`，`sorry` 是警告。CI 的 `lake build` 同理。
* 单文件检查 `lake env lean -DwarningAsError=true KLS/Target.lean` **会**失败，这是预期的；
  该文件不适用零警告约定。

## 口径变更

此前记录「0 直接洞、26 证书」。自本记录起口径为：**1 个有意的直接洞（`KLS.kls`），0 个无意的直接洞，26 证书**。
后续审计不得把这 1 个洞当作回归。

## 规则细化：另三个 `conjectural` 节点为何不补 theorem（同日，owner 决定）

规则第 3 条的精确表述：**凡已有精确 Lean 命题的未证断言，必须以 `theorem … := by sorry` 出现。**
没有精确命题的节点不得为凑规则而发明语句或写占位定义——那是伪造，违背规则的初衷。
`tasks.json` 里另三个 `conjectural` 节点均属此类，本轮**不写任何 Lean**，只在各自 `note` 记录原因与前置条件：

| 节点 | 性质 | 为何暂无 Lean 语句 | 陈述它需要先建什么 |
| --- | --- | --- | --- |
| `q:smooth-gradient-raw-core-agreement` | 开放式问题（"determine when"） | Blueprint 明写不定义性地假设任何图范数/序列核等价；图范数有限能量域尚未构造；任何 theorem 都得由我们替 owner 发明一个具体命题 | owner 选定精确表述；`Energy.Functional` 域上的图范数稠密性定义 |
| `ass:tight-prefix-carleson` | 对手稿对象的假设 | `S_t, r_t, D_t, τ_η` 是 Eldan 随机局部化的两色量；仓库与 pinned Mathlib 都没有 SDE/Itô（Mathlib 有 Brownian 运动、滤子、停时，无随机积分） | 随机局部化定义模块（过程、停时、两色量） |
| `q:mm-spectral-occupation` | 开放式问题 | `g_t, H_t, A_t` 是沿随机局部化的第一特征函数量，同样缺 SDE/Itô；另需固定光滑强对数凹逼近方案 | 同上，加逼近方案的形式化 |

与 KLS 的区别：`KLS.Conjecture` 早已是一条精确的 `def : Prop`，补 theorem 只是换一种呈现；这三个节点补 theorem 则是新造数学内容。

## 改动清单

* 新增 `formalization/FunctionalInequalities/KLS/Target.lean`
* `formalization/FunctionalInequalities.lean` 加 import
* `formalization/blueprint/src/chapters/00-orientation-and-status.tex` `conj:kls` 后追加说明段
* `research/tasks.json` `conj:kls` 的 `note` 追加
* `formalization/FunctionalInequalities/KLS/README.md` 表格加一行；`formalization/README.md` 状态行追加
