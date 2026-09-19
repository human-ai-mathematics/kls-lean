# 2026-09-20 formalization 目录整理

`formalization/FunctionalInequalities/` 下的 71 个模块迁入家族目录。本轮**只改模块路径**：
没有重命名任何 namespace 或声明，没有改动任何定理陈述、证明、假设、维数范围或证书状态。

## 一、新的全局目录规则

规则写入 [`research/naming.md`](../naming.md) 的“家族词归目录，不进文件名”一节，自本日起
适用于全库，不只是 `Analysis/`：

1. **三个以上**属于同一数学对象的模块必须进入家族目录，basename 去掉家族词。
2. 两个模块若构成明确的“基础模块 + 扩展/性质模块”，可以进入家族目录。
3. 不允许 `X.lean` 与 `X/` 同时存在；这种情况下基础模块改名为 `X/Basic.lean`。
4. 根目录只保留跨家族基础设施、稳定公共入口，或确实无法归入单一对象的模块。
5. 目录按**主要数学对象**划分，不按一次性的证明路线划分。
6. 文件迁移不得改变 namespace、声明名、定理陈述、证明、假设、维数范围或证书状态。
7. 不提供旧路径兼容模块或别名。

### 为什么允许明确的两模块家族（规则 2）

规则 1 的“三个以上”是防止把偶然相邻的模块硬凑成目录。但“基础定义 + 其性质”是
一种已经定型的结构关系，不是偶然相邻：扩展模块的存在理由就是补充基础模块的对象，
第三个模块迟早会出现在同一位置。本轮的两例是

- `KLS/LogConcave/HeatSemigroup/{Basic,Markov}.lean`：`Basic` 把抽象半群构造特化到
  加权梯度算子，`Markov` 只证这个具体半群的 Markov 性质。
- `Energy/Cheeger/{Basic,Identification}.lean`：`Basic` 定义度量 Cheeger 能量，
  `Identification` 只证它与光滑梯度松弛的识别。

反过来，本轮**不**为只是碰巧同名前缀、没有基础/扩展关系的两个模块建目录；
`Poincare/L2/{Energy,Comparison}.lean` 进目录是因为它们同属 `L2Energy` 这一个数学对象
（能量的定义与该能量下最优常数的比较），不是因为 basename 共享 `L2`。

### 为什么 `FunctionalInequalities.lean` 与 `FunctionalInequalities/` 共存不算冲突（规则 3）

规则 3 针对的是**库内部**的 `X.lean` 与 `X/` 同名：这种形态让 `X` 既是一个模块又是一个
命名前缀，读者无法从路径判断 `X` 的内容是基础定义还是目录索引，本轮的
`Energy/Cheeger.lean` + `Energy/Cheeger/` 就是唯一实例，已改为 `Energy/Cheeger/Basic.lean`。

`formalization/FunctionalInequalities.lean` 是 Lake `lean_lib` 的**库根**（`lakefile.toml`
的 `[[lean_lib]] name = "FunctionalInequalities"`），Lean 4 与 Mathlib 的标准布局就要求
根聚合模块与同名目录并存（`Mathlib.lean` + `Mathlib/`）。它不是 `FunctionalInequalities/`
下某个数学对象的基础模块，而是整库的公共入口，由 `lake build` 按名字解析。
把它改成 `FunctionalInequalities/Basic.lean` 会改变库根，不属于目录整理。

### 为什么保留 `Poincare/Euclidean/`、`Poincare/FiniteProduct/`、`Poincare/LipschitzGradient/`

这三个目录是规则 5 的既有例外，本轮不动：

- `Poincare/Euclidean/` 按**定义域**划分（欧氏空间上的具体反例与障碍），
  namespace 是 `Poincare.Euclidean`，与 `Energy/Euclidean/` 成对。
- `Poincare/FiniteProduct/` 按**模型**划分（有限乘积律的张量化与几何），
  namespace 是 `Poincare.FiniteProduct`，与 `Poincare/Product/` 的可数情形分开。
- `Poincare/LipschitzGradient/` 按**测试类**划分，namespace 是
  `Poincare.LipschitzGradient`，与 `SmoothGradient`、`CovarianceGradient` 并列。

三者的目录名都与自己的 namespace 一致，且各自只有一到两个模块；它们划分的是数学对象的
**承载空间或测试类**，不是一次性的证明路线，因此规则 5 不要求改动。

## 二、迁移范围

三批共 71 个文件，逐条映射见：

- [`research/api-migration/2026-09-20-analysis-module-map.json`](../api-migration/2026-09-20-analysis-module-map.json)（30 个）
- [`research/api-migration/2026-09-20-foundation-module-map.json`](../api-migration/2026-09-20-foundation-module-map.json)（20 个）
- [`research/api-migration/2026-09-20-kls-module-map.json`](../api-migration/2026-09-20-kls-module-map.json)（21 个）

每份映射同时给出 dotted module map 和 filesystem path map。

| 批次 | 新建家族目录 |
| --- | --- |
| Analysis | `Analysis/Coarea/`、`Analysis/Hausdorff/`、`Analysis/Vector/Coarea/`、`Analysis/Vector/Slice/`；`Analysis/RankDeficient/` 整体并入 `Analysis/Vector/RankDeficient/`；`AreaFormula`/`SubgraphDivergence` 并入既有 `Analysis/Graph/`，`QuadraticCover`/`TaylorRemainder` 并入 `Analysis/Sard/`，`FirstOrderJet` 并入 `Analysis/Whitney/`，`LipschitzC1Pieces`/`LipschitzJet` 并入 `Analysis/Lipschitz/` |
| Energy / Probability / Poincare | `Energy/Form/`、`Energy/Euclidean/Slope/`、`Probability/Covariance/`、`Probability/Domination/`、`Poincare/L2/`；`Energy/Cheeger.lean` 改为 `Energy/Cheeger/Basic.lean`，`HaarLine` 并入既有 `Probability/Line/` |
| KLS | `KLS/Geometry/Perimeter/`、`KLS/Geometry/Slice/`、`KLS/Geometry/SmoothDomain/`、`KLS/LogConcave/Density/`、`KLS/LogConcave/HeatSemigroup/`；四个支持模块并入既有 `KLS/Geometry/Cheeger/` |

迁移后 `formalization/FunctionalInequalities/` 下没有空目录；
`Energy/Euclidean/` 的三个历史空目录（`SmoothGradient/`、`IntrinsicAffine/`、
`CovarianceGradient/`）与迁空后的 `Analysis/RankDeficient/` 一并消失。

## 三、不变量

- **只改模块路径。** namespace、声明短名、theorem statement、proof、参数显隐与顺序、
  假设、维数范围、证书状态全部不变。目录只承担分组。
- 特别地，下列 namespace 与其新目录名无关，本轮**没有**被同步改写：
  `FunctionalInequalities.Energy.Cheeger`（模块现在是 `Energy/Cheeger/Basic.lean`）、
  `FunctionalInequalities.Energy.Functional`（`Energy/Form/Functional.lean`）、
  `FunctionalInequalities.Poincare.L2Energy`（`Poincare/L2/Energy.lean`）、
  `FunctionalInequalities.Probability.Covariance`（`Probability/Covariance/Basic.lean`）、
  `FunctionalInequalities.Analysis.LipschitzJet`（`Analysis/Lipschitz/Jet.lean`）、
  `FunctionalInequalities.KLS.ConditionalFiber`。
  `Analysis/` 的模块无论放在哪个子目录，namespace 都仍是
  `FunctionalInequalities.Analysis`。
- **不保留兼容模块。** 旧路径不再存在，也没有转发 import 的 shim 或别名。旧引用只通过
  本轮的三份映射表解析。
- **历史记录冻结。** `research/decisions/**` 与 `research/explorations/**` 保留原路径写法，
  不追溯改写；`research/api-migration/` 下既有的映射（含
  `2026-09-19-kls-module-map.json`）原样保留，本轮新增三份独立文件。
- statement snapshot golden 只有一处变化：`FunctionalInequalities.Covariance.operator` 的
  `module` 字段由 `FunctionalInequalities.Probability.Covariance` 改为
  `FunctionalInequalities.Probability.Covariance.Basic`。依赖集、类型与 value 逐字不变。
- `FunctionalInequalities.KLS.kls`（`KLS/Target.lean`）是全库唯一有意保留的目标洞。
  本轮没有触碰它，没有把它加入任何 `\lean` 标签或证书闭包，也没有新增任何直接
  `sorry`/`admit` 或传递 `sorryAx`。

## 四、同步范围

生产 imports、根聚合 `FunctionalInequalities.lean`、`solutions/`、`research/audits/`、
README / HANDOFF / LEAN_DESIGN / `research/verification.md`、Blueprint 当前章节的
`\path{}`、`research/progress/nodes.json`（及由它生成的 README / STATUS / TREE / LITERATURE）、
`research/tasks.json` 的证据路径与 sha256、`research/proof-corrections-and-improvements.md`
全部同步。Blueprint 的 `\lean{}` 声明标签不含模块路径，未改动。
