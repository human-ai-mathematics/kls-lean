# Borell 密度表示：statement 起草与语义对齐

日期：2026-09-07（Asia/Shanghai）。基线：`0451f2e` 之上的未提交工作树，本地 `main` 与
`origin/main` 一致。Lean/Mathlib 为 v4.33.0，Mathlib 提交
`db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示："暂时先不发布，完成第一步的那些
工作，然后帮我写出第二步的 statement，要求风格与 formech 一致，然后跑完后检查一次语义
是否对齐"。本决定不做 commit、push、远端 CI 或 Pages 部署。

## 第一步：收口，不发布

前一轮分析发现两处与已完成证明不一致的文字，本次改正：

1. `formalization/FunctionalInequalities.lean` 的模块文档仍写 Borell 等价与 conditional-fiber
   "含 `sorry`，等待 Claude 证明"。改为说明二者已证，并指出新模块
   `KLS/BorellRepresentation.lean` 是当前唯一含占位的草稿。
2. `blueprint/src/chapters/50-kls-routes.tex` 第 7 行仍称本章无任何节点带 `leanok`。改为：
   上游陈述均未 Lean 认证；本章唯一的 `leanok` 是已实现定义 `def:conditional-fiber-form`，
   定理、推论、假设与问题均不带 `leanok`。

上一份收据 `build/verification/20260907T083402.818470Z` 状态为 passed，但其快照哈希已过期，
原因只有 Prove2Me 文件删除与 lakefile 改动。本决定完成后重跑 `verify.py`，让收据与当前
源码一致；结果不在此预写。发布（CL、commit、push、远端 CI）按用户要求推后。

## 第二步：`thm:borell-logconcave-density` 的 Lean statement

### 阅读入口

1. [HANDOFF](../../HANDOFF.md)、[验证流程](../verification.md)、[命名](../naming.md)。
2. Blueprint [00 章](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex)
   `thm:borell-logconcave-density` 的原陈述。
3. [KLS/BorellRepresentation.lean](../../formalization/FunctionalInequalities/KLS/BorellRepresentation.lean)：
   先读 `IsBorellDensity`，再读五个 `sorry` 义务与两条已证恒等式。
4. [默认构建入口](../../solutions/ThmBorellLogconcaveDensity.lean)：打印八条签名，给出
   `Fin n`、`Fin 0` 的类型应用，为两条已证恒等式加标准公理守卫。没有 `certificate`。

### 写作约定

HANDOFF 把 `lyw-ops/formech@d0bb1913` 定为写作风格参考。本批遵循其 README 与 AGENTS.md 的
几条做法：每个声明的文档先说结论是什么、在什么模型下成立，再单独一句说明不主张什么；
命题级规格与可执行对象分开，这里体现为 `IsBorellDensity` 是 `Prop` 结构，存在性、正性、
有界性与矩是独立定理；有限范围显式写出，例如零维、任意 Haar 参考测度；不把草稿呈现为
定理。没有采用 formech 的自定义记号或 `Bool` 谓词，因为本仓库对象不是有限可枚举的。

### 声明表

下表省略公共前缀 `FunctionalInequalities.KLS`。类型变量：`F` 为有限维完备实内积空间，
Borel、第二可数；`V := (Probability.affineSupport μ).direction`；`ν := Probability.intrinsicMeasure μ`；
`m` 为 `V` 上任意加法 Haar 测度。

| 序号 | 声明 | 状态 | 精确内容 |
| --- | --- | --- | --- |
| 0 | `IsBorellDensity ν m ρ` | 定义，无占位 | `ρ : V → ℝ` 可测、非负、上半连续、逐点实幂对数凹 `ρ x ^ t * ρ y ^ (1 - t) ≤ ρ (t • x + (1 - t) • y)`（`0 < t < 1`），且 `m.withDensity (ENNReal.ofReal ∘ ρ) = ν` |
| 1 | `LogConcave.exists_isBorellDensity` | `sorry` | 对每个 Haar `m`，存在 `ρ` 使 `IsBorellDensity ν m ρ` |
| 2 | `IsBorellDensity.pos_of_mem_interior_support` | `sorry` | 概率律的任意代表元在 `interior ν.support` 上逐点为正 |
| 3 | `IsBorellDensity.exists_bounds_of_isCompact` | `sorry` | 对 `interior ν.support` 的任意紧子集 `K`，存在 `0 < a` 与 `b` 使 `a ≤ ρ x ≤ b` 于 `K` |
| 4 | `LogConcave.intrinsic_integrable_exp_norm` | `sorry` | 存在 `t > 0` 使 `exp (t * ‖v‖)` 关于 `ν` 可积 |
| 5 | `LogConcave.intrinsic_integrable_norm_pow` | `sorry` | 对每个 `p : ℕ`，`‖v‖ ^ p` 关于 `ν` 可积 |
| 6 | `LogConcave.closure_convexHull_intrinsic_support` | 已证 | `closure (convexHull ℝ ν.support) = ν.support` |
| 7 | `LogConcave.intrinsic_interior_support_compl` | 已证 | `ν (interior ν.support)ᶜ = 0` |

第 2、3 条对任意 Borel 有限维 `V` 上的概率律与任意代表元陈述，不依赖内禀构造；第 1、4、5
条以 `hμ : LogConcave μ` 为前提，由 `hμ.` 调用。第 6、7 条由既有
`LogConcave.intrinsicMeasure`、`convex_support`、`intrinsic_frontier_support` 与 Mathlib 的
`Measure.isClosed_support`、`measure_compl_support` 直接得到，本次实际完成证明。

### 量词与边界

- 参考测度是任意 Haar 测度 `m`，不是固定的 Lebesgue 测度；每个 `m` 有自己的 `ρ`。零维时
  `V` 为单点，Haar 测度是 Dirac 质量的正倍数，`ρ` 是正常数，Blueprint 所说的计数测度是
  其中一种。Dirac 律因此被包含，没有正维数前提。
- `Ω` 取 `interior ν.support`。Blueprint 写为支撑闭凸包的内部；第 6 条证明二者相同。
- 对数凹以 `Real.rpow` 逐点写出，允许 `ρ` 取零，`0 ^ t = 0`（`t > 0`）；`{ρ > 0}` 因而
  是凸集。与 `KLS.LogConcave` 的组合 `t • x + (1 - t) • y` 顺序一致。
- 第 3 条是紧集上的逐点双侧界，比 Blueprint 的 `ρ, ρ⁻¹ ∈ L^∞_loc(Ω)` 更强并蕴含它；
  `K = ∅` 时平凡成立。
- 第 4 条不在 Blueprint 原文中，是文献给出矩结论的实际形式，单列为库级中间目标；第 5 条
  才是节点的矩结论。没有陈述环境测度 `μ` 的矩；`Conjecture` 已把二阶矩作为前提。
- 没有假设密度、二阶矩、环境满维支撑或 raw/core agreement；没有主张 Cheeger、Dirichlet、
  谱隙或 KLS。

### 已有工具与证明边界

- `LogConcave.intrinsic_absolutelyContinuous`（已证）与 Mathlib `measurable_rnDeriv`、
  `withDensity_rnDeriv_eq`、`rnDeriv_lt_top`：给出 a.e. 密度。第 1 条的缺口是选取上半连续
  对数凹的有限值版本；`rnDeriv.toReal` 本身不具备这些性质。
- `LogConcave.exists_eventually_closedBall_le` 与 `Probability/BallDomination.lean`：小球比值
  一致有界，可用于第 2、3 条的上界与正性转移。
- Mathlib `UpperSemicontinuousOn.exists_isMaxOn`、`UpperSemicontinuousOn.bddAbove_of_isCompact`：
  第 3 条上界。开凸集上有限凹函数的连续性给下界，需要本地论证。
- Mathlib `Probability/Moments/IntegrableExpMul.lean` 的
  `integrable_pow_abs_of_integrable_exp_mul` 一族：由第 4 条推第 5 条。第 4 条本身需从
  对数凹性推指数尾，绝对连续性不够。
- Borell (1974) 原文 PDF 上一轮未能读取，本轮未再尝试；完整代表元与矩的原文段落对应仍待
  补核。这不改变 mathematics 分类。

`tasks.json` 保持 `published / missing`，证据新增本模块哈希，三条缺口改写为对应的具名
义务。验收器继续审计全部 Blueprint 锚点：本节点只锚定无占位的 `IsBorellDensity` 与第 6、7
条，五个 `sorry` 义务不进入 `\lean{}`，否则公理审计会因 `sorryAx` 失败。节点不带 `leanok`。

### ledger 与元数据

- ledger 新增 `thm:borell-logconcave-density`，`drafted / checked_by: null`，`lean_solution`
  为默认构建入口；十一个 proved 节点逐项不变。`meta.scope` 追加一句。
- `lakefile.toml` 的 Solutions 根新增 `solutions.ThmBorellLogconcaveDensity`；聚合根导入新
  模块并更新文档。
- Blueprint 定理块新增三条锚点，证明文字说明 Lean 草稿的实际范围与非主张。
- HANDOFF、`verification.md`、`solutions/README.md` 同步一段说明。`check_blueprint.CERTIFICATES`、
  golden、`STATEMENT_CHECKS` 与 `FoundationAxiomAudit` 均未改动。

## 语义对齐检查

以下对照 Blueprint 原文各子句与 `lake env lean` 打印的完整签名。

| Blueprint 子句 | Lean 对应 | 结论 |
| --- | --- | --- |
| `ν` 是有限维对数凹 `μ` 在仿射支撑方向空间 `V` 上的内禀律 | 变量 `F` 的实例集合与 `LogConcaveDensity.lean` 的 Intrinsic 节相同；`ν = ↑(Probability.intrinsicMeasure μ)`，前提 `KLS.LogConcave μ` | 一致 |
| `K_ν` 为支撑闭凸包，`Ω = int_V K_ν` | 使用 `interior (↑ν).support`；第 6 条证明 `closure (convexHull ℝ supp) = supp`，入口文件给出 `interior (closure (convexHull ℝ supp)) = interior supp` 的类型应用 | 一致，经已证恒等式 |
| 存在上半连续对数凹 Borel `ρ : V → [0,∞)` | `IsBorellDensity` 的 `measurable`、`nonneg`、`upperSemicontinuous`、`logConcave`；值域为 `ℝ`，非负性单列，有限值自动成立 | 一致 |
| `ν(V ∖ Ω) = 0` | 第 7 条 `↑ν (interior (↑ν).support)ᶜ = 0` | 一致，已证 |
| `dν = ρ dLeb_V` | `m.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) = ν`，`m` 为任意 Haar 测度 | Lean 更一般：对每个 Haar `m` 各给一个 `ρ`，Lebesgue 是其中之一 |
| `ρ > 0` 于 `Ω` | 第 2 条对任意满足 `IsBorellDensity` 的 `ρ` 成立 | Lean 更强：对所有代表元而非某一个 |
| `ρ, ρ⁻¹ ∈ L^∞_loc(Ω, Leb_V)` | 第 3 条：每个紧 `K ⊆ Ω` 上 `0 < a ≤ ρ ≤ b` | Lean 更强：逐点界蕴含局部本质有界 |
| `ν` 有各阶有限矩 | 第 5 条 `∀ p : ℕ, Integrable (fun v ↦ ‖v‖ ^ p) ↑ν`；第 4 条指数矩为附加中间目标 | 一致；第 4 条是 Blueprint 之外的更强库级陈述 |
| 零维时 Lebesgue 为单点上的计数测度，包含 Dirac 律 | 未加正维前提；零维 Haar 测度是 Dirac 质量的正倍数，计数测度在内；入口文件有 `Fin 0` 类型应用 | 一致 |

未发现 Lean 陈述弱于 Blueprint 的子句。三处差异均为 Lean 侧更一般或更强，且都在上表标明；
不需要修改 Blueprint 陈述，也不需要 `\notready`。第 4 条与环境矩的取舍已在"量词与边界"
说明。签名中 `IsBorellDensity` 的参数顺序为 `(ν m : Measure V) (ρ : V → ℝ)`，入口文件与
Blueprint 锚点按此引用。

## 本地证据

- `lake build`：默认目标通过，新模块与入口各报若干 "declaration uses sorry" 警告，预期。
- `check_ledger.py`：1 ledger、12 nodes、0 errors。`check_blueprint.py`：8 章、87 labels、
  4 active routes、0 errors。`atlas.py check`：74 数学节点、11 证书、无环。Python 测试 100 通过。
- 两条已证恒等式在入口文件有标准公理守卫；五个义务的传递公理应含 `sorryAx`，不得当作
  证明验收。
- 本记录完成后对最终工作树运行 `python3 research/verify.py`，随后 `atlas.py export` 与
  `ready`。收据的 source SHA256 记录在收据自身，不回写本文件。默认构建中的草稿 elaboration
  通过不代表五个义务已证明。本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI
  或发布。
