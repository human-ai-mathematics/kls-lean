# 第一批 Poincaré 比较 statement

日期：2026-09-06。用户在基础清理与严格复核后要求“按照计划开始构建下一步的
leanstatement”。本批按基础指南和 Blueprint 的顺序，先准备 ambient/intrinsic 与
legacy/relaxed 两组桥接，不开始文献前端、whitening 或长路线证明。

**状态：两个节点均为 `drafted / checked_by: null`，12 条比较定理全部保留 `sorry`。**
本记录不是 human freeze 或证明验收。起点 HEAD 为
`70ca1c19c4d207a31716c2e589c0b096521a5490`，此前未提交工作保留。

## 交付入口

- [比较阅读指南](../../formalization/FunctionalInequalities/Poincare/Euclidean/README.md)：
  先解释用途、数学范围、具体用法，再给证明路线和来源。
- [Ambient/intrinsic statement 入口](../../solutions/LemAmbientIntrinsicPoincareComparison.lean)：
  5 条声明，4 个应用检查。
- [Legacy/relaxed statement 入口](../../solutions/LemLegacyRelaxedPoincareComparison.lean)：
  7 条比较声明、原始测试族定义的检查，以及 8 个应用检查。
- [Ledger](../a-series/ledger.yaml)：两个新节点的完整数学规格与状态。

两个入口都进入默认 `Solutions` target，但没有名为 `certificate` 的新证明包装。
四个新模块按数学职责放在原 subject hierarchy 中，没有按 draft/proved 拆分文件路径：

| 模块 | 定义或 statement |
| --- | --- |
| `Poincare.Relaxation` | `TestFamily.ofPreEnergy`；`holds_ofPreEnergy_iff`；`constant_ofPreEnergy_eq` |
| `Energy.Euclidean.AffineComparison` | `SmoothGradientTest.exists_intrinsic_restriction`；`SmoothGradientTest.exists_ambient_extension`；`smoothGradientRelaxation_eq_intrinsicAffineSmoothGradientRelaxation` |
| `Poincare.Euclidean.AffineComparison` | `smoothGradientRelaxationHolds_iff_intrinsicAffine`；`smoothGradientRelaxationConstant_eq_intrinsicAffine` |
| `Poincare.Euclidean.LegacyComparison` | `holds_iff_smoothGradientPreEnergy`；`holds_iff_smoothGradientRelaxation`；`constant_eq_smoothGradientRelaxation`；`holds_iff_intrinsicAffineSmoothGradientRelaxation`；`constant_eq_intrinsicAffineSmoothGradientRelaxation` |

模块中的声明沿用 `FunctionalInequalities` 根命名空间。`ofPreEnergy` 是直接构造的定义，
不含占位证明；其余 12 条 theorem 是待证明的候选接口。

## 数学一般性与语义核对

### 抽象比较

`TestFamily.ofPreEnergy μ P` 使用 `P.Test`，方差取 `L2.variance μ (P.toAmbient f)`，
能量取 `P.energy f`。`μ` 可以是任意可测空间上的概率律，`P` 可以是任何已有 `PreEnergy`
接口在其实 `L²` 上的实例。

比较有限常数时始终使用 `C : NNReal`，relaxed 不等式只在有限能量域量化。
relaxation 在具体测试上不增能量，给出一个方向。反向可在每个有限能量点用现有 finite
recovery theorem 和方差连续性。故不需要 dense realization、二次性、Markov 性、
raw/core agreement 或原始能量在 realization fibers 上一致。

该路线保留 `C = 0`，不在无限能量点操作 `0 * infinity`；也无需假设最优测试存在。
空测试类仍适用：原始不等式真空成立，relaxation 的有限域为空。常数相等是 `ENNReal`
等式，无穷值不被转为实数。

### 坐标比较

`E` 为任意有限维 complete real inner product space，带 Borel measurable structure 和
second-countable norm topology，`μ : ProbabilityMeasure E` 任意。不增加二阶矩、密度、
log-concavity、正维或 covariance 非退化假设。

restriction statement 明确给出沿 `Probability.reconstruct μ` 的逐点函数限制、
`toIntrinsicL2` 下的 realization 等式及原始能量不等式。extension statement 只要求存在
一个限制正确、realization 正确且原始能量相同的全局光滑测试，不预先固定 helper 的
实现。证明应使用 affine support 的正交投影；现有 `intrinsicMap` 的支撑外分支仅可测，
不能拿来充当全局光滑延拓。

最终能量等式位于同一个原始 `L²(μ)` 载体上，并量化全部元素，包括无限能量点。
它没有错误地宣称每个 ambient 原始测试的法向能量等于其限制的能量。由此比较两种
relaxed 常数时方差不变，也无须偷偷添加坐标原点无关性或 raw/core 假设。

### Legacy 前端

两类原始测试均要求普通 `ContDiff ℝ ∞`、`MemLp f 2 μ` 和平方梯度可积。
`L2.variance_toLp` 对齐方差，两侧的有限梯度积分相同。旧的 `Holds` 使用 `(C : ℝ)`，
新的有限常数使用 `C : NNReal`；旧接口的非负性由该显式类型提供。

所有归一化均为 `Var ≤ C ∫ ‖gradient‖²`，没有额外的因子二。由有效有限常数集合相等
得到最优常数等式，不需要旧 infimum 的 attainment 假设。

## 来源与 Blueprint 对应

| 本地 Blueprint 节点 | 新 Lean 映射 |
| --- | --- |
| `thm:ambient-intrinsic-relaxation-equality` | `Energy.Euclidean.smoothGradientRelaxation_eq_intrinsicAffineSmoothGradientRelaxation` |
| `cor:ambient-intrinsic-constant-equality` | `Poincare.Euclidean.smoothGradientRelaxationConstant_eq_intrinsicAffine` |
| `thm:legacy-relaxed-holds-equivalence` | `Poincare.Euclidean.holds_iff_smoothGradientRelaxation` |
| `thm:legacy-canonical-constant-comparison` | `Poincare.Euclidean.constant_eq_intrinsicAffineSmoothGradientRelaxation` |

这些桥接的精确数学范围和证明路线来自本地 Blueprint chapters 30、45。抽象 pre-energy
版本及两个测试操作是为后续证明提炼的本地接口，没有将其归给某篇未经核对的论文。

本次重新读取历史固定版本
`kls-exploration@cd4a894a0faf40c0180f80b1a31eec1fdb6cb576` 的
`modules/01-definitions.tex`：lines 17–25 的 Definition 2.1 提供 variance/gradient
归一化；lines 6–15 的上下文是 `exp(-U)` 密度及 Langevin generator。它不直接提供本批
任意 Borel 概率下的全部前端等价或 spectral-gap 识别。当前长路线 source pin 未改动。

Blueprint 只增加四个 `lean` 声明链接，保留对应的 `notready`，不添加 `leanok`。
原有侧车路线状态和数学依赖未升级。

## 范围与后续工作

本批不定义 locally Lipschitz 文献常数、log-concave law、isotropic law 或 KLS 主命题，
也不证明 Dirichlet、Cheeger、raw/core、whitening 或任何长路线结论。先接通已有前端，
可以让后续 KLS statement 使用一个清楚的常数接口，同时保留它与文献前端的显式边界。

Gaussian 应用全部只是候选接口调用检查。旧 Gaussian 证书仍已证明；经本批草案转到
所选常数的结论仍依赖 `sorryAx`，不能记为新的 Gaussian 认证。

本次仅扩展 statement 层，不自动冻结接口。后续证明按已经声明的假设和结论实施；若
审阅发现应调整接口，则继续保留草案并追加决策，不回写此前的 freeze 或验收历史。

## 验证材料

本批工作使用的临时快照与完整日志位于：

```text
/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-bridge-statements-20260906-s5zdn3p8/
```

两个 ledger statement 字符串的 SHA-256（UTF-8，无附加换行）：

```text
ambient/intrinsic ddb7b7ddcb37690e392fbc9e8f27f323fbe1da0849e687fae48697eab7e0ecd7
legacy/relaxed    9ab94cdb9d87ca092f141a4f724003475e00b139a6ff03b97eab9eb83af6487a
```

## 最终本地验证

| 检查 | 结果 |
| --- | --- |
| 四个新增模块与两个 statement 入口 | 全部编译成功 |
| 默认 `lake build` | 成功，3240 jobs；仅有 12 条预期的占位证明 warning |
| 入口中的具体应用 | 12 个全部通过，包括零维、空测试类、Dirac、Gaussian 和无穷常数 |
| 指南中的 Lean 代码块 | 单独用 `warningAsError=true` 检查通过 |
| Ledger | 6 nodes：4 proved、2 drafted；0 errors |
| Blueprint | 73 labels、4 active routes；0 errors |
| Python tests | 63 项通过 |
| Blueprint PDF、web、checkdecls | 全部成功；四个新声明链接可解析 |
| 最终 PDF | 27 页；检查物理页 13、16，修改段落无溢出、裁切或重叠 |
| 最终 TeX 日志 | 无 overfull、undefined references/citations 或重复 label；8 条 underfull |
| 修改文档的本地链接 | 全部存在 |
| `git diff --check` | 通过 |

内部表达式比较复用严格复核留下的当前基线：原有 691 个项目声明的类型、宇宙参数、
可归约定义体及传递公理全部相同，无声明删除。新增 15 个内部声明分别是 12 条候选定理、
`ofPreEnergy` 定义及 Lean 为该定义生成的两个证明辅助项。仅这 12 条候选定理依赖
`sorryAx`；没有新增 unsafe 或 partial 声明。

源码 import 闭包检查确认：root aggregate、`Poincare.Foundation` 和四份已证明证书均
不依赖这四个草案模块。四个已证明 ledger 对象、全部旧证书与两份公理 audit 文件均保持
原样。所有 `leanok` 和 `notready` 标记按 Blueprint 节点比较不变。

完整证据在临时目录的 `lake-build.log`、`declaration-comparison.json`、
`import-boundaries.json`、`guide-example.log` 和 `blueprint-build-final.log`。
本次未 commit、push、执行远程 CI 或改变既有历史记录。
