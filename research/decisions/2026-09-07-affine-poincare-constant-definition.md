# 仿射协方差 Poincaré 常数：定义节点的实现、语义对齐与契约证明

日期：2026-09-07（Asia/Shanghai）。基线：`575c82c` 之上的未提交工作树，紧接
[环境/内禀协方差记录](2026-09-07-ambient-intrinsic-covariance.md)。Lean/Mathlib 为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示：按 atlas `formalize`
完成 `def:affine-poincare-constant`，它是定义节点，不断言闭性、Markov 性或任何 Poincaré 结论。
本决定不做 commit、push、远端 CI 或发布。

## 节点选择

atlas 在 `lem:ambient-intrinsic-covariance` 认证后把 `def:affine-poincare-constant` 列为唯一
`verify_prerequisites` 的定义任务：其全部 `\uses` 前提都已 Lean 认证或已实现。它是
`thm:affine-covariance-relaxation-closed`、`lem:affine-poincare-translation-invariance`、
`thm:affine-isotropic-reduction` 与两个 CMH 路线节点的共同前提。

## Statement 设计

三个新模块，类型变量一律为有限维完备实内积空间、Borel、第二可数。

| 模块 | 声明 | 内容 |
| --- | --- | --- |
| [Energy/Euclidean/CovarianceGradient/Basic.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Basic.lean) | `Energy.Euclidean.covarianceGradientDensity ν g x` | `⟪Σ ∇g x, ∇g x⟫`，`Σ = Covariance.operator ν`，`∇` 为 Mathlib 典范 Hilbert 梯度（不可微点取零）；逐点非负 |
| | `Energy.Euclidean.CovarianceGradientTest ν` | 结构：`∃ K, LipschitzWith K g`、`MemLp g 2 ν`、`Integrable (covarianceGradientDensity ν g) ν` |
| | `CovarianceGradientTest.covarianceEnergy`、`toL2` | `NNReal` 能量 `∫⟪Σ∇g,∇g⟫dν` 与 `L²(ν)` 类 |
| | `Energy.Euclidean.covariancePreEnergy ν`、`covarianceRelaxation ν` | `PreEnergy (Lp ℝ 2 ν)` 及其 `sequentialRelaxation` |
| | `Energy.Affine.preEnergy μ`、`Energy.Affine.energy μ` | 在 `ν = intrinsicMeasure μ` 上的实例：`P^aff_μ`、`𝓔^aff_μ` |
| | `gradient_ae_eq_of_ae_eq`、`CovarianceGradientTest.covarianceEnergy_eq_of_toL2_eq` | 通用前提版本：支撑边界 `ν` 零测时，连续代表元的梯度 a.e. 相等，能量只依赖 `L²` 类 |
| | `CovarianceGradientTest.ae_hasGradientAt` | 通用前提版本：`ν ≪ Haar` 时测试 a.e. 可微且 `gradient` 为其导数（调用 `LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz`） |
| [Poincare/Euclidean/AffineCovariance.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/AffineCovariance.lean) | `Poincare.Affine.constant μ`、`Poincare.Affine.Holds μ C`、`holds_iff_constant_le` | `C_P^aff(μ) = L2Energy.constant ν (Energy.Affine.energy μ)` 及有限常数的序等价 |
| | `constant_eq_zero_of_subsingleton`、`constant_eq_zero_of_direction_eq_bot` | 零维方向给常数零 |
| [KLS/LogConcave/AffineCovariance.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/AffineCovariance.lean) | `hμ.intrinsic_memLp_id_two` | 内禀律有二阶矩，`Σ` 是真实协方差而非 Mathlib 的零约定 |
| | `hμ.intrinsic_ae_hasGradientAt f` | Rademacher：每个测试 `ν`-a.e. 可微，`gradient` 为导数 |
| | `hμ.intrinsic_gradient_ae_eq_of_ae_eq`、`hμ.intrinsic_covarianceEnergy_eq_of_toL2_eq` | 代表元无关性：同一 `L²(ν)` 类的连续代表元梯度 a.e. 相等，能量相等 |

两条通用引理另置：`L2.variance_eq_zero_of_subsingleton`（`L2/MeanVariance.lean`）与
`Poincare.L2Energy.constant_eq_zero_of_subsingleton`（`Poincare/L2Energy.lean`）：单点载体上任意
能量的最优常数为零。它们不放在 `Affine` 命名空间。

**主张什么。** 上表全部声明；定义对任意 Borel 概率律成立；对数凹律满足三条良定义契约；零维
常数为零；五条 StatementChecks 类型检查（展开、测试域字段、能量积分无 1/2 因子、`Fin 0`、
`ℝ` 上 Dirac 律）。

**不主张什么。** 不主张 `P^aff_μ` 的实现稠密、二次、可闭、松弛下半连续、Markov 性、松弛与原始
能量在测试上一致、平移不变性、与 `Poincare.Canonical.constant` 或 `KLS.literatureConstant`
的比较、常数有限或任何 KLS 界。这些是 Blueprint 的独立节点。

**有限范围与零维。** 空间有限维；测试全局 Lipschitz（不是局部 Lipschitz）；无二阶矩时 Mathlib
约定 `Covariance.operator ν = 0`，能量恒为零，此约定只在非对数凹律出现。零维方向空间含在每条
声明中：测试皆为常数，能量为零，常数为零；`ℝ` 上的 Dirac 律亦然。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| μ 为有限维欧氏空间上的对数凹概率律 | 定义对任意 `ProbabilityMeasure E` 给出；对数凹只在契约中使用 | Lean 更强（前提更弱），记录 |
| ν 为仿射支撑方向空间 V 上的内禀律 | `Probability.intrinsicMeasure μ` on `(affineSupport μ).direction` | 一致 |
| Σ = Cov_{μ,V} = Cov_ν | `Covariance.operator (intrinsicMeasure μ)`，即 Cov_ν；与 Cov_{μ,V} 的限制相等是已证 `operator_coe_intrinsic`，不重复陈述；对数凹时 `intrinsic_memLp_id_two` 保证它是真实协方差 | 一致 |
| 测试：全局 Lipschitz，g ∈ L²(ν)，∫⟨Σ∇g,∇g⟩dν < ∞ | 三个结构字段；有限性写成 `Integrable`，被积函数用处处定义的典范梯度 | 一致；对数凹时被积函数 a.e. 等于经典梯度表达式 |
| 实现为 L²(ν) 类 | `toL2` | 一致 |
| 能量为该积分 | `covarianceEnergy`，`NNReal`，无 1/2 因子 | 一致 |
| Borell 表示的绝对连续性与 Rademacher 使梯度 ν-a.e. 良定义 | `intrinsic_ae_hasGradientAt`（存在）与 `intrinsic_covarianceEnergy_eq_of_toL2_eq`（代表元无关）；证明只用 `intrinsic_absolutelyContinuous` 与 `intrinsic_frontier_support` | Lean 更强（同时给出代表元无关性），记录 |
| 𝓔^aff_μ := (P^aff_μ).sequentialRelaxation | `Energy.Affine.energy μ`，`rfl` 展开 | 一致 |
| C_P^aff(μ) := C_P(ν, 𝓔^aff_μ) | `Poincare.Affine.constant μ = L2Energy.constant ν (energy μ)`，`rfl` 展开 | 一致 |
| 零维时常数为零 | `constant_eq_zero_of_direction_eq_bot`；通用引理对任意能量成立 | 一致（Lean 更一般） |

未发现 Lean 弱于 Blueprint 之处。`Poincare.Affine.Holds` 与 `holds_iff_constant_le` 是 Blueprint
未列出的接口，沿用 `Canonical`/`Ambient` 常数的模式。Blueprint `\uses` 中的
`thm:borell-logconcave-density` 在 Lean 中确有使用：二阶矩契约调用其矩结论
`intrinsic_integrable_norm_pow`；a.e. 可微与代表元无关性只用到它的绝对连续性部分。

## 证明路线

- 非负性：`Covariance.operator_inner` 化为 `covarianceBilin ν v v`，Mathlib
  `covarianceBilin_self_nonneg`（无二阶矩时形式为零，仍非负）。
- Rademacher：全局 Lipschitz 蕴含局部 Lipschitz，仓库接口给出 Haar-a.e. 可微，`ν ≪ Haar`
  传递到 `ν`-a.e.，`DifferentiableAt.hasGradientAt` 给导数。
- 代表元无关：连续函数 a.e. 相等则在 `ν.support` 上相等（不等集为开零测集，
  `subset_compl_support_of_isOpen`）；`ν`-a.e. 点落在支撑内且不在边界（`support_mem_ae`、
  边界零测），闭集减边界为内部（`IsClosed.frontier_eq`），于是两函数在该点邻域相等，
  `Filter.EventuallyEq.fderiv_eq` 给 `fderiv` 相等，`gradient` 随之相等；`integral_congr_ae` 给能量相等。
- 二阶矩：`memLp_two_iff_integrable_sq_norm` 加已证的二阶矩可积。
- 零维：概率测度给出非空载体，任一 `L²` 元等于其在唯一点的取值的常数元（`Lp.ext`），
  `variance_const`；`TestFamily.constant_eq_zero_of_variance_zero`；方向 `= ⊥` 经
  `Submodule.subsingleton_iff_eq_bot` 化为单点。

## 元数据同步

- Blueprint 定义块锚定十二条声明并标 `leanok`，块尾补充 Lean 实现范围与非主张的说明；
  `\uses` 未改。定义节点不进 ledger，`check_blueprint.CERTIFICATES` 未改。
- `solutions/StatementChecks.lean` 新增五条具名检查（`affine_constant_unfold`、
  `affine_test_fields`、`affine_energy_integral`、`zero_dimension_affine_constant`、
  `ambient_dirac_affine_constant`），加标准公理守卫；另为四条对数凹契约与零维定理加守卫。
  `verify.py` 的 `STATEMENT_CHECKS` 同步为二十五条。
- tasks.json：该节点 note 改写，新增 `available` infrastructure 记录（三个新模块、
  `LipschitzApproximation.lean`、`AbsoluteContinuity.lean` 与 Mathlib `Rademacher`、`Gradient/Basic`、
  `CovarianceBilin`、`Support` 的哈希）；本次编辑触及的 `StatementChecks.lean` 与
  `L2/MeanVariance.lean` 在另两个任务记录中的哈希同步刷新。
- 聚合模块：`Poincare/Foundation.lean` 导入两个新 Energy/Poincare 模块，根模块导入对数凹契约模块，
  并改正根模块文档中"Borell 表示仍含 sorry"的过时描述。
- 当前指南同步：HANDOFF、README、`verification.md`、`solutions/README.md`、`formalization/README.md`、
  `KLS/README.md`、`KLS/LogConcave/README.md`、`Energy/README.md`、`Poincare/README.md`、
  `Poincare/Euclidean/README.md`、`naming.md`、`blueprint/README.md`。statement golden 与路线配置未动。

## 证据边界

`lake build` 通过，无新警告。最终验证收据由 `python3 research/verify.py` 在本记录及所有指南编辑
之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；
未做隔离重建、远端 CI 或发布。
