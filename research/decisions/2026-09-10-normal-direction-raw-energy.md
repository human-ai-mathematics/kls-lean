# 法向导数的原始能量障碍 `obs:normal-direction-raw-energy`：statement、语义对齐与证明

日期：2026-09-10（Asia/Shanghai）。基线：本地 `main` 提交 `5e5c704`，工作树含同日尚未提交的 Dirichlet 见证与
一维 `12·Var` 工作。用户决定继续追系数 4（等待合作者提供 KLS 1995 原文），期间先做与该线无关的节点；
本节点是 atlas `ready` 列表中与一维常数无关、基础设施最轻的一项。用户指示不 commit、不 push。

## 节点选择与核对

`obs:normal-direction-raw-energy`（Blueprint 第 30 章 "Core and coordinate comparisons"）是障碍节点，
类型与 `obs:dirac-raw-energy` 相同：命名的库内已证结果，不进 ledger、不设证书。tasks.json 原状态
`local_argument / unchecked`。所需基础设施全部在库内：`Probability.affineSupport`、`supportPoint`、
`ae_mem_affineSupport`、`Energy.SmoothGradient.Test`/`preEnergy`、`PreEnergy.RespectsAmbientFibers`，
以及 Mathlib 的 `Submodule.orthogonal_eq_bot_iff`、`toDual_gradient`。`unchecked → available` 并同轮证明。

## Statement 设计

新模块 [Energy/SmoothGradient/NormalDirection.lean](../../formalization/FunctionalInequalities/Energy/SmoothGradient/NormalDirection.lean)，
命名空间 `FunctionalInequalities.Energy.SmoothGradient`：

| 声明 | 内容 |
| --- | --- |
| `normalCoordinate μ n x := ⟪n, x − supportPoint μ⟫` | 沿 `n` 的坐标，以选定支撑点为原点 |
| `contDiff_normalCoordinate`、`hasFDerivAt_normalCoordinate`、`gradient_normalCoordinate` | 光滑；梯度恒为 `n` |
| `normalCoordinate_ae_eq_zero (hn : n ∈ directionᗮ)` | `μ`-a.e. 为零（a.e. 点落在仿射支撑内，差向量属于方向空间） |
| `smoothTest_energy_normalCoordinate` | `Poincare.SmoothTest.energy μ u = ‖n‖²` |
| `Test.normalCoordinate hn`、`Test.toL2_normalCoordinate`、`Test.energy_normalCoordinate` | 作为光滑梯度测试：L² 类为 0，能量 `‖n‖²` |
| `exists_unit_normal (h : direction ≠ ⊤)` | 真方向空间有单位法向量 |
| `exists_test_toL2_eq_zero_energy_eq_one (h)` | Blueprint 陈述：存在测试，L² 类为 0，能量与原始能量均为 1 |
| `not_respectsAmbientFibers (h)` | `¬ (preEnergy μ).RespectsAmbientFibers` |

**主张什么。** 上表全部声明，对任意有限维实内积空间上的 Borel 概率律，只要仿射支撑的方向空间不是全空间。
**不主张什么。** 不主张内禀松弛能量的任何性质；不主张 raw/core agreement 在内禀坐标下成立或失败；
不涉及密度。**有限范围与零维。** 有限维；`direction = ⊤`（全维支撑）时无结论，也不应有；零维空间中方向空间为 ⊤，
不在前提内。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| 仿射支撑是真仿射子空间 `A = a + V` | `(affineSupport μ).direction ≠ ⊤`，`a = supportPoint μ` | 一致（真子空间等价于方向空间为真） |
| `n ∈ V^⊥` 单位向量 | `n ∈ directionᗮ`，`‖n‖ = 1`（由 `exists_unit_normal` 提供） | 一致 |
| `u = 0` in `L²(μ)` | `(Test.normalCoordinate μ n hn).toL2 = 0` 与 a.e. 零 | 一致 |
| `∫‖∇u‖² dμ = 1` | `Poincare.SmoothTest.energy μ u = 1` 与 `Test.energy = 1` | 一致 |
| "ambient raw energy depends on the extension away from A" | `not_respectsAmbientFibers` | Lean 更强：把结论表述为 `FormCore` 谓词的失败，已在 Blueprint 块中说明 |

未发现 Lean 弱于 Blueprint 之处。`\uses` 未改。

## 元数据同步

障碍节点不进 ledger、不设证书、`check_blueprint.CERTIFICATES` 不变。Blueprint 块锚定八条声明并标 `leanok`
（声明与证明）；`Poincare/Foundation.lean` 导入新模块（根聚合经 Foundation 导入）；
`solutions/FoundationAxiomAudit.lean` 新增两条公理守卫；tasks.json 节点改为 `available` 并登记模块与依赖哈希；
HANDOFF、`formalization/README.md`、`Energy/README.md`、`blueprint/README.md`、`solutions/README.md` 同步。

## 证据边界

默认 `lake build` 通过；两条守卫只依赖三条标准公理。最终收据由 `python3 research/verify.py` 在后续节点
（`thm:smooth-gradient-raw-core-agreement-density`）完成后统一生成。未 commit、未 push。
