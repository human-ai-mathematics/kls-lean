# Borell 密度表示：五条义务的证明与证书登记

日期：2026-09-07（Asia/Shanghai）。基线：`0451f2e` 之上的未提交工作树，起点为
[statement 起草与语义对齐记录](2026-09-07-borell-density-statements.md)。Lean/Mathlib 为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。用户指示："顺便把这个 sorry 给解决掉"。
本决定不做 commit、push、远端 CI 或 Pages 部署。

期间另一会话把模块重排到 `KLS/LogConcave/`，`BorellRepresentation.lean` 随之移动，见
[迁移记录](../explorations/2026-09-07-logconcave-module-layout.md)。本决定在新路径上完成证明；
statement 记录中引用的旧路径是当时的事实，不改写。

## 结果一览

| 目标 | 之前 | 现在 |
| --- | --- | --- |
| `LogConcave.exists_isBorellDensity` | `sorry` | 已证 |
| `IsBorellDensity.pos_of_mem_interior_support` | `sorry` | 已证 |
| `IsBorellDensity.exists_bounds_of_isCompact` | `sorry` | 已证 |
| `LogConcave.intrinsic_integrable_exp_norm` | `sorry` | 已证 |
| `LogConcave.intrinsic_integrable_norm_pow` | `sorry` | 已证 |
| ledger `thm:borell-logconcave-density` | `drafted / null` | `proved / lean` |
| `check_blueprint.CERTIFICATES` | 十一个映射 | 十二个映射 |
| Blueprint 该节点 | 三条锚点，无 `leanok` | 九条锚点，声明与证明均 `leanok` |

五条声明的签名与 statement 记录中的完全一致；没有改变任何前提、结论或量词。
`Solutions.ThmBorellLogconcaveDensity.certificate` 是唯一证书，一次性打包存在性、正性、紧集界、
闭凸包恒等式、内部补集零测、指数矩与各阶矩；证书文件对证书及九条库级声明加标准公理守卫。

## 证明路线

模块新增三节，均在 `FunctionalInequalities.KLS` 命名空间。

**代表元性质（`IsBorellDensity.*`）。** `convex_pos`：正性集在实幂对数凹性下凸。
`concaveOn_log`：`log ρ` 在正性集上凹。`measure_compl_pos`：`ν` 在正性集补集上为零。
`interior_support_subset`：若正性集内部为空，则它落在真仿射子空间内，Haar 零测
（`Measure.addHaar_affineSubspace`），于是 `ν = 0`，矛盾；故支撑含于正性集的闭包，
再由 `Convex.interior_closure_eq_interior_of_nonempty_interior` 得
`interior supp ⊆ interior {ρ > 0}`。正性是其推论。紧集上界来自
`UpperSemicontinuousOn.bddAbove_of_isCompact`；下界来自 Mathlib 的
`ConcaveOn.continuousOn_interior`：`log ρ` 在正性集内部连续，`ρ = exp ∘ log ρ` 在紧集上取到正的最小值。

**矩（`BorelLogConcave.*`）。** `measure_norm_ge_le`：Borell 引理。取 `t = 2/(k+1)`，
`B₀ = {‖v‖ ≥ kR}`，`B₁ = ball 0 R`，其组合落在 `(closedBall 0 R)ᶜ` 内；用已证的 Borel 集表述
（`LogConcave.borel_iff`）与 `innerMeasure_le` 得 `ν(B₀)^t · (3/4) ≤ 1/4`，再开 `1/t` 次方得
`ν(B₀) ≤ 3^{(1-k)/2}`（`k < 2` 时用 `ν ≤ 1`）。`exists_integrable_exp_norm`：由球的穷竭取
整数半径 `R ≥ 1` 使 `ν(ball 0 R) ≥ 3/4`；取 `t₀ = log 3 / (4R)`，用
`exp(t₀‖v‖) ≤ Σ_k exp(t₀(k+1)R)·1_{‖v‖ ≥ kR}` 逐点控制（`k = ⌊‖v‖/R⌋`），`lintegral_tsum`
交换后每项等于 `3^{(k+1)/4} · 3^{(1-k)/2} = 3^{3/4}·(3^{-1/4})^k`，几何级数可和，
`ENNReal.ofReal_tsum_of_nonneg` 给出有限性。`integrable_norm_pow_of_integrable_exp_norm`：
`exp(-t‖v‖) ≤ 1` 可积，Mathlib `integrable_pow_abs_of_integrable_exp_mul` 给全部矩。

**构造（`BorellRepresentation.*`，`LogConcave.exists_isBorellDensity_of_interior_support_nonempty`）。**
`radius n = 1/(n+1)`；`ballRatio n x = ν(closedBall x rₙ)/m(closedBall 0 rₙ)`，可测性由
`measurable_measure_prodMk_left`；`lowerDensity = liminf ballRatio`。三条性质：
有界，由 `LogConcave.exists_eventually_closedBall_le` 沿 `rₙ → 0⁺`；a.e. 等于
`ν.rnDeriv m`，由 `Besicovitch.ae_tendsto_rnDeriv` 与 `Measure.addHaar_closedBall_center`；
对数凹，由 `LogConcave.closedBall_mul_le`（等半径球质量的对数凹性）经
`liminf_eq_iSup_iInf_of_nat`、`ENNReal.orderIsoRpow` 与 `ENNReal.iSup_mul` 传递到下极限。
`envelope x = ⨅ n, ⨆ y ∈ ball x rₙ, lowerDensity y`：不小于 `lowerDensity`，有界，上半连续
（半径减半的球包含），对数凹（组合点仍落在同半径球内，逐 `n` 比较后取下确界），且与
`lowerDensity` 在凸正性集边界之外处处相等：闭包外两者为零；内部上 `log` 有限凹从而连续
（`concaveOn_log_toReal_of_logConcave`），包络不增大取值。凸集边界 Haar 零测
（`Convex.addHaar_frontier`），故 `withDensity` 相同，再经 `withDensity_rnDeriv_eq` 得 `ν`。
最终 `ρ = (envelope ·).toReal`：可测（上半连续）、非负、上半连续、对数凹（`toReal` 单调传递）。

内禀版本由 `hμ.intrinsicMeasure`、`interior_intrinsic_support_nonempty`、
`intrinsic_absolutelyContinuous` 和 `borel_iff` 直接实例化。零维方向空间不需特殊处理。

## 元数据同步

- ledger：节点改为 `proved / lean`，statement 改述为证书打包的七项结论，source 追加本记录。
- `check_blueprint.CERTIFICATES` 新增映射；Blueprint 定理块锚定五条定理、谓词、两条恒等式与
  证书，声明与证明标 `leanok`，证明文字改为实际论证。
- tasks.json：infrastructure 改为 `available`，gaps 清空，证据加入 `Borel.lean`、Mathlib
  `Besicovitch.lean` 与 `Convex/Continuous.lean` 并刷新全部哈希。
- 当前指南（HANDOFF、README、`verification.md`、`solutions/README.md`、`formalization/README.md`、
  `KLS/README.md`、`KLS/LogConcave/README.md`）把 drafted 描述改为 proved，证书计数改为十二。
  HANDOFF 的"未认证陈述"清单删去 Borell 表示一项，后续工作流第二项相应改写。
- statement golden、`STATEMENT_CHECKS`、`FoundationAxiomAudit` 与路线配置均未改动。

## 证据边界

证书证明的是 Blueprint 的陈述及 statement 记录中标明的三处更强形式；没有主张 Cheeger、
Dirichlet、谱隙、仿射白化或 KLS。Borell (1974) 原文 PDF 仍未读取；本地证明是从紧集约定出发的
独立论证，不依赖原文逐字对应。最终验证收据由 `python3 research/verify.py` 在本决定及所有指南
编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；
未做隔离重建、远端 CI 或发布。
