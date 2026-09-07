# Borell 等价证明完成与 conditional-fiber 六合同证明

日期：2026-09-07（Asia/Shanghai）。基线：`0451f2e` 之上的未提交工作树，起点为
[证明交接决定](2026-09-07-borell-equivalence-claude-handoff.md)。Lean/Mathlib 仍为 v4.33.0，
Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。本次由 Claude 按交接完成七个 `sorry`，
没有更改任何已证声明的数学内容、路线配置或历史决定文件。本决定不做 commit/push、远端 CI
或 Pages 部署。

## 结果一览

| 目标 | 之前 | 现在 |
| --- | --- | --- |
| `KLS.LogConcave.borel_iff` | `sorry` | 已证；由 `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate` 包装 |
| ConditionalFiber 六个合同 | 六个 `sorry` | 全部已证；定义节点获得 `\leanok` |
| ledger | 十个 proved + 一个 drafted | 十一个 proved，`checked_by: lean` |
| `check_blueprint.CERTIFICATES` | 十个映射 | 十一个映射 |
| `atlas.py check` | 通过 | 通过：74 个数学节点、11 个证书、无环 |
| Python 测试 | 100 通过 | 100 通过 |
| 默认 `lake build` | 通过（含 `sorryAx`） | 通过，新增公理守卫全部为标准三公理 |

## Borell 等价：实际证明路线

[LogConcaveBorel.lean](../../formalization/FunctionalInequalities/KLS/LogConcaveBorel.lean)
新增五个具名辅助结论，然后证明主定理：

- `innerMeasure_mono`、`innerMeasure_le`、`le_innerMeasure_of_isCompact`：内测度单调，
  不超过原测度，且每个紧子集给出下界。这些不需要有限维或 Borel 结构。
- `innerMeasure_eq_of_measurableSet`：在 `InnerRegular` 测度的可测集上内测度等于测度，
  直接由 `MeasurableSet.measure_eq_iSup_isCompact` 给出，二者的上确界形状逐字一致。
- `isCompact_combination`、`combination_mono`：两个紧集的 Minkowski 组合是紧积集在
  `(x,y) ↦ t•x + (1-t)•y` 下的连续像，因而紧；组合对两个集合单调。
- `LogConcave.borel_iff`：Borel 方向到紧集方向由紧集可测和 `innerMeasure_le` 得到。
  反方向先用内正则把两个 Borel 质量写成紧子集上确界，再用
  `ENNReal.orderIsoRpow` 的 `map_iSup` 与 `ENNReal.iSup_mul`/`mul_iSup` 把幂与乘积
  换到上确界内部，最后对每一对紧子集应用紧集不等式并用紧组合作为内测度下界。
  空紧集处理零质量；有限维仅用于内正则实例，零维空间包含在内。

证书文件提供唯一 `certificate`，附带 `Fin n`、`Fin 0` 与单向推论的类型检查，并对
`certificate`、`borel_iff`、`innerMeasure_eq_of_measurableSet`、`isCompact_combination`
加标准公理守卫。

## Conditional-fiber：六个合同的证明

[ConditionalFiber.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber.lean)
的定义未改动。新增辅助对象：`reconstruct_coordinates`（重构与坐标互逆），`baseMap` 及
`baseLaw_eq_map`（基律是 `ρ ⊗ μ` 经基投影的推前），`compProd_baseLaw_kernel`
（`Measure.disintegrate` 的本地名字），`memLp_id_two_iff`/`memLp_id_two_iff'`
（二阶矩有限的 lintegral 表述），`instIsProbabilityMeasureBaseLaw`，以及
`fiberEnergy_congr_kernel`、`fiberEnergy_congr_ae`、`ae_fiber_congr`。

| 合同 | 证明要点 |
| --- | --- |
| `lintegral_baseLaw` | `lintegral_map` 到 `ρ ⊗ μ`，Tonelli（`lintegral_prod`），再对每个方向反向 `lintegral_map` |
| `ae_memLp_id` | 条件二阶矩的基律积分经 `Measure.lintegral_compProd` 与分解恒等式等于联合律下 `‖⟨x,θ⟩‖²` 的积分，用 `‖θ‖=1` 控制为 `∫‖x‖²dμ < ∞`；`ae_lt_top` 给出 a.e. 有限 |
| `measurable_fiberEnergy` | 条件均值用 `StronglyMeasurable.integral_kernel_prod_right'`，条件方差和条件二阶矩用 `Measurable.lintegral_kernel_prod_right'`；`GoodFiber` 集写成三个可测集之交；`Measurable.ite` 与 ENNReal 除法 |
| `energyWith_eq` | `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd` 给出 a.e. 核相等，`fiberEnergy` 只通过 `κ b` 依赖核 |
| `energy_congr_ae` | `f ≠ g` 的重构原像在联合律下的质量等于 `μ{f ≠ g} = 0`（`ae_map_iff`、`Measure.snd_prod`），再经分解恒等式与 `ae_ae_of_ae_compProd` 得到 a.e. 纤维上的 a.e. 相等，`evariance_congr` 结束 |
| `form_toLp` | `Lp.stronglyMeasurable`、`Lp.memLp`、`MemLp.coeFn_toLp` 代入 `energy_congr_ae` |

`energy_congr_ae` 的两个 `MemLp` 前提在证明中未被使用，签名保留原状并以下划线命名
（`_hf₂`、`_hg₂`）表明这一点；结论对所有可测代表元成立，L² 上下文由 `form_toLp` 使用。
六个合同在 `solutions/StatementChecks.lean` 末尾获得标准公理守卫。

## 元数据同步

- Blueprint：`thm:compact-borell-logconcavity-equivalence` 的 `\lean` 增加证书声明，
  声明与证明均标 `\leanok`，证明文字改为实际论证；`def:conditional-fiber-form` 标
  `\leanok` 并把“草稿占位”文字改为六个合同的实际内容。
- ledger：Borell 节点改为 `proved / lean`，statement 去掉“包含 sorry”的句子并记录证书。
  没有为 conditional-fiber 新增 ledger 节点：定义不是 proved 定理。
- tasks.json：Borell 节点证据新增 `LogConcaveBorel.lean` 与证书文件，刷新
  `StatementChecks.lean` 哈希；conditional-fiber 的 infrastructure 由 `missing` 改为
  `available`，gaps 清空，刷新 `ConditionalFiber.lean` 哈希。
- 当前指南（HANDOFF、solutions/README、verification.md、两个 README）的证书计数改为十一。

## 证据边界

密度表示节点 `thm:borell-logconcave-density`、`lem:conditional-fiber-form` 及其下游
没有获得新证明；本决定只解除 Borell 等价与 conditional-fiber 定义两个根因的 `sorry`。
Borell (1974) 原文的读取限制不变。最终验证收据由 `python3 research/verify.py` 在本决定及
所有指南编辑之后生成，其源码 SHA 记录在收据自身，不写回本文件。
