# 环境与内禀协方差：statement、语义对齐与证明

日期：2026-09-07（Asia/Shanghai）。基线：`0451f2e` 之上的未提交工作树，紧接
[Borell 密度证明记录](2026-09-07-borell-density-proofs.md)。Lean/Mathlib 为 v4.33.0。用户指示：
"按照我们的 Blueprint 接着跑，然后优化你刚刚的发现"。本决定不做 commit、push、远端 CI 或发布。

## 先完成的接口优化

上一记录的审查发现下游 `lem:covariance-core-closure` 的证明文字使用"ρ 在 Ω 上连续"，而该事实
只出现在证明内部。现在导出为 `IsBorellDensity.continuousOn_interior_pos`（正性集内部）与
`IsBorellDensity.continuousOn_interior_support`（支撑内部），`exists_bounds_of_isCompact` 改为
调用后者；证书文件加对应公理守卫，模块文档同步。没有改变任何已证声明的陈述。

## 节点选择

atlas 在 Borell 定理认证后显示 `lem:ambient-intrinsic-covariance` 是唯一只依赖已证定义的
`inspect_infrastructure` 叶节点，且它是 `def:affine-poincare-constant` 的最后一个未认证前提。
`lem:relative-perimeter-smoothing` 与 `lem:covariance-core-closure` 涉及磨光与分布论闭性，
留作后续。

## Statement 设计

模块 [Probability/IntrinsicCovariance.lean](../../formalization/FunctionalInequalities/Probability/IntrinsicCovariance.lean)。
类型变量：`E` 有限维完备实内积空间，Borel、第二可数；`V := (affineSupport μ).direction`；
`ν := intrinsicMeasure μ`；前提 `hμ : MemLp id 2 μ`。`Covariance.operator` 是 Mathlib
`covarianceBilin` 的 Riesz 表示，已有定义，未改动。

| 声明 | 内容 |
| --- | --- |
| `Probability.integral_id_mem_affineSupport` | 重心属于仿射支撑 |
| `Probability.intrinsicMap_ae_eq_orthogonalProjection` | 内禀坐标 a.e. 等于位移到支撑点后的正交投影 |
| `Probability.memLp_id_two_intrinsicMeasure` | 内禀律保持二阶矩 |
| `Covariance.operator_apply_eq_zero_of_mem_orthogonal` | 环境协方差算子在 `Vᗮ` 上为零 |
| `Covariance.covarianceBilin_intrinsic` | 内禀协方差双线性形式等于环境形式在 `V` 上的限制 |
| `Covariance.operator_coe_intrinsic` | 环境算子在 `V` 上等于内禀算子（嵌回 `E`） |
| `Covariance.opNorm_operator_intrinsic` | 两个算子范数相等 |
| `Covariance.intrinsic_operator_inner_self_pos` | 内禀协方差正定 |
| `Covariance.operator_eq_zero_of_direction_eq_bot` | 零维方向给出零环境算子 |

二阶矩前提必须显式：Mathlib 约定无二阶矩时 `covarianceBilin = 0`，否则陈述会空洞。
证书 `Solutions.LemAmbientIntrinsicCovariance.certificate` 把五项结论一次打包，零维情形同时
给出内禀算子为零。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| μ 有限二阶矩的 Borel 概率律，A = a + V 仿射支撑 | `hμ : MemLp id 2 μ`，`affineSupport μ`、其 `direction` | 一致 |
| Cov_{μ,V} 是内禀律在 V 上的协方差算子 | `Covariance.operator (intrinsicMeasure μ)` | 一致 |
| Cov_μ 零化 V^⊥ | `operator_apply_eq_zero_of_mem_orthogonal` | 一致 |
| Cov_μ 在 V 上限制为 Cov_{μ,V} | `operator_coe_intrinsic`，另有双线性形式版本 | 一致 |
| 算子范数相等 | `opNorm_operator_intrinsic` | 一致 |
| Cov_{μ,V} 在 V 上正定 | `intrinsic_operator_inner_self_pos`：对每个非零 v，⟪Σv, v⟫ > 0 | 一致 |
| 零维时两个算子与两个范数均为零 | `operator_eq_zero_of_direction_eq_bot` 加证书中内禀算子为零；范数为零是推论 | 一致 |

未发现 Lean 弱于 Blueprint 之处。范数用 `ContinuousLinearMap` 的算子范数，与 Blueprint 的
‖·‖_op 相同；没有涉及最大特征值表述。

## 证明路线

- 重心在 A：`Convex.integral_mem`，A 闭且凸，μ a.e. 落在 A。零化：被积函数
  ⟪w, z − m⟫⟪y, z − m⟫ 对 a.e. z 为零，因 z − m ∈ V 而 w ∈ V^⊥。
- 内禀坐标：对 x ∈ A，`intrinsicMap x = ⟨x − a⟩ = P (x − a)`（`starProjection_eq_self_iff`）。
  于是 ν 是 μ 经平移 `x ↦ −a + x` 再经 P 的推前；`covarianceBilin_map_const_add` 消去平移，
  `covarianceBilin_map` 与 `adjoint_orthogonalProjectionOnto` 把 P 的伴随换成包含映射。
- 算子限制与范数：y = P y + (y − P y)，第二项被零化；范数两个方向分别用
  `opNorm_le_bound`、`le_opNorm` 与 `norm_orthogonalProjectionOnto_apply_le`。
- 正定：`covarianceBilin_self` 化为方差；方差为零则 `evariance_eq_zero_iff` 给 ⟪v,·⟫ a.e. 常数；
  该常数超平面作为 `AffineSubspace.mk'` 闭集承载 ν，`affineSupport_le_of_ae_mem` 与
  `affineSupport_intrinsicMeasure = ⊤` 迫使 (span{v})^⊥ = ⊤，故 v = 0。
- 零维：⊥^⊥ = ⊤，归结为零化。

## 元数据与证据

ledger 新增 `proved / lean` 节点（十三个 proved）；`check_blueprint.CERTIFICATES` 新增映射；
Blueprint 引理块锚定六条声明与证书，声明与证明标 `leanok`，证明文字改为实际论证；
tasks.json 该节点 infrastructure 改为 `available` 并登记源码与 Mathlib 文件哈希；HANDOFF、
README、`verification.md`、`solutions/README.md`、`formalization/README.md` 同步。golden、
`STATEMENT_CHECKS`、路线配置未动。

`lake build` 通过；证书与九条库级声明有标准公理守卫。最终验证收据由 `python3 research/verify.py`
在本记录之后生成，源码 SHA 记录在收据自身。本地 kernel 重放信任第三方编译导入；未做隔离
重建、远端 CI 或发布。
