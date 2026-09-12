# 光滑梯度松弛的 Dirichlet 性：statement、语义对齐与证明

日期：2026-09-10（Asia/Shanghai）。基线：本地 `main` 提交 `5e5c704`（命名空间重构与空白清理之后），
工作树在开始时只有未跟踪的 `research/weekly/`。本地分支领先 `origin/main` 两个提交、落后三个文档提交；
用户指示不 commit、不 push。Lean/Mathlib 为 v4.33.0，Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。
用户批准从 HANDOFF 下一阶段第 1 项 "Dirichlet 见证" 开始。

## 核对与节点选择

开始前核对：默认 `lake build` 通过（3359 jobs）；2026-09-09 的收据 passed 但源码快照已因后续提交过期，
atlas 显示 "failed or stale verification"。仿射链上的节点已全部认证或记为 missing；剩余可做节点中
`thm:smooth-gradient-relaxation-dirichlet` 是 HANDOFF 明列的下一阶段工作，且所需基础设施在库内：
条件性收缩转移 `PreEnergy.RelaxedContractionBound.sequentialRelaxation_comp_le`、
`LipschitzApproximation.mollify` 及其光滑、Lipschitz 与一致逼近引理、`Energy.Dirichlet`/`NormalContraction`
定义、`SmoothGradient.relaxation_closedQuadratic`。Mathlib 已有 `LipschitzWith.compLp`（含 Lipschitz 性）、
`fderiv_comp`、`norm_fderiv_le_of_lipschitz`、`Lp.norm_le_of_ae_bound`。不需要新的 Mathlib 接口，故
`unchecked → available` 并同轮证明。

## Statement 设计

Blueprint：对每个有限维 Borel 概率律 μ，环境光滑梯度松弛是 Markov 的：L²(μ) 类的每个正规收缩使松弛能量
不增；与闭二次结构一起构成 Dirichlet 能量。Blueprint 证明标 "Open."，提示用收缩转移定理加"一致于松弛能量的
光滑逼近"。

单个新模块 [Energy/SmoothGradient/Dirichlet.lean](../../formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean)：

| 声明 | 内容 |
| --- | --- |
| `Energy.NormalContraction.smoothed φ j` | φ 在 ℝ 上以 Lebesgue 测度、半径 `radius j` 磨光 |
| `contDiff_smoothed`、`lipschitzWith_smoothed`、`norm_smoothed_sub_le`、`norm_fderiv_smoothed_le` | 磨光后光滑、仍 1-Lipschitz、与 φ 一致距离 ≤ 2·radius j、导数范数 ≤ 1 |
| `SmoothGradient.Test.norm_gradient_comp_le` | 光滑 1-Lipschitz 实函数 ψ 与光滑测试 f 复合：‖∇(ψ∘f)‖ ≤ ‖∇f‖ 逐点 |
| `SmoothGradient.Test.compSmoothed f φ j` | 复合 `φ.smoothed j ∘ f` 是光滑测试（光滑、L²、梯度平方可积） |
| `energy_compSmoothed_le`、`norm_toL2_compSmoothed_sub_le` | 复合测试能量 ≤ f 的能量；其 L² 类与 φ∘f 的类距离 ≤ 2·radius j |
| `SmoothGradient.relaxedContractionBound μ φ` | 每个实现的测试满足松弛收缩界 |
| `SmoothGradient.markovian μ`、`SmoothGradient.dirichlet μ` | `Energy.Markovian μ (relaxation μ)`、`Energy.Dirichlet μ (relaxation μ)` |
| `SmoothGradient.Intrinsic.toIntrinsicL2_compL2`、`Intrinsic.markovian`、`Intrinsic.dirichlet` | 内禀坐标与收缩交换；内禀仿射松弛（拉回到环境 L²）的 Markov 与 Dirichlet 性 |

证书 `Solutions.ThmSmoothGradientRelaxationDirichlet.certificate μ`：Markov 性、环境松弛的 Dirichlet 性、
内禀松弛的 Dirichlet 性。三个 `example`：`Fin n` 上任意正规收缩与 L² 类的收缩不等式、`Fin 0`、ℝ 上 Dirac 律。

**主张什么。** 上表全部声明与证书，对任意 Borel 概率律（含奇异律与零维）。**不主张什么。** 不主张松弛在测试上
等于原始能量（raw/core agreement）、与 Cheeger 能量或 2 Ch 的识别、任何 Poincaré 不等式、协方差加权松弛的
Markov 性、自伴生成元或谱隙。**有限范围与零维。** 空间有限维；测试全局 C∞；正规收缩按仓库定义为 1-Lipschitz
且固定 0；零维时所有类为常数，收缩不等式退化为 0 ≤ 0 但由统一证明覆盖。

## 语义对齐

| Blueprint 子句 | Lean | 结论 |
| --- | --- | --- |
| 每个有限维 Borel 概率律 μ | 任意 `ProbabilityMeasure E`，E 有限维实 Hilbert、Borel、第二可数 | 一致 |
| 环境光滑梯度松弛 | `Energy.SmoothGradient.relaxation μ` | 一致 |
| 正规收缩作用于 L²(μ) 类 | `Energy.NormalContraction`，作用 `φ.compL2 μ` 经 Mathlib `LipschitzWith.compLp`，不选代表元 | 一致 |
| 收缩使松弛能量"减少"（不增） | `Energy.Markovian`：`relaxation (φ.compL2 μ f) ≤ relaxation f` | 一致（Blueprint "decreases" 按 ≤ 理解，与 `Markovian` 定义一致） |
| 与闭二次结构一起构成 Dirichlet 能量 | `Energy.Dirichlet μ (relaxation μ)` = `ClosedQuadratic ∧ Markovian`；闭二次性来自 `thm:smooth-gradient-relaxation-closed` 的 `relaxation_closedQuadratic` | 一致 |
| 证明提示："收缩转移定理 + 一致于松弛能量的光滑逼近" | 逼近对象是收缩 φ（磨光）而非测试；复合测试能量逐点被控，L² 收敛由一致逼近给出；转移用已有 `RelaxedContractionBound.sequentialRelaxation_comp_le` | 一致（提示的具体实现） |
| （Blueprint 未列）内禀仿射松弛 | `Intrinsic.dirichlet`：`Energy.SmoothGradient.Intrinsic.energy μ` 亦为 Dirichlet | Lean 更强，记录 |

未发现 Lean 弱于 Blueprint 之处。`\uses{thm:smooth-gradient-relaxation-closed}` 在 Lean 中实际使用。
Blueprint 块尾补充了 Lean 中收缩的表达、内禀推论与"无绝对连续性前提"的说明；证明中 "Open." 删除。
`obs:dirac-raw-energy` 的 Dirac 障碍与本结论不冲突：Markov 性是松弛能量（L² 类的函数）的性质。

## 证明路线

- **磨光收缩。** `mollify volume (radius j) φ`：`contDiff_mollify`（φ 连续）、`lipschitzWith_mollify`（K = 1）、
  `norm_mollify_sub_le` 给 ‖φ_j t − φ t‖ ≤ 1·(2·radius j)；导数界由 `norm_fderiv_le_of_lipschitz`。
- **复合测试。** 光滑性 `ContDiff.comp`；L²：‖φ_j(f x)‖ ≤ ‖φ_j 0‖ + ‖f x‖（1-Lipschitz），`MemLp.of_le` 于
  常数加 ‖f‖；梯度：`norm_gradient_eq_norm_fderiv`、`fderiv_comp`、`opNorm_comp_le` 给 ‖∇(φ_j∘f)‖ ≤ ‖∇f‖，
  平方可积由 `Integrable.mono`（可测性用 `aestronglyMeasurable_gradient`）。
- **松弛收缩界。** ‖[φ_j∘f] − φ.compL2 [f]‖ ≤ 2·radius j：a.e. 逐点差是 φ_j(f x) − φ(f x)，
  `Lp.norm_le_of_ae_bound` 加概率测度 `measureUnivNNReal = 1`；`radius → 0` 给 L² 收敛；
  逼近序列的能量 liminf ≤ energy f（`liminf_le_liminf` + `liminf_const`）。
- **转移。** `φ.compL2 μ` 连续（`lipschitzWith_compLp`），`sequentialRelaxation_comp_le` 由松弛的下半连续性
  推到全部 L² 类。
- **内禀。** `toIntrinsicL2 μ (φ.compL2 f) = φ.compL2 (toIntrinsicL2 f)`：两边 a.e. 等于 v ↦ φ(f(reconstruct v))
  （`Lp.coeFn_compMeasurePreserving`、`quasiMeasurePreserving.ae_eq_comp`、`coeFn_compL2`），`Lp.ext`；
  再用环境版本于内禀律。

坑：`RelaxedContractionBound.sequentialRelaxation_comp_le` 的点记法会把参数错位，需显式写 `PreEnergy.` 全名
并把 `preEnergy μ` 作为首参数；`(x : Measure _)` 的强制转换目标仍需写全类型；section 变量在不同定理中的
使用不一致时用 `omit ... in` 而不关闭 linter（遵循 2026-09-08 命名整理的作用域规则）。

## 元数据同步

- ledger 新增 `thm:smooth-gradient-relaxation-dirichlet`（proved / lean，`kind: lemma` 按仓库遗留规则），
  十八个 proved 节点；`check_blueprint.CERTIFICATES` 新增映射；lakefile `Solutions` 根新增证书模块；
  `Poincare/Foundation.lean` 导入新模块（根聚合经 Foundation 导入）。
- Blueprint 定理块锚定十三条声明与证书，声明与证明标 `leanok`；`\uses` 未改。route-composition.yaml 没有该节点
  的 claim，`check_blueprint` 通过。
- tasks.json：节点改为 `available`，登记新模块与 `Energy/Dirichlet.lean`、`Relaxation/Contraction.lean`、
  `LipschitzApproximation.lean`、`SmoothGradient/{Basic,Closed}.lean`、`SmoothGradient/Intrinsic/{Basic,Closed}.lean`
  及 Mathlib `LpSpace/Basic`、`Convolution`、`FDeriv/Basic`、`FDeriv/Comp` 的哈希；既有证据哈希全部匹配。
- 当前指南：HANDOFF（新节、十八计数、表格、数学边界与下一阶段列表）、README、`verification.md`、
  `solutions/README.md`、`formalization/README.md`、`blueprint/README.md`、`Energy/README.md`、
  `Poincare/README.md`、`naming.md`、根模块与 `Foundation` 文档要点。statement golden、`STATEMENT_CHECKS`、
  路线配置未动。

## 证据边界

`lake build` 通过（3361 jobs），证书与十一条库级声明有标准公理守卫；`check_ledger`、`check_blueprint`、
`atlas check` 与 100 项 Python 测试通过。最终验证收据由 `python3 research/verify.py` 在本记录及所有指南编辑之后
生成，其源码 SHA 记录在收据自身，不写回本文件。本地 kernel 重放信任第三方编译导入；未做隔离重建、远端 CI、
commit 或 push；本地与远端分支的分叉（本地两个重构提交、远端三个文档提交）留待用户处理。
