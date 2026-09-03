# Codex 后续工作上下文：有限张量化验收之后

> 本文件记录当前交付状态与后续边界，替代已完成的 CI、ledger 生命周期和张量化骨架工作包。
> 早期阶段的决定与验证结果保留在 `research/decisions/` 和 `research/explorations/` 的
> 历史记录中。新工作继续采用陈述审查、人工冻结、独立证明与验收的流程。

## 1. 仓库现状

- 仓库：`numina-functional-inequalities/kls-lean`；伞形 Issue #1。
- Issue #2 已完成，节点 `lem:linear-test-lower` 为 `proved` / `checked_by: lean`。
  其证书同时覆盖可容许测试函数的 Rayleigh 下界与有限第二矩下的
  $C_P(\mu) \ge \lambda_{\max}(\operatorname{Cov}_\mu)$，包括零维约定。
- Issue #6 的两因子张量化证明、正式证书、语义审查和验收已完成；节点
  `lem:poincare-tensorization` 为 `proved` / `checked_by: lean`。
- Issue #7 的有限乘积张量化、反向界与最优常数等式已完成人工确认和最终语义验收；节点
  `lem:poincare-finite-tensorization` 为 `proved` / `checked_by: lean`。唯一节点证书为
  `Solutions.LemPoincareFiniteTensorization.certificate`。
- `research/decisions/2026-09-03-tensorization-freeze.md` 记录人工验收、完整公开签名及
  ledger 陈述；`research/explorations/2026-09-03-tensorization-acceptance.md` 记录文献对应、
  语义审查、验证证据与最终发布/CI 状态。是否已发布、远端 CI 是否通过，以该记录及对应
  commit 的实际结果为准。
- Issue #7 的批准签名与完整 ledger 陈述见
  `research/decisions/2026-09-03-finite-tensorization-freeze.md`；最终语义复核和验证记录见
  `research/explorations/2026-09-03-finite-tensorization-acceptance.md`。最终发布 SHA 和同一
  commit 的 CI 结果记入 [Issue #7](https://github.com/numina-functional-inequalities/kls-lean/issues/7)，
  不以早先的构建或 CI 成功替代本次发布验证。
- `.github/workflows/lean.yml` 已存在，执行 ledger checker、Python 回归测试与默认 Lean
  build，并使用 Mathlib cache。无需重复创建 CI。
- Lean 工程在 `formalization/`，Lean/Mathlib 固定为 `v4.33.0`；必须先阅读
  `LEAN_DESIGN.md`。

## 2. 已交付的二因子与有限张量化接口

乘积空间采用 `WithLp 2 (E × F)` 的 Hilbert 范数，乘积测度为

```lean
Poincare.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)
```

普通 `E × F` 的最大值范数保持原样。两个公开结果为：

- `FunctionalInequalities.Poincare.Holds.prod`：由 `Poincare.Holds μ C` 与
  `Poincare.Holds ν C'` 得到 `Poincare.Holds (Poincare.prodMeasure μ ν) (max C C')`。
- `FunctionalInequalities.Poincare.constant_prod_le`：对 Borel 概率测度，
  $C_P(\mu\otimes\nu) \le \max(C_P(\mu),C_P(\nu))$，以 `ENNReal` 表述并包括 `⊤`。

环境为实可分 Hilbert 空间，不要求第二矩、密度、正维数、最优常数有限或下确界达到。
`solutions/LemPoincareTensorization.lean` 直接组合这两项通用结论，形成默认 Lake target
中的唯一节点证书；同文件用精确类型应用检查任意自然数维度的 Euclidean 特例，包括零维。

可复用中间结果位于 `formalization/FunctionalInequalities/Poincare/Product/`：

- `Geometry.lean`：概率测度搬运、截面光滑性、梯度分量及平方范数分解。
- `Variance.lean`：L² 截面、边际积分的 L²、全方差公式和两因子方差上界。
- `Admissible.lean`：a.e. 截面可容许性、分量梯度能量可积及能量分解。
- `Tensorization.lean`：固定常数与最优常数的两个公开证明。
- `Reverse.lean`：坐标反向界与最优常数等式；保留两个因子分别为概率测度的假设。

Issue #7 进一步交付：

- 二因子等式 `constant (prodMeasure μ ν) = max (constant μ) (constant ν)`。
- 依赖有限乘积 `PiLp 2 E` 与测度
  `piMeasure μ := (Measure.pi μ).map (WithLp.toLp 2)`。
- 对 `C : ι → NNReal`，`Holds.pi` 将各因子的有效常数合并为
  `((Finset.univ.sup C : NNReal) : ℝ)`；`Holds.of_pi` 给出坐标反向界。
- 最优等式 `constant (piMeasure μ) = ⨆ i, constant (μ i)`，在 `ENNReal` 中包含 `⊤`。
  空族的固定／最优常数均为零，也覆盖单因子、混合零维和全部零维情形。
- `Poincare/Transport.lean` 提供等距伴随投影的测试提升及线性等距同构搬运；
  `Poincare/FiniteProduct/Geometry.lean` 提供依赖重编号和 `none, tail` 顺序的 Option 分解。
  相应范数与概率测度均保持一致。

二因子、有限乘积和边界结论直接组合成
`solutions/LemPoincareFiniteTensorization.lean` 的唯一 certificate。同文件保留包含搬运
引理在内的 45 项通用接口检查、八类 Euclidean 陈述应用及六个具体边界应用。

## 3. 必须保留的语义契约

- `Poincare.Admissible μ f` 是**全局光滑、L²、平方梯度可积**的实值测试函数类。
  本轮没有证明它与闭 Dirichlet 域、Sobolev 域或全部局部 Lipschitz 测试类的等价性。
- `Poincare.energy μ f` 使用 Mathlib 的 canonical gradient，论文归一化为
  $\operatorname{Var}_\mu(f) \le C\int\lVert\nabla f\rVert^2\,d\mu$。
- `Poincare.Holds μ C` 同时记录概率归一化、常数非负和全部可容许测试的不等式。
- `Poincare.constant μ : ℝ≥0∞` 对有限非负有效常数取下确界；无有限常数时为 `⊤`。
- 截面的 L² 与有限能量只在 a.e. 意义下成立。证明不对边际积分求导，也不假定每个截面
  都可容许。处理实值积分时必须保留必要的可积性证据。
- 现有 `Poincare.rayleigh`、`Poincare.linearTest`、centered `Covariance.operator`、
  `Covariance.rayleighMax` 与 `Covariance.lambdaMax` 的定义和 Issue #2 证书保持有效。

BGL §4.3 Proposition 4.3.1 提供张量化的文献对应；本仓库的具体测试类与其 Dirichlet 域
框架的区别记录在 `research/explorations/2026-09-03-tensorization-source-alignment.md`。
上游手稿 `prop:products` 使用有限多因子版本，并另需一维对数凹界与 Cheeger–Poincaré
比较。当前已交付二因子与有限乘积张量化及最优等式；它们只是完整乘积 KLS 论证的
组成部分，一维对数凹界、Cheeger–Poincaré 比较及随机局部化部分仍需独立完成。

## 4. 验收与工作流程

从仓库根目录执行：

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

三项已证节点都必须通过证书及其本地 imports 的禁用 token 检查。机器编译之外，还要
检查公开定理和证书的传递公理依赖，并核对签名与 ledger 陈述是否符合人工批准快照。
结构 checker 只验证当前元数据，不证明历史审批或数学语义。

工作直接在 `main` 上进行，遵循 `research/explorations/2026-09-03-main-only-workflow.md`。
未完成工作保留为本地修改；完成验收后按用户授权直接发布到 `origin/main`，不新建 feature
branch 或 PR。不得用较早 commit 的 CI 结果代替最终发布 commit 的结果。

未来节点遵循 `drafted → frozen → proved`：人工批准完整陈述后冻结，独立证明阶段保留
其公开签名和语义定义。若需要改变冻结陈述，在新 exploration 中记录问题供人工处理。
历史 decision/exploration 不改写；状态变化追加新记录。

## 5. 后续独立任务

建议下一独立任务是**一维 Gaussian Poincaré 锐常数**，目标候选为
`Poincare.constant (gaussianReal m v) = (v : ENNReal)`。先审查本仓库精确测试类、
`gaussianReal` 的方差参数约定、Mathlib API 与上界证明路线，再由人类冻结陈述；下界可
考虑复用已有线性测试结论。本文件没有声称该后续 Issue 已创建或证明已经开始。

其余路线分别为：

1. **乘积情形 KLS**：复用已交付的有限乘积与反向界／等式，独立证明一维对数凹
   Poincaré 界，再结合 Cheeger–Poincaré 比较连接手稿 `prop:products`。
   随机局部化部分仍是独立任务。
2. **多元 Gaussian 与仿射推前**：从一维结果、有限乘积张量化和仿射推前界获得
   $C_P(\gamma)=\lambda_{\max}(\Sigma)$。
3. **Log-Sobolev 与 Bakry–Émery**：分别审查并冻结 LSI 定义、Gaussian LSI 与强凸性界。

闭 Sobolev/谱隙等价、完整 optimal transport、Otto–Villani、Γ₂ calculus 和 KLS
随机分析主干不属于本次张量化验收范围。

## 6. 本次有限乘积验收记录（2026-09-03）

用户“我觉得OK了，你最后再检查一下语义是否对齐，我们就可以开始下一步了”作为本次
人工验收确认；最终独立语义复核确认实现与 ledger 对齐。完整批准签名和 ledger 快照
保存在 `research/decisions/2026-09-03-finite-tensorization-freeze.md`，证书覆盖、签名比较、
传递公理与构建证据汇总在
`research/explorations/2026-09-03-finite-tensorization-acceptance.md`。

Issue #7 已存在并挂在 #1 下，勿重复立项。#2、#6 的通用证明、定义、冻结签名、节点陈述及
保留的两个 certificate 签名不变。#7 的唯一 certificate 直接调用已审查库；当前交付不
恢复 Project 包装层或重复声明 Euclidean 定理。最终发布 SHA 与同 commit CI 以 Issue #7
的实际记录为准。

历史去重记录 `research/explorations/2026-09-03-certificate-deduplication.md` 保存 45 项
接口及检查源码；原 53 项候选记录保留在
`research/decisions/2026-09-03-finite-tensorization-candidate.md`。
来源/API/证明路线见 `research/explorations/2026-09-03-finite-tensorization-design.md`，
实现记录见 `research/explorations/2026-09-03-finite-tensorization-proofs.md`。
这些历史文件中描述的草稿和待验收状态属于当时阶段，不覆盖本次验收记录。

## 7. 当前目录约定（2026-09-03）

可复用 Lean 模块按数学主题分组：`Poincare/` 放基本定义、线性测试和搬运接口，
`Poincare/Product/` 放二因子结果，`Poincare/FiniteProduct/` 放有限乘积结果。
`solutions/` 是唯一节点入口层；每个已证节点一个 certificate，直接引用通用库。
重复的 `Project/` 三文件已删除，Euclidean 特例采用精确类型应用检查。
完整导航与放置规则见 `formalization/README.md`。
根 aggregate `formalization/FunctionalInequalities.lean` 导入已验收的
`Poincare/Product/Reverse` 和 `Poincare/FiniteProduct/Tensorization`，默认构建包含三个
节点证书。

早先的主题目录迁移见 `research/explorations/2026-09-03-module-layout.md`；之后的
Project 去重和保留的 45 项通用接口以 `research/explorations/2026-09-03-certificate-deduplication.md`
为准。历史记录保留当时路径和声明数量，不能据此重新创建旧包装。状态不编码进目录，
完成证明后无需再次搬迁。陈述／证明分离继续由人工冻结及独立证明流程保证。
