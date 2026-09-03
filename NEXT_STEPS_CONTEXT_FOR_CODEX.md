# Codex 后续工作上下文：张量化证明与验收之后

> 本文件记录当前交付状态与后续边界，替代已完成的 CI、ledger 生命周期和张量化骨架工作包。
> 早期阶段的决定与验证结果保留在 `research/decisions/` 和 `research/explorations/` 的
> 历史记录中。新工作继续采用陈述审查、人工冻结、独立证明与验收的流程。

## 1. 仓库现状

- 仓库：`numina-functional-inequalities/kls-lean`；伞形 Issue #1。
- Issue #2 已完成，节点 `lem:linear-test-lower` 为 `proved` / `checked_by: lean`。
  其证书同时覆盖可容许测试函数的 Rayleigh 下界与有限第二矩下的
  $C_P(\mu) \ge \lambda_{\max}(\operatorname{Cov}_\mu)$，包括零维约定。
- Issue #6 的两因子张量化证明已完成，本轮同步正式证书、语义审查和验收记录；节点
  `lem:poincare-tensorization` 为 `proved` / `checked_by: lean`。
- `research/decisions/2026-09-03-tensorization-freeze.md` 记录人工验收、完整公开签名及
  ledger 陈述；`research/explorations/2026-09-03-tensorization-acceptance.md` 记录文献对应、
  语义审查、验证证据与最终发布/CI 状态。是否已发布、远端 CI 是否通过，以该记录及对应
  commit 的实际结果为准。
- `.github/workflows/lean.yml` 已存在，执行 ledger checker、Python 回归测试与默认 Lean
  build，并使用 Mathlib cache。无需重复创建 CI。
- Lean 工程在 `formalization/`，Lean/Mathlib 固定为 `v4.33.0`；必须先阅读
  `LEAN_DESIGN.md`。

## 2. 已交付的张量化接口

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
`Project/PoincareTensorization.lean` 包装两项结论并给出自然数维度 Euclidean 特例，
包括零维；`solutions/LemPoincareTensorization.lean` 是默认 Lake target 中的正式薄证书。

可复用中间结果分布在：

- `ProductGeometry.lean`：概率测度搬运、截面光滑性、梯度分量及平方范数分解。
- `ProductVariance.lean`：L² 截面、边际积分的 L²、全方差公式和两因子方差上界。
- `ProductAdmissible.lean`：a.e. 截面可容许性、分量梯度能量可积及能量分解。
- `Tensorization.lean`：固定常数与最优常数的两个公开证明。

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
比较。本轮仅交付二因子 Poincaré 上界。

## 4. 验收与工作流程

从仓库根目录执行：

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

两项已证节点都必须通过证书及其本地 imports 的禁用 token 检查。机器编译之外，还要
检查公开定理和证书的传递公理依赖，并核对签名与 ledger 陈述是否符合人工批准快照。
结构 checker 只验证当前元数据，不证明历史审批或数学语义。

工作直接在 `main` 上进行，遵循 `research/explorations/2026-09-03-main-only-workflow.md`。
未完成工作保留为本地修改；完成验收后按用户授权直接发布到 `origin/main`，不新建 feature
branch 或 PR。不得用较早 commit 的 CI 结果代替最终发布 commit 的结果。

未来节点遵循 `drafted → frozen → proved`：人工批准完整陈述后冻结，独立证明阶段保留
其公开签名和语义定义。若需要改变冻结陈述，在新 exploration 中记录问题供人工处理。
历史 decision/exploration 不改写；状态变化追加新记录。

## 5. 后续独立任务

以下为路线，不因本次验收而自动开工：

1. **乘积情形 KLS 路线**：二因子推广到有限多因子；可在该扩展中加入反向界与最优常数
   等式。独立证明一维对数凹 Poincaré 界，再结合 Cheeger–Poincaré 比较连接手稿
   `prop:products`。随机局部化部分仍是独立任务。
2. **一维 Gaussian Poincaré 锐常数**：先做 Mathlib 依赖与归一化审查，冻结
   $C_P(N(m,\sigma^2))=\sigma^2$ 的精确接口；复用已有线性测试下界。
3. **多元 Gaussian 与仿射推前**：从一维结果、有限乘积张量化和仿射推前界获得
   $C_P(\gamma)=\lambda_{\max}(\Sigma)$。
4. **Log-Sobolev 与 Bakry–Émery**：分别审查并冻结 LSI 定义、Gaussian LSI 与强凸性界。

闭 Sobolev/谱隙等价、完整 optimal transport、Otto–Villani、Γ₂ calculus 和 KLS
随机分析主干不属于本次张量化验收范围。
