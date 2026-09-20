# 下一步提示词：Bakry–Émery 路线探查——生成元识别与 Bochner 接口

> **已被后续任务范围取代。** Owner 同日决定先完成完整 Buser；请执行
> [完整 Buser 交接](2026-09-20-buser-handoff-prompt.md)。下文保留为早期路线切口与技术检查记录，
> 其中“只探查”“不改 Lean”“不要求完成 Buser”的限制不再适用于当前任务。


可直接把下文交给下一会话。2026-09-20 的状态基线：半群生成与所述 `L²` Markov 性已完成；本任务尚未实施。

---

请在 `/Users/lyuyuwei/Documents/ChatGPT/KLS` 做下一轮**路线探查与精确接口设计**，目标是为 Buser 半
`Ψ_KLS(μ)² ≤ π C_P^lit(μ)` 补齐 Bakry–Émery 路线的起点。本轮不要求证明完整 Buser，
也不要求一次完成梯度估计或一般对数凹测度的逼近理论。

## 1. 先核对现状，避免重复工作

先读 `AGENTS.md`、`HANDOFF.md` 顶部的 `Current operational status (2026-09-20)`、
`research/decisions/2026-09-20-current-status-alignment.md`，再检查当前工作区。
旧交接中的 S6、S7、S8、Markov 待办已经过时，不要重新实现。

已经存在的入口（以下路径相对仓库根）：

- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/{Basic,Laws,Generator,Markov}.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/{Basic,Markov}.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient.lean`
- `formalization/FunctionalInequalities/Energy/WeightedGradient/{Basic,Core,Closable}.lean`
- `formalization/FunctionalInequalities/Energy/Cheeger/Identification.lean`
- `formalization/FunctionalInequalities/Poincare/LocalSlope/Gradient.lean`
- `research/audits/{HeatSemigroupAudit,HeatSemigroupMarkovAudit}.lean`

`heatSemigroup hν m B hi ht` 已是由加权梯度闭包 `T` 生成的 `L²(ν)` 半群；
`heatSemigroup_generator` 给出 `D(T*T)` 上的生成元 `-T*T`。
`heatSemigroup_positive`、`heatSemigroup_one`、`heatSemigroup_subMarkov`、
`integral_heatSemigroup`、`abs_heatSemigroup_le` 和 `abs_heatSemigroup_le_const` 已证。
完整参数、隐式实例及命名空间以当前 `#check @...` 为准。
这些是 `L²` 上的结论，不要把它们写成已经构造了独立的全 `L¹` 半群。

## 2. 本轮的最小数学切口

先限制到有限维欧氏空间上的**光滑凸位势**，记空间为 `E`、位势为 `V`，避免同名。
取

`dμ = Z⁻¹ exp(-V) dx`，`0 < Z < ∞`，`B = I`。

凸性不自动保证可归一化；应明确归一化、光滑性、可积性、测试函数及非空内部等条件。
局部 Bochner 公式与概率测度/半群之间的连接应分开陈述。光滑子类仅是中间任务，
不得用这些新条件替换最终任意对数凹律的 Buser 目标。

逐项设计以下义务，说明哪些已有 API 可直接承担，哪些缺失：

1. **微分生成元与符号。** 设 `A = T*T ≥ 0`，`P_t = exp(-tA)`，
   `ℒ = Δ - ⟨∇V, ∇·⟩`。目标是对明确的光滑紧支撑测试函数证明
   `f ∈ D(A)` 且 `Af = -ℒf`，包括 `ℒf ∈ L²(μ)`。
   分部积分应连接现有闭梯度算子的伴随定义，而不是只计算一个形式微分表达式。
   不要未经证明就把 `C_c∞` 称作完整生成元的 operator core；区分测试函数上的一致、
   form-core 稠密性、operator-core 稠密性与完整闭算子相等。
2. **Γ 与 Γ₂。** 采用扩散生成元 `ℒ` 的约定：
   `Γ(f,g) = (ℒ(fg) - fℒg - gℒf)/2 = ⟨∇f,∇g⟩`，
   `Γ₂(f) = ℒ(Γ(f,f))/2 - Γ(f,ℒf)`。
   设计带精确正则性假设的 Bochner 恒等式：
   `Γ₂(f) = ‖Hess f‖_HS² + Hess V(∇f,∇f)`，继而由凸性得 `Γ₂(f) ≥ 0`。
   核查 Hessian、Laplacian、Hilbert–Schmidt 范数、基无关性及混合导数 API；
   若只能先在固定正交坐标中陈述，明确记录这层选择。
3. **接到现有 P_t 的缺口。** 列出从局部 Bochner 公式得到
   `‖∇P_t f‖ ≤ P_t(‖∇f‖)` 所缺的域稳定性、正则性、时间微分和极限交换。
   区分 L¹ 型梯度交换与平方形式的 Γ 估计，不得把较弱结论自动替代文献所需输入。
   `P_t f` 是 `L²` 等价类，梯度必须通过闭梯度或已证明存在的正则代表解释；
   不能直接对任意代表取经典 `gradient`。
4. **能量归一化。** 明确 `‖Tf‖²`、`E^can`、`2 Ch`、谱隙及时间参数的关系。
   若 `B = I` 的算子能量与某个前端的等同性尚缺，单列桥梁义务，不能凭命名认定。

## 3. 一般测度的出口必须写清楚

不要求本轮实现，但必须列出如何走向一般对数凹律：非光滑凸位势、支撑边界、
仿射降维、Dirac/零维情形。分别指出逼近方案、闭形式/预解/半群的收敛意义，
以及梯度界、周长界和目标常数的极限稳定性需要什么。

不要默认一定能用 Neumann 边条件，也不要未经证明就把当前对象视为 RCD 空间；
比较可行方案，推荐一个与现有 API 最接近的方案，明确未解决的桥梁。
光滑严格凸逼近如被采用，要解释它为何能逼近带边界或非严格凸的目标类。

## 4. 先核查原始文献，再定足够的接口

核对 Blueprint 的 `thm:logconcave-cheeger-poincare-comparison` 及 bibliography。
主要外部参照是 De Ponti–Mondino：
<https://arxiv.org/abs/1902.03835>，并核查 Blueprint 引用的 Klartag 常数约定。
记录实际使用的版本、定理/引理编号、假设和归一化，不要仅凭摘要推断常数。
对照最终 π 目标反推需要的梯度/热估计强度。
本轮不实现小时间 BV 估计与最终 Buser 拼装，但应标出其对本轮接口的要求。

## 5. 交付物与验收

- 新建 `research/decisions/2026-09-20-bakry-emery-route.md`：路线、文献定位、API 清单、
  域与归一化审查、精确障碍，以及下一轮可独立证明的最小任务。
- 新建 `research/audits/BakryEmeryRouteStatements.lean`：已有声明的 `#check @...`，
  以及具备足够定义后可精确写出的候选命题 `#check (∀ ..., ...)`。只做类型检查，
  不引入 `axiom`、`sorry`、占位证明或把目标本身藏入结构字段/假设。
  缺少关键对象时，先写清缺少哪个定义；不要为凑语句发明一个不忠实的替代目标。
- 给出“已有证明／仅通过类型检查／仍是非形式化方案”三栏清单。
  本轮路线文件编译成功不代表上述义务已证明。
- 从 `formalization/` 运行
  `lake env lean -DwarningAsError=true ../research/audits/BakryEmeryRouteStatements.lean`，
  应为零错误、零警告；不得升级 Lean/Mathlib 或修改 lakefile 来通过。
- 路线合理后再推荐证明任务；不把完整 Buser 当成本轮验收条件。

保留所有既有公开声明、定理范围、26 个证书和孤立的 `KLS/Target.lean` 目标洞。
本轮不改 Lean 库证明、不改 Blueprint 完成标记、不改完整比较节点为 proved，
不提交、不推送。若同步当前进度文档，按 `AGENTS.md` 从暂存的 canonical records
重新生成视图，保留他人改动。最终用中文说明已核实内容、真正缺口与推荐的下一证明切口。
