# 下一步提示词：完成任意维对数凹律的 Buser 比较

2026-09-20，owner 调整优先级：**先完成完整 Buser，再推进依赖它的 KLS 路线**。
这取代同日仅交付 Bakry–Émery 路线探查的任务范围；当前证明状态没有因此改变。

---

请在 `/Users/lyuyuwei/Documents/ChatGPT/KLS` 继续实施 Lean 证明，主目标是完成
Blueprint 节点 `thm:logconcave-cheeger-poincare-comparison` 中尚缺的 Buser 半：

**对每个有限维欧氏空间上的任意对数凹概率律 μ，证明**

`Ψ_KLS(μ)² ≤ π C_P^lit(μ)`。

以现有 Blueprint 和 `research/audits/BuserRouteStatements.lean` 中 B0 的精确命题为准。
必须保持常数 π、任意维、非光滑位势、有边界或降维支撑、Dirac/零维情形和扩展非负实数约定。
不能用一维常数 12、只对光滑严格凸密度成立的定理，或附带未消解分析假设的条件定理代替完成。

## 已有成果与工作入口

先读 `AGENTS.md`、`HANDOFF.md` 的当前状态段和工作区改动。保护既有未提交文件，
不要重新实施已经完成的半群生成或 Markov 性。

- Cheeger 半 `C_P^lit ≤ 4 Ψ²` 已证：`KLS/Geometry/Cheeger/Inequality.lean`。
- 仿射支撑维数至多一时的 Buser 常数 12 已证：`KLS/LogConcave/Line/Buser.lean`。
- Cheeger infimum 等同性已证：`KLS/Geometry/Cheeger/{Infimum,Equality}.lean`。
- 文献 Poincaré 梯度刻画已证：`Poincare/LocalSlope/Gradient.lean`。
- S1–S8、`-T*T` 生成元及具体热半群已证：`Analysis/Semigroup/Generated/`、
  `KLS/LogConcave/HeatSemigroup/Basic.lean`。
- `L²` 上的保正、保常数、次 Markov、保积分、绝对值控制及有限本质界压缩已证：
  `Analysis/Semigroup/Generated/Markov.lean`、`KLS/LogConcave/HeatSemigroup/Markov.lean`。

以上模块均位于 `formalization/FunctionalInequalities/` 下。已有审计入口是
`research/audits/{HeatSemigroupAudit,HeatSemigroupMarkovAudit}.lean`。
完整参数与假设以当前 `#check @...` 为准。全维定理可用于 intrinsic law；
现有 `L²` 结果不自动等于已经构造了全 `L¹` 半群。

## 实施方式：内部拆解，最终交付完整 Buser

先核查原始文献和现有 API，写出精确依赖与归一化，然后直接推进证明。
路线记录和候选语句是中间产物，不能作为本任务的完成条件。
采用有文献依据且能接上现有 API 的路线；下面是建议的半群路线，不要求机械照搬：

1. **生成元、Bochner 与梯度估计。** 在光滑凸位势 `V`、
   `dμ = Z⁻¹ exp(-V) dx`、`0 < Z < ∞`、`B = I` 的中间类上，
   核查 `A = T*T ≥ 0` 与 `ℒ = Δ - ⟨∇V,∇·⟩ = -A` 的域和符号。
   对精确测试函数证明成员关系及作用一致，处理所需的 core/闭包接口。
   用扩散生成元 ℒ 的约定构造 Γ、Γ₂，并证明
   `Γ₂(f) = ‖Hess f‖_HS² + Hess V(∇f,∇f) ≥ 0`。
   继续补齐通向现有 `P_t` 的域稳定性、正则性、微分与极限接口，得到文献所需的梯度估计。
   局部 Bochner 计算不是半群估计；`L²` 等价类不能未经正则性证明就选代表求经典梯度。
2. **一般对数凹律。** 实现所采用的逼近或其他推广机制，证明闭形式、预解或半群的适当收敛，
   以及所用不等式和常数的稳定性。支撑边界、非光滑位势、降维与零维必须落实。
   不预设 Neumann 边条件或 RCD 身份已经成立，不把逼近有效性藏进最终定理假设。
3. **小时间估计。** 证明 Buser 论证实际需要的热半群 L¹ 逼近界和梯度平滑界，
   处理指标函数/BV 测试、所需的 L¹ 接口以及 metric BV、Minkowski 和 relative perimeter 的联系。
   只实现终点需要的接口，避免无关的通用理论扩张。
4. **拼装 π 比较。** 将谱隙、Poincaré 最优常数、`‖Tf‖²`、`E^can = 2 Ch` 与时间归一化精确对齐，
   完成时间参数优化及退化情形处理，消解所有中间分析假设，给出 B0 的本地 Lean 证明。
   再与既有 Cheeger 半组合，完成完整比较节点。

核查 Blueprint bibliography 中的 De Ponti–Mondino
<https://arxiv.org/abs/1902.03835> 和 Klartag 的归一化；记录具体版本、定理编号、假设和常数。
不要依据摘要或“标准论证”省略形式化桥梁。此前
`research/decisions/2026-09-20-bakry-emery-handoff-prompt.md` 中的技术检查可作参考，
但其中“只探查”“不改 Lean”“本轮不完成 Buser”的范围限制已被本提示词取代。

## 完成标准

- 新增证明零 `sorry`、零自定义占位公理，无隐藏的循环依赖、目标假设或范围削弱。
  保留已有公共签名和数学边界，遵守当前目录与命名约定。
- 独立审计客户端逐字重述并证明原始 B0，核查所有量词、常数、无限值和退化情形。
  关键公开声明及最终比较的 `#print axioms` 只含标准公理，不依赖 `sorryAx`。
- 受影响模块与审计客户端在 `-DwarningAsError=true` 下通过；运行 `lake build`、
  ledger/Blueprint/atlas 检查及 `python3 research/verify.py`，绑定最终工作区快照。
  既有 `KLS/Target.lean` 的孤立 KLS 目标洞不属于本任务，不得导入证明链。
- 只有完整原始比较得到证明与验证后，才更新 Blueprint 完成标记及相应证书记录；
  更新任务证据、当前摘要和进度视图，按 `AGENTS.md` 从暂存 canonical records 生成。
  中间辅助结果可以如实登记，不能提前把完整 Buser 标为已完成。
- 不升级 Lean/Mathlib，不提交、不推送。可持续完成内部子任务，不在每个阶段重新请求许可。

完成 Buser 仍不等于证明 KLS。若遇到真正无法消解的数学或 API 障碍，诚实报告
已经证明的精确声明、未证义务、失败路线及最小缺口；不能把降级后的结果当作完成，
也不要因为路线文件已写好或单个辅助引理已完成就主动结束实施。
