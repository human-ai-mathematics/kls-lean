# Bakry–Émery 路线：`G0`/`G1` 已证——光滑测试函数上的生成元识别

2026-09-20，紧接同日的[路线审查](2026-09-20-bakry-emery-route.md)，是
[完整 Buser 交接](2026-09-20-buser-handoff-prompt.md)的第一个内部里程碑。本轮是**实际 Lean 证明**，
不是路线探查；它不证明也不声称完整 Buser，不把 `C_c^∞` 说成 `T̄†T̄` 的 operator core。
不 commit、不推送；工作区其他未提交修改全部保留。

## 结果

三个新模块，均零 `sorry`、零自定义公理，`-DwarningAsError=true` 下零警告。

| 模块 / 声明 | 内容 |
| --- | --- |
| `Analysis/BakryEmery/IntegrationByParts.lean` | |
| `weightedLaplacian U f x := Δ f x - ⟪∇U x, ∇f x⟫` | 扩散生成元约定的 `ℒ`；`Δ` 是 Mathlib 的 `InnerProductSpace.instLaplacian` |
| `laplacian_eq_sum_fderiv_fderiv`、`inner_gradient_eq_sum_fderiv_mul_fderiv` | `Δf = Σᵢ D²f(eᵢ,eᵢ)`、`⟪∇f,∇g⟫ = Σᵢ ∂ᵢf ∂ᵢg`（`stdOrthonormalBasis`） |
| `continuous_laplacian`、`hasCompactSupport_laplacian`、`continuous_gradient`、`hasCompactSupport_gradient`、`continuous_weightedLaplacian`、`hasCompactSupport_weightedLaplacian`、`memLp_weightedLaplacian` | `ℒf` 连续、紧支撑，故对任意有限测度属于每个 `L^p` |
| `integral_mul_fderiv_mul_fderiv` | 单方向：`∫ w ∂ᵥf ∂ᵥg dm = -∫ (w ∂ᵥ∂ᵥf + ∂ᵥw ∂ᵥf) g dm` |
| `integral_mul_inner_gradient_eq_neg` | **Haar 加权分部积分**：`∫ w ⟪∇f,∇g⟫ dm = -∫ (w Δf + ⟪∇w,∇f⟫) g dm` |
| `inner_gradient_tilted_weight`、`integral_inner_gradient_tilted` | **`G0`**：`μ = m.tilted (-U)` 时 `∫ ⟪∇f,∇g⟫ dμ = ∫ (-ℒf) g dμ` |
| `Analysis/Semigroup/AdjointClosure.lean` | |
| `inner_eq_inner_closure_apply` | `T` 可闭、`⟪w,x⟫ = ⟪v,Tx⟫` 对 `x ∈ D(T)` 成立 ⟹ 对 `x ∈ D(T̄)` 与 `T̄x` 成立（图闭包含于闭集） |
| `mem_adjoint_domain_closure_of_forall`、`adjoint_closure_apply_eq_of_forall` | 由此 `v ∈ D(T̄†)`，且 `D(T̄)` 稠密时 `T̄† v = w` |
| `KLS/LogConcave/HeatSemigroup/Generator.lean` | |
| `integral_inner_gradient_eq` | `G0` 的概率律形式：前提 `(ν : Measure V) = m.tilted (-U)` |
| `integral_weightedLaplacian_eq_zero` | `∫ ℒf dν = 0`（`g = 1`；`integral_heatSemigroup` 的无穷小形式） |
| `memLp_neg_weightedLaplacian` | **`G1` 可积性**：`-ℒf ∈ L²(ν)` |
| `toLp_mem_closedWeightedOperator_domain`、`closedWeightedOperator_toLp_eq` | `[f] ∈ D(T̄)`，`T̄[f] = [∇f]` |
| `inner_toLp_neg_weightedLaplacian_eq` | 弱恒等式 `⟪[-ℒf], x⟫ = ⟪[∇f], T̄x⟫` 对**所有** `x ∈ D(T̄)` |
| `toLp_mem_adjointComp_domain`、`adjointComp_toLp_eq` | **`G1`**：`[f] ∈ D(T̄†T̄)`，`T̄†T̄ [f] = [-ℒf]` |

这里 `T̄ = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi`，`A = T̄†T̄ = adjointComp T̄`，
`P_t = exp(-tA)`；由 `heatSemigroup_generator`，对 `f ∈ C_c^∞`，`(P_t[f] - [f])/t → [ℒf]`，
即 `d/dt P_t f |_{t=0} = ℒf`，符号与路线记录一致。

审计 `research/audits/BakryEmeryGeneratorAudit.lean` 逐字重述路线文件的 `G0`、`G1` 为
`route_G0`、`route_G1` 并各用一个 `exact` 证明，另记三条一致性用法（`g = 1` 零均值、`g = f`
的 Dirichlet 形式 `∫ ‖∇f‖²`、`ℒ` 在 `C_c^∞` 上对称）；**32 条 `#print axioms` 全部标准，0 `sorryAx`**。
`research/audits/BakryEmeryRouteStatements.lean` 加入新模块的 `#check @…`，并在 `G0`、`G1` 段落注明
已被哪些声明消解；其匿名命题保留为签名审计，零错误零警告。

## 证明结构

`G0`：Mathlib 只有单方向的 `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`。取
`F = w ∂ᵥf`（`f` 紧支撑故 `F` 紧支撑，`g` 不必紧支撑），用 `HasFDerivAt.mul`、`HasFDerivAt.clm_apply`
算出 `∂ᵥF`，可积性全部来自"连续 × 紧支撑"。再对 `stdOrthonormalBasis` 求和：
`OrthonormalBasis.sum_inner_mul_inner` 给 `⟪∇f,∇g⟫`，
`laplacian_eq_iteratedFDeriv_orthonormalBasis` + `iteratedFDeriv_two_apply` 给 `Δf`。
tilted 情形由 `integral_tilted` 化为 Haar 积分，权 `w = exp(-U)/Z` 的梯度是 `-w ∇U`；`Z` 的正性
不需要（恒等式对权线性）。

`G1`：**不做点态计算**。对 `g ∈ C_c^∞` 由 `G0` 得 `⟪[-ℒf],[g]⟫_{L²} = ⟪[∇f],[∇g]⟫_{L²}`；
`closure_domRestrict_eq_of_smoothCore_le` 说光滑核上的限制与 `T̄` 同闭包，
`inner_eq_inner_closure_apply` 把恒等式延拓到整个 `D(T̄)`；于是按伴随定义
（`LinearPMap.mem_adjoint_domain_of_exists`、`LinearPMap.adjoint_apply_eq`，后者用
`dense_domain_closedWeightedOperator`）`[∇f] = T̄[f] ∈ D(T̄†)` 且 `T̄†[∇f] = [-ℒf]`，
这正是 `adjointComp` 的域成员关系与取值（`adjointComp_apply`）。

实际使用的正则性弱于路线文件：`U ∈ C¹`，`G0` 只需 `f ∈ C²`、`g ∈ C¹`（`g` 无需紧支撑）；
`G1` 保留 `f ∈ C_c^∞`，因为 `smoothCore`/`IsTest.of_contDiff_hasCompactSupport` 以 `ContDiff ℝ ∞`
为接口。审计客户端把 `ContDiff ℝ ∞` 降到这些阶数后逐字重述。

## 这意味着什么、不意味着什么

路线记录第 4 节的四层区别保持不变，**只有第一层被证明**：

1. ✓ `C_c^∞` 上 `A[f] = [-ℒf]`，包含 `[f] ∈ D(A)`；
2. （已有）`C_c^∞` 是一阶闭形式的 form core（`closure_domRestrict_eq_of_smoothCore_le`）；
3. ✗ 未证明 `C_c^∞` 在 `D(A)` 的图范数下是 operator core；
4. ✗ 未证明 `-ℒ` 在 `C_c^∞` 上的闭包等于完整的 `A`。

前提 `(ν : Measure V) = m.tilted (-U)` 是显式假设，本轮没有从对数凹性构造它，也没有用到 `U` 的凸性
（`N0` 包仍只通过类型检查）。没有 `Γ`、`Γ₂`、Bochner、任何 `t > 0` 时 `P_t f` 的正则性或梯度估计，
没有一般对数凹律的逼近，也没有 Buser 的任何一步。`thm:logconcave-cheeger-poincare-comparison`
仍无 `\leanok`，常数 `π` 未被触及，26 个证书与 `KLS/Target.lean` 的目标洞不变。

## 摩擦记录

- `HasCompactSupport.fderiv` 的 `𝕜` 无法由结论推出，须写 `hfc.fderiv (𝕜 := ℝ)`；
  `HasCompactSupport.fderiv_apply` 的 `𝕜` 是显式参数：`hfc.fderiv_apply ℝ v`。
- `ContDiff ℝ ∞ f → ContDiff ℝ 2 f`：`mod_cast le_top` 失败（目标是 `2 ≤ ↑⊤`），
  用 `hf.of_le (WithTop.coe_le_coe.mpr le_top)`。
- `ContinuousLinearMap.add_apply`/`smul_apply`/`zero_apply`/`neg_apply` 已弃用，改用根名字空间的
  `add_apply` 等。
- `set S := T₀.domRestrict …` 之后 `rw [LinearPMap.domRestrict_apply …]` 找不到模式（子类型的类型标注不同），
  改为不用 `set`、显式写出算子并用 `erw`；`(LinearPMap.le_closure T).2` 要同时给 `x` 与 `y`。
- 聚合根 `FunctionalInequalities.lean` 此前缺少 `Generated/Markov`、`HeatSemigroup/Markov`、
  `CanonicalEnergy`、`BakryEmery/Basic`（均为未提交模块），本轮连同三个新模块一起加入。

## 验证

默认 `lake build` **3548 jobs** 通过（聚合根含上述七个模块）。
`BakryEmeryGeneratorAudit.lean` 与 `BakryEmeryRouteStatements.lean` 在 `-DwarningAsError=true` 下零错误零警告；
**32 条公理报告全部标准，0 `sorryAx`**。`check_ledger.py` 26 个证书 0 错误；`check_blueprint.py` 88 个标签
0 错误；`atlas.py check` 75 个节点、26 个证书、无环；`research/tests` 104 个单元测试通过。
`tasks.json` 中 `thm:logconcave-cheeger-poincare-comparison` 的 infrastructure 证据加入本轮文件的
sha256，第一条缺口改写为剩余义务；进度图 `BE` 节点由 pending 改为 partial，视图按 `AGENTS.md`
从临时索引中暂存的 canonical records 重新生成，真实索引不变。根 `python3 research/verify.py`
在本轮末重跑，其收据记录在 `build/audit/generator-identification/final-snapshot.json`。

## 下一步

按路线记录第 10 节：`B0`（carré du champ 乘积恒等式）与 `B1`（`C²` 凸函数的 Hessian 半正定）是纯局部微分模块，
可独立证明；`B3` 的坐标 Bochner 展开等 Hessian/混合导数辅助引理稳定后再做。半群侧的下一障碍是
第 6 节的代表与域稳定性：`t > 0` 时 `P_t[f]` 的正则代表、`P_t` 保持 `D(T̄)`、时间微分与极限交换。
第 3、4 层（operator core、闭包等同）如需使用须单独证明，不得由本轮结论推出。
