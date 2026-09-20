# 下一步提示词：Bakry–Émery S0a——生成元域刻画、半群域稳定与闭梯度接口

请在 `/Users/lyuyuwei/Documents/ChatGPT/KLS` 继续 Buser 的 Bakry–Émery 路线。本轮做一个
独立、可验证的半群接口切口：在当前抽象生成半群上证明生成元域的反向刻画，并由此得到
`D(T†T)` 在 `P_t` 下的稳定性和生成元交换，再专门化到现有
`KLS.LogConcave.heatSemigroup`。

本轮不是完整的正时间 PDE 平滑性：只从 `f ∈ D(T†T)` 出发证明
`P_t f ∈ D(T†T)`。不得把它写成对任意 `L²` 输入已有 `P_t f ∈ D(T†T)`，也不得声称已经
构造了 `P_t f` 的经典光滑代表、证明了梯度交换或完成了 Buser。

## 1. 先核对当前工作区

先读：

- `AGENTS.md`
- `HANDOFF.md` 顶部 `Current operational status (2026-09-20)`
- `research/decisions/2026-09-20-bakry-emery-route.md`
- `research/decisions/2026-09-20-generator-identification.md`
- `research/decisions/2026-09-20-bochner-identification.md`
- `research/audits/BakryEmeryRouteStatements.lean`

重点检查：

- `formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Basic.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Laws.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Generator.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Family.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Limit.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Basic.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean`

检查当前 dirty worktree，保留所有既有修改；不 reset、clean、覆盖或删除他人工作。本轮
不提交、不推送。

## 2. 当前已证基线

设 `T : H₀ →ₗ.[ℝ] H₁` 闭且稠密定义，

```text
A = adjointComp T = T†T,
P_t = semigroupApply T hT hd t.
```

已经存在：

- `isSelfAdjoint_adjointComp`：`A` 自伴；
- `dense_adjointComp_domain`：`D(A)` 稠密；
- `inner_semigroupApply_left`：`P_t` 自伴；
- `semigroupApply_add`：`P_(t+u) = P_t P_u`；
- `norm_semigroupApply_le`：`P_t` 是压缩；
- `exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt`：
  对 `f ∈ D(A)`，

  ```text
  h⁻¹ • (P_h f - f) → -Af    (h ↓ 0).
  ```

- `mem_domain_of_mem_adjointComp_domain`：`D(A) ⊆ D(T)`；
- `heatSemigroup_generator`：上述生成元极限已专门化到闭加权梯度。

G0/G1 与 B0–B4 已完成，但本轮不要重复 Bochner 计算。

所有完整参数、命名空间、隐式实例和 `LinearPMap` subtype 形状以当前 `#check @...` 为准，
不要凭本文简写猜测。

## 3. 第一目标：生成元域的反向刻画

当前只证明了

```text
f ∈ D(A)  ⟹  h⁻¹ • (P_h f - f) → -Af.
```

本轮先证明反向：若某个 `y : H₀` 的右差商在 `h ↓ 0` 时收敛到 `z : H₀`，则

```text
y ∈ D(A)  且  A y = -z.
```

建议新增：

```text
formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Domain.lean
```

候选公开声明可命名为：

```text
mem_adjointComp_domain_of_generator_limit
adjointComp_eq_neg_of_generator_limit
```

或将成员关系和作用值放在一个返回 `∃ hy : y ∈ D(A), ...` 的定理中。具体 Lean 陈述应沿用
当前生成元文件的 `ε`–`δ` 右极限形状，例如：

```text
∀ ε > 0, ∃ δ > 0, ∀ h > 0, h < δ,
  ‖h⁻¹ • (P_h y - y) - z‖ < ε.
```

注意现有正向定理写成

```text
‖h⁻¹ • (P_h f - f) + Af‖ < ε,
```

所以反向结论必须是 `Ay = -z`，不要发生符号反转。

### 推荐证明路线

固定任意 `x ∈ D(A)`：

1. 用 `inner_semigroupApply_left` 把

   ```text
   ⟪h⁻¹ • (P_h y - y), x⟫
   ```

   改写成

   ```text
   ⟪y, h⁻¹ • (P_h x - x)⟫.
   ```

2. 左边由假设趋于 `⟪z,x⟫`；右边由现有生成元定理趋于 `⟪y,-Ax⟫`。
3. 得到对所有 `x ∈ D(A)`：

   ```text
   ⟪-z,x⟫ = ⟪y,Ax⟫.
   ```

4. 用 `LinearPMap.mem_adjoint_domain_of_exists` / `adjoint_apply_eq` 一类现有接口证明
   `y ∈ D(A†)` 且 `A†y = -z`。
5. 用 `isSelfAdjoint_adjointComp` 把 `A† = A`，得到 `y ∈ D(A)` 和 `Ay = -z`。

不得把反向刻画本身作为新假设，也不得定义一个结构并把目标结论藏入字段。若内积极限的
搬运没有现成拓扑 API，可以按当前仓库风格做显式 `ε`–`δ` 估计；不要引入未经证明的抽象
生成元定理。

## 4. 第二目标：`D(A)` 的半群稳定与交换

对任意 `f : D(A)`、`t ≥ 0`，证明：

```text
P_t f ∈ D(A),
A(P_t f) = P_t(Af).
```

建议公开声明：

```text
semigroupApply_mem_adjointComp_domain
adjointComp_semigroupApply
```

推荐从第 3 节的反向刻画推出，而不是重新做一套 Yosida 图极限：

```text
h⁻¹(P_h(P_t f) - P_t f)
  = P_t(h⁻¹(P_h f - f))
  → -P_t(Af).
```

这里使用：

- `semigroupApply_add`；
- `semigroupApply_sub`、`semigroupApply_smul`；
- `norm_semigroupApply_le`；
- `P_h P_t = P_t P_h`，应从同一参数的半群加法和 `h+t=t+h` 精确推出；
- 已有的 `f ∈ D(A)` 零时刻生成元极限。

随后由反向刻画得到成员关系和

```text
A(P_t f) = P_t(Af).
```

定理应覆盖 `t = 0`，不需要人为增加 `0 < t`。若 subtype 的成员证明不同导致项表面不相等，
使用 proof irrelevance / `Subtype.ext`，不要增加无关假设。

## 5. 第三目标：任意时刻的右时间导数

对 `f ∈ D(A)`、`t ≥ 0`，证明精确的 `ε`–`δ` 版本：

```text
h⁻¹ • (P_(t+h) f - P_t f) → -A(P_t f)
                         = -P_t(Af)    (h ↓ 0).
```

建议声明：

```text
exists_delta_norm_inv_smul_semigroupApply_add_sub_add_adjointComp_lt
```

或采用项目中更简洁且不歧义的名称。必须明确这是右导数；不要把只对 `h > 0` 的结论写成
已经证明了整个实轴上的 Fréchet 可微性。

这一步是后续插值量

```text
s ↦ P_s Γ(P_(t-s) f)
```

时间微分的纯半群先决条件，但本轮不定义或微分该插值量。

## 6. 第四目标：专门化到现有 `heatSemigroup`

建议新增：

```text
formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Domain.lean
```

设

```text
T̄ = hν.closedWeightedOperator m B hi,
A  = adjointComp T̄.
```

证明与抽象定理逐字对应的包装：

- `heatSemigroup_mem_generator_domain`：`f ∈ D(A)` 时 `P_t f ∈ D(A)`；
- `heatSemigroup_generator_comm`：`A(P_t f)=P_t(Af)`；
- `heatSemigroup_mem_closedWeightedOperator_domain`：由 `D(A) ⊆ D(T̄)` 得
  `P_t f ∈ D(T̄)`；
- `heatSemigroup_right_derivative`：任意 `t ≥ 0` 的右导数。

至少对一般权重 `B` 保持抽象包装；不要无故限制到 `B = I`。与经典
`weightedLaplacian` 的等同仍只在 G1 已证明的 `C_c∞` 输入上使用。

本轮所得“梯度”只能解释为闭梯度

```text
T̄(P_t f),
```

不能直接写成某个任意 `L²` 代表的经典 `gradient`。

## 7. 明确不属于本轮的更强结论

以下都保持未证：

1. 对任意 `f : H₀`、`t > 0`，`P_t f ∈ D(A)`；
2. `‖A P_t f‖ ≤ C/t · ‖f‖`；
3. 对任意 `f ∈ D(T)`，`P_t f ∈ D(T)` 及
   `‖T(P_t f)‖ ≤ ‖Tf‖`；
4. `P_t[f]` 存在 `C∞` 或 `C³` 的经典代表；
5. `P_t` 保持 `C_c∞`，或 `C_c∞` 是 `A` 的 operator core；
6. `Γ(P_t f) ≤ P_t Γ(f)`；
7. `‖∇P_t f‖ ≤ P_t ‖∇f‖`；
8. BGL 反向估计、小时间 BV 估计、一般测度逼近和最终 Buser。

其中第 1–2 项是真正的“正时间解析平滑”，需要额外的 Yosida 指数一致估计或等价功能演算，
不能从本轮的域稳定性自动推出。第 3 项是 form-domain 稳定性，也比 `D(A)` 输入上的结论强。

## 8. 候选后续接口只做类型检查

在审计文件中额外保留以下下一阶段候选，但不要用假设把它们伪装成证明：

```text
∀ f t, 0 < t → P_t f ∈ D(A)
```

以及带显式常数的

```text
‖A(P_t f)‖ ≤ C / t * ‖f‖.
```

在证明具体常数前先从标量函数 `λ ↦ λ exp(-tλ)` 的最优界反推正确归一化；如果当前无
谱函数演算，只记录所缺的 Yosida 一致估计，不要猜常数。

## 9. 审计与交付物

新增：

- `research/audits/SemigroupDomainStabilityAudit.lean`
- `research/decisions/2026-09-20-semigroup-domain-stability.md`

审计至少逐字重述并关闭：

```text
D0  右差商极限存在 ⟹ y ∈ D(A) 且 Ay = -z
D1  f ∈ D(A) ⟹ P_t f ∈ D(A)
D2  A(P_t f) = P_t(Af)
D3  t ≥ 0 处的右导数为 -A(P_t f)
D4  heatSemigroup 的 D1–D3 包装及 D(A) ⊆ D(T̄)
```

对所有新增公开声明运行 `#print axioms`。只允许 Mathlib 常见基础公理；不得出现：

- `sorryAx`
- 新 `axiom`
- `sorry` / `admit`
- 占位证明
- 把结论藏入结构字段、typeclass 或额外假设
- 把 `D(A)` 输入偷偷加强成测试函数并仍声称完成一般域稳定

决策记录必须列出：

- 实际声明与证明依赖；
- 反向生成元刻画中自伴性的使用位置；
- `A` 与半群交换的符号；
- 哪些结论只对 `D(A)` 输入成立；
- 与正时间任意输入平滑、form-domain 稳定和经典代表之间的严格边界；
- 下一阶段需要的 Yosida 一致估计或弱 Γ 接口。

给出“已有证明／仅类型检查／仍是非形式化方案”三栏表。本轮完成不改变完整
Cheeger–Buser 节点的 pending 状态，`BE` 节点仍应是 partial。

## 10. 验收

从 `formalization/` 运行：

```bash
lake env lean -DwarningAsError=true \
  FunctionalInequalities/Analysis/Semigroup/Generated/Domain.lean

lake env lean -DwarningAsError=true \
  FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Domain.lean

lake env lean -DwarningAsError=true \
  ../research/audits/SemigroupDomainStabilityAudit.lean

lake build
```

从仓库根运行：

```bash
git diff --check
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests
python3 research/verify.py
```

新文件必须在 `-DwarningAsError=true` 下零错误、零警告。完整构建中
`KLS/Target.lean` 的既有目标洞警告可以保留，不得新增其他 `sorry` 或警告。

若同步进度文档，按 `AGENTS.md` 从暂存的 canonical records 运行
`python3 research/progress/update.py`；保留他人修改，不把 `BE`、完整 Buser 或 KLS 标成
proved。

## 11. 最终汇报

最终用中文说明：

1. D0–D4 分别由哪些声明完成；
2. 反向生成元刻画为何需要 `P_t` 和 `A` 的自伴性；
3. `A(P_t f)=P_t(Af)` 的符号与 subtype 成员关系如何处理；
4. 是否只证明了 `D(A)` 输入上的域稳定；
5. 公理审计、严格编译和完整验证结果；
6. 下一步应选“任意输入正时间进入 `D(A)`”还是“`D(T)` form-domain 稳定”，以及所缺的
   最小估计。

不要提交、不要推送。
