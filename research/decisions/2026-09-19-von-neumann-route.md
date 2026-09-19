# 半群生成路线：von Neumann 定理与预解极限（`S6` 前置）路线轮

2026-09-19，紧接 [`S5` 轮](2026-09-19-semigroup-yosida-proof.md)与 owner 保持常数 π 的决定
（[交接清单](2026-09-19-semigroup-handoff.md) §5 附注）。本轮**只写定义与语句，不证明**；
证明交给并行的 Opus 会话，之后由本会话集成。不 commit、不推送。

## 为什么是这一块

`S1`–`S5` 已证。`S6`（Yosida 指数 `exp(-t L_s)` 随 `s ↓ 0` 强收敛）是路线里没有 Mathlib 先例的一步，
经典证法需要两样 `S1`–`S5` 刻意绕开的东西：

1. **von Neumann 定理**：`T` 闭且稠定 ⟹ `T†T` 自伴、`D(T†T)` 稠密，且 `(1 + s T†T) J_s = 1`；
2. **预解极限**：`J_s → 1` 强收敛，`J_s J_r = J_r J_s`（后者正是 `S6` 语句里假设的交换性）。

owner 已决定目标保持 π，局部化路线出局，所以半群路线必须走完，这是下一块。

## 定义模块（本轮已写并编译）

`formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean`，仅定义与 `rfl` 级胶水：

| 声明 | 内容 |
| --- | --- |
| `adjointCompDomain T` | `{x ∈ D(T) \| T x ∈ D(T†)}`，作为 `Submodule ℝ H₀` |
| `adjointComp T` | `T†T`，即 `T†.comp (T.domRestrict (adjointCompDomain T)) _` |
| `adjointComp_domain`、`adjointComp_domain_eq` | 域按定义是 `adjointCompDomain T ⊓ T.domain`，等于 `adjointCompDomain T` |
| `adjointComp_apply` | `adjointComp T x = T† ⟨T ⟨x, x.2.2⟩, _⟩` |

Mathlib 的 `LinearPMap.comp` 要求内层算子的所有值落在外层域里，所以先用 `domRestrict` 限制 `T`。
`T†` 需要 `[CompleteSpace H₀]`；`H₁` 的完备性在定义里用不到。
`-DwarningAsError=true` 通过，0 错误 0 警告；已用 `lake build` 单独生成 olean 供证明会话 import。

## 语句文件

`research/audits/VonNeumannRouteStatements.lean`，只含 `#check`，8 条全部通过类型检查：

| 编号 | 内容 | 假设 | 风险 |
| --- | --- | --- | --- |
| `V1` | `⟪T†T x, y⟫ = ⟪T x, T y⟫`，`x ∈ D(T†T)`，`y ∈ D(T)` | `Dense` | 低：`adjoint_isFormalAdjoint` 展开 |
| `V2` | `J_s f ∈ D(T†T)` 且 `J_s f + s • T†T (J_s f) = f` | 闭、`Dense`、`0 < s` | 中：弱方程 ⟹ `T u ∈ D(T†)`（`mem_adjoint_domain_of_exists`）+ `adjoint_apply_eq` |
| `V3` | `IsSelfAdjoint (adjointComp T)` | 闭、`Dense` | 中高：对称性给 `≤`，反向用 `1 + T†T` 满射（`V2`） |
| `V4` | `Dense (D(T†T))` | 闭、`Dense` | 低：`V3` + `IsSelfAdjoint.dense_domain` |
| `V5` | `f - J_s f = s • J_s (T†T f)`，`f ∈ D(T†T)` | 闭、`Dense`、`0 < s` | 低中：`f` 自身解数据为 `f + s T†T f` 的弱方程，唯一性 |
| `R1` | `‖J_s f - f‖² ≤ s ‖T f‖²`，`f ∈ D(T)` | 闭、`0 < s` | 低：弱方程对 `v = u - f` 与 `v = u` 检验 |
| `R2` | `∀ f ε>0, ∃ δ>0, ∀ 0<s<δ, ‖J_s f - f‖ < ε` | 闭、`Dense` | 低：`R1` + 稠密 + 压缩 |
| `R3` | `J_s ∘ J_r = J_r ∘ J_s` | 闭 | 中：弱形式的预解恒等式 + 唯一性 |

`R2` 用 ε–δ 形式而非 `Tendsto`，因为 `resolventCLM` 把 `0 < s` 作为参数携带，写成 `s ↦ J_s f` 需要依赖 `if`。
预期个别假设会像 `S2`/`S3` 一样多余（`V1` 的 `CompleteSpace H₁`、`R1`/`R3` 的 `Dense` 已经没写），
证明会话若发现更多，按惯例：证更强版本 + 逐字包装 + 记录。

## 分工

* 会话 A（von Neumann）：`V1`–`V5`，新模块 `Analysis/Semigroup/VonNeumann.lean`，审计 `research/audits/VonNeumannAudit.lean`。
* 会话 B（预解极限）：`R1`–`R3`，新模块 `Analysis/Semigroup/ResolventLimit.lean`，审计 `research/audits/ResolventLimitAudit.lean`。

两者互不依赖（`R` 系列不碰伴随）。规则同前：只建新文件、只用 `lake env lean -DwarningAsError=true`、
不 `lake build`、不 `verify.py`、不 git、不改任何既有文件、零 `sorry`。

## 明确没做什么

`S6`–`S8` 未证也未在此陈述。Markov 性、Γ 演算、小时间热估计、Buser 不等式均不在本轮。
`thm:logconcave-cheeger-poincare-comparison` 无进展标记，`tasks.json` 未改（集成时统一登记）。

## 追加：`V1`–`V5`、`R1`–`R3` 全部证出（同日，两个并行 Opus 会话，约 8 与 13 分钟）

新模块 `Analysis/Semigroup/VonNeumann.lean`（`V1`–`V5`）与 `Analysis/Semigroup/ResolventLimit.lean`（`R1`–`R3`），
审计 `research/audits/VonNeumannAudit.lean`（18 条 `#print axioms`）与 `ResolventLimitAudit.lean`（9 条），
**27 条报告全部只有 `propext, Classical.choice, Quot.sound`，0 条 `sorryAx`**；8 条路线语句逐 token 与路线文件一致
（本会话独立重编译并机械比对）。三个新模块已进聚合根，`lake build` 3524 jobs 通过，六个半群审计客户端严格重编译均 exit 0。

| 编号 | 声明 | 备注 |
| --- | --- | --- |
| `V1` | `inner_adjointComp` | **不需要 `CompleteSpace H₁` 与 `T.IsClosed`** |
| `V2` | `resolvent_add_smul_adjointComp`（+ `mem_adjointComp_domain_resolventDomain`） | 域的一半 `T(J_s f) ∈ D(T†)` **不需要 `Dense`**，审计记为 `route_V2_domain_of_not_dense` |
| `V3` | `isSelfAdjoint_adjointComp` | 见下 |
| `V4` | `dense_adjointComp_domain` | 直接证，见下 |
| `V5` | `sub_resolvent_eq_smul` | 按草稿 |
| `R1` | `norm_resolventCLM_sub_sq_le`（包装 `norm_resolventCLM_sub_sq_le_quarter`） | **常数实为 `s‖Tf‖²/4`**，路线的 `s‖Tf‖²` 作逐字包装 |
| `R2` | `exists_delta_norm_resolventCLM_sub_lt` | 按草稿，`δ = (ε/3)²/(‖Tg‖²+1)` |
| `R3` | `resolventCLM_comp_comm` | 证法与草稿不同，见下 |

### 三处与路线草稿不同

* **`V3 ⟹ V4` 的顺序是不可能的，已反转。** Mathlib 的 `LinearPMap.IsFormalAdjoint.le_adjoint` `include` 了 `Dense (T.domain)`，
  在 `T := adjointComp T` 处这恰是 `V4`，所以 `V3` 的证明必须先有 `V4`。`V4` 直接证（`g ⊥ D(T†T)`，
  由 `1 + T†T` 满射写 `g = x + T†T x`，则 `0 = ⟪x, g⟫ = ‖x‖² + ‖Tx‖²`），`V3` 由之导出。审计另给
  `dense_of_route_V3`（经 `IsSelfAdjoint.dense_domain`）与 `isClosed_of_route_V3`，保持两条目在表面上仍相互一致。
* **`R1` 的辅助界 `‖Tu‖ ≤ ‖Tf‖` 不需要。** 单次检验 `v = u − f` 加 `s(‖Tu‖ − ‖Tf‖/2)² ≥ 0` 直接给出常数 1/4。
* **`R3` 草稿里「用 `resolventCLM_symm` 收尾」是循环的**（对称性把命题映回自身）。实际证法：
  `z := s·J_s f − r·J_r f + (r−s)·J_s(J_r f)` 解数据为 0 的弱 `s`-方程（三条弱方程的一个 `linear_combination`），
  故 `z = 0`（`weakResolvent_unique`）；再由 `Tz = 0` 把 `w = J_s(J_r f)` 的 `r`-方程化为另一个 `linear_combination`，
  `eq_resolventDomain` 收尾。不需要 `r = s` 分情况，`resolventCLM_symm` 未用。

### 对 `S6` 的意义

`S6` 语句里假设的交换性 `(L s).comp (L r) = (L r).comp (L s)` 由 `R3` 对 `L_s = s⁻¹(1 − J_s)` 直接给出；
`L_s f → T†T f`（`f ∈ D(T†T)`）由 `V5` + `R2` 给出；`D(T†T)` 稠密由 `V4` 给出。`S6` 本身仍未证。

### 摩擦（供下一轮）

`real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫`，首个显式参数是左边的**第二**个位置；`Dense.exists_dist_lt` 在本 pin 不存在，
用 `Metric.mem_closure_iff.mp`；`lt_div_iff₀` 而非 `div_lt_iff₀`；子类型 eta（`T ⟨↑u, u.2⟩` 与 `T u`）让 `linarith` 视为不同原子，
用 `rfl`-`have` 或 `show` 统一。
