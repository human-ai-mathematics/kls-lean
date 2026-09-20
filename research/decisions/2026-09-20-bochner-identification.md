# Bakry–Émery 路线：`B0`–`B4` 已证——局部 `Γ`/`Γ₂` 计算与 Bochner 恒等式

2026-09-20，紧接同日的[生成元识别记录](2026-09-20-generator-identification.md)，是
[完整 Buser 交接](2026-09-20-buser-handoff-prompt.md)的第二个内部里程碑。本轮是**实际 Lean 证明**：
`research/audits/BakryEmeryRouteStatements.lean` 中的 `B0`、`B1`、`B3`、`B4` 逐字被消解，`B2` 复用既有的
`bilinearIteratedFDerivTwo_symm`。全部结论是有限维欧氏空间上光滑函数的**点态微分恒等式**；不证明也不声称任何
半群梯度估计、一般对数凹律逼近或 Buser 拼装。不 commit、不推送；工作区其他未提交修改全部保留。

## 结果

两个新模块，均零 `sorry`、零自定义公理，`-DwarningAsError=true` 下零警告。

| 模块 / 声明 | 内容 |
| --- | --- |
| `Analysis/BakryEmery/Gamma.lean` | |
| `gamma f g x := ⟪∇f x, ∇g x⟫` | carré du champ，几何定义 |
| `gamma_self`、`gamma_self_fun` | `Γ(f,f) = ‖∇f‖²`（无额外因子） |
| `weightedLaplacian_mul` | `ℒ(fg) = f ℒg + g ℒf + 2 Γ(f,g)`，`f, g ∈ C²`，`U` 任意 |
| `gamma_eq_weightedLaplacian` | **`B0`**：`(ℒ(fg) - f ℒg - g ℒf)/2 = Γ(f,g)` |
| `gammaTwo U f x := ℒ(Γ(f,f)) x / 2 - Γ(f, ℒf) x` | 扩散约定下的 `Γ₂`；`Γ(f, ℒf)` 按几何定义读作 `⟪∇f, ∇(ℒf)⟫`，不需要 `C⁴` |
| `gammaTwo_eq_expanded` | `Γ₂` 展开为 `(Δ‖∇f‖² - ⟪∇U,∇‖∇f‖²⟫)/2 - ⟪∇f, ∇(Δf - ⟪∇U,∇f⟫)⟫`，即路线文件 `B3` 左端 |
| `contDiff_fderiv_apply`、`differentiable_fderiv_apply`、`fderiv_fderiv_apply`、`bilinearIteratedFDerivTwo_eq_fderiv_apply` | 方向导数 `y ↦ Df(y)v` 的正则性；`D²f(x)(v,w) = D(y ↦ Df(y)w)(x)v` |
| `fderiv_apply_comm` | `B2` 的方向导数形式：`∂ᵥ∂_w f = ∂_w∂ᵥ f`（`C²`） |
| `fderiv_fderiv_fderiv_apply_comm` | 三阶交换 `∂_w∂ᵥ∂ᵥ f = ∂ᵥ∂ᵥ∂_w f`（`C³`） |
| `fderiv_mul_apply`、`fderiv_const_mul_apply`、`fderiv_sum_apply`、`fderiv_sub_apply`、`fderiv_add_apply` | 方向导数的乘积、常数倍、和、差法则 |
| `contDiff_gradient`、`gradient_mul`、`gradient_sub` | 梯度正则性与乘积、差法则 |
| `gradient_eq_sum_fderiv_smul`、`norm_gradient_sq_eq_sum`、`bilinearIteratedFDerivTwo_gradient_gradient`、`bilinear_sum_smul_sum_smul` | `∇f = Σᵢ ∂ᵢf eᵢ`，`‖∇f‖² = Σᵢ (∂ᵢf)²`，`D²U(∇f,∇f) = Σᵢ Σⱼ ∂ᵢf ∂ⱼf D²U(eᵢ,eⱼ)` |
| `laplacian_eq_sum_fderiv_apply_fderiv_apply`、`laplacian_eq_fun_sum`、`contDiff_laplacian`、`laplacian_mul` | `Δg = Σᵢ ∂ᵢ∂ᵢ g`（点态与函数级）、`Δ` 的正则性、`Δ(fg) = fΔg + gΔf + 2⟪∇f,∇g⟫` |
| `Analysis/BakryEmery/Bochner.lean` | |
| `convexOn_line`、`hasDerivAt_line`、`deriv_line`、`deriv_deriv_line` | 直线限制 `t ↦ U(x + t v)` 的凸性、一阶导 `DU(x+tv)v`、二阶导在 `0` 处等于 `D²U(x)(v,v)` |
| `bilinearIteratedFDerivTwo_nonneg_of_convexOn` | **`B1`**：`C²` 凸 `U` ⟹ `0 ≤ D²U(x)(v,v)` |
| `hessianSqStdBasis f x := Σᵢ Σⱼ (D²f(x)(eᵢ,eⱼ))²`、`hessianSqStdBasis_nonneg` | **固定标准正交基**下的 Hessian 平方和 |
| `fderiv_norm_gradient_sq_apply`、`inner_gradient_gradient_norm_sq`、`laplacian_norm_gradient_sq`、`inner_gradient_gradient_laplacian`、`inner_gradient_gradient_inner` | `Γ₂` 四项的坐标展开（见下） |
| `gammaTwo_eq_hessianSqStdBasis_add` | **`B3`（`Γ₂` 形式）**：`Γ₂(f) = hessianSqStdBasis f + D²U(∇f,∇f)`，`U ∈ C²`，`f ∈ C³` |
| `bochner_stdBasis` | **`B3`（展开形式，逐字候选）**，`U, f ∈ C³` |
| `gammaTwo_nonneg`、`bochner_nonneg_stdBasis` | **`B4`**：凸 `U` ⟹ `0 ≤ Γ₂(f)`（两种形式） |
| `gammaTwo_zero_potential`、`bilinearIteratedFDerivTwo_affine`、`hessianSqStdBasis_affine`、`gammaTwo_affine`、`gammaTwo_of_subsingleton` | 边界情形：`U = 0` 退化为欧氏 Bochner；仿射 `f` 的 Hessian 平方为零、`Γ₂ = D²U(∇f,∇f)`；零维空间 `Γ₂ = 0` 且不需任何正则性 |

审计 `research/audits/BakryEmeryBochnerAudit.lean` 逐字重述路线文件的 `B0`–`B4` 为 `route_B0`–`route_B4`（各一个 `exact`），
另给 `Γ₂` 形式 `route_B3_gammaTwo`、`route_B4_gammaTwo`，以及边界检查 `boundary_euclidean`（`U = 0`）、`boundary_affine`、
`boundary_zero_dim`、`boundary_affine_nonneg`、`boundary_one_dim_value`、`boundary_one_dim_hessianSq`；
**70 条 `#print axioms` 全部标准（`propext`、`Classical.choice`、`Quot.sound`），0 `sorryAx`**。
`BakryEmeryRouteStatements.lean` 加入新声明的 `#check @…`，`B0`–`B4` 段落注明消解声明；匿名候选命题原样保留，零错误零警告。

实际使用的正则性弱于候选：`B0` 不需要 `U` 的任何正则性；`B3`、`B4` 的 `Γ₂` 形式只需 `U ∈ C²`。审计把候选的 `C²`/`C³` 降到这些阶数后逐字重述。

## 符号与归一化

- 扩散生成元 `ℒf = weightedLaplacian U f = Δf - ⟪∇U, ∇f⟫`；半群的非负算子 `A = T̄†T̄` 只在 `G1` 已识别的光滑测试函数上等于 `-ℒ`。本轮所有声明只涉及 `ℒ`，不涉及 `A`。
- `Γ(f,g) = ⟪∇f, ∇g⟫`；`B0` 给出 `Γ = (ℒ(fg) - fℒg - gℒf)/2`，因子 `1/2` 与 `Δ(fg) = fΔg + gΔf + 2⟪∇f,∇g⟫` 中的 `2` 精确抵消，`Γ(f,f) = ‖∇f‖²`。
- `Γ₂(f) = ℒ(Γ(f,f))/2 - Γ(f, ℒf)`。`B3` 右端 `Σᵢ Σⱼ (D²f(eᵢ,eⱼ))² + D²U(∇f,∇f)` 的两项都带正号；对凸 `U` 两项都非负，故 `B4` 的方向是 `0 ≤ Γ₂`，没有符号反转。
- 独立数值核对（`boundary_one_dim_value`）：在 `ℝ` 上取 `U = 0`、`f(t) = t²`，**不经由 `B3`**，直接用 Mathlib 的 `laplacian_eq_iteratedDeriv_real` 与 `gradient_eq_deriv'` 计算得 `Γ₂(f)(0) = 8/2 - 0 = 4`，与 `B3` 右端 `(f'')² = 4` 一致。若因子 `1/2` 缺失将得 `8`，若符号反转将得 `-4`。

## 证明结构

全部计算在固定的标准正交基 `eᵢ = stdOrthonormalBasis ℝ E i` 中以方向导数 `∂ᵢ g := y ↦ Dg(y)eᵢ` 进行：
`∇g = Σᵢ ∂ᵢg eᵢ`，`‖∇f‖² = Σⱼ (∂ⱼf)²`，`Δg = Σᵢ ∂ᵢ∂ᵢg`，`⟪∇U,∇f⟫ = Σᵢ ∂ᵢU ∂ᵢf`，Hessian `D²f(eᵢ,eⱼ) = ∂ᵢ∂ⱼf`
（`bilinearIteratedFDerivTwo` 在定义上就是 `fderiv (fderiv f)`，`bilinearIteratedFDerivTwo_eq_fderiv_apply` 把它换成迭代方向导数）。
在点 `x` 处记 `aⱼ = ∂ⱼf`，`bᵢⱼ = ∂ᵢ∂ⱼf`，`cᵢⱼ = ∂ᵢ∂ᵢ∂ⱼf`，`uᵢ = ∂ᵢU`，`wᵢⱼ = ∂ᵢ∂ⱼU`：

| 项 | 展开 | 声明 |
| --- | --- | --- |
| `Δ‖∇f‖²` | `2 Σᵢ Σⱼ bᵢⱼ² + 2 Σⱼ aⱼ Σᵢ cᵢⱼ` | `laplacian_norm_gradient_sq` |
| `⟪∇U, ∇‖∇f‖²⟫` | `2 Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ` | `inner_gradient_gradient_norm_sq` |
| `⟪∇f, ∇(Δf)⟫` | `Σⱼ aⱼ Σᵢ ∂ⱼ∂ᵢ∂ᵢf = Σⱼ aⱼ Σᵢ cᵢⱼ` | `inner_gradient_gradient_laplacian` |
| `⟪∇f, ∇⟪∇U,∇f⟫⟫` | `Σⱼ aⱼ Σᵢ (uᵢ bⱼᵢ + aᵢ wⱼᵢ) = D²U(∇f,∇f) + Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ` | `inner_gradient_gradient_inner` |

于是 `Γ₂ = (2S + 2T - 2M)/2 - (T - H - M) = S + H`，其中 `S = Σᵢ Σⱼ bᵢⱼ²`、`T = Σⱼ aⱼ Σᵢ cᵢⱼ`、`M = Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ`、
`H = D²U(∇f,∇f)`，最后一步是 `ring`。

**三阶导数的抵消。** `Δ‖∇f‖²/2` 贡献 `Σⱼ aⱼ Σᵢ ∂ᵢ∂ᵢ∂ⱼf`，`⟪∇f, ∇Δf⟫` 贡献 `Σⱼ aⱼ Σᵢ ∂ⱼ∂ᵢ∂ᵢf`。
`fderiv_fderiv_fderiv_apply_comm`（`f ∈ C³`）证明 `∂ⱼ∂ᵢ∂ᵢf(x) = ∂ᵢ∂ᵢ∂ⱼf(x)`：先对 `C²` 函数 `g = ∂ᵢf` 用 `B2` 的方向形式
`fderiv_apply_comm` 交换两个外层导数，`∂ⱼ∂ᵢg = ∂ᵢ∂ⱼg`；再在每一点用 `B2` 交换 `f` 的两个内层导数，`∂ⱼ∂ᵢf = ∂ᵢ∂ⱼf`
（函数级 `funext`），从而 `∂ᵢ(∂ⱼ∂ᵢf) = ∂ᵢ(∂ᵢ∂ⱼf)`。两项因此逐字相同并抵消；没有加强结论，也没有隐藏假设。

**漂移项。** `-⟪∇U,∇‖∇f‖²⟫/2 = -Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ`，`+⟪∇f, ∇⟪∇U,∇f⟫⟫ = Σⱼ Σᵢ aⱼ uᵢ bⱼᵢ + Σⱼ Σᵢ aⱼ aᵢ wⱼᵢ`；
用 `B2`（`bᵢⱼ = bⱼᵢ`）第一部分与前者抵消，剩余 `Σⱼ Σᵢ aⱼ aᵢ wⱼᵢ = D²U(∇f,∇f)`（`bilinearIteratedFDerivTwo_gradient_gradient`），
符号为 `+`。

**`B1`。** 固定 `x v`，`φ(t) = U(x + t v)`。`convexOn_line` 直接由 `ConvexOn` 定义得到 `φ` 在 `ℝ` 上凸（没有用 `comp_affineMap`，因其实例转换在 `convert` 下产生无关的实例目标）；
`ConvexOn.monotoneOn_deriv` 给出 `φ'` 单调，`Monotone.deriv_nonneg` 给出 `φ''(0) ≥ 0`；
`deriv_deriv_line` 用 `HasFDerivAt.comp_hasDerivAt` 与 `HasDerivAt.clm_apply` 证明 `φ''(0) = D²U(x)(v,v)`。
pinned Mathlib 没有现成的“`C²` 凸函数 Hessian 半正定”定理，故按此路线证明；结论对所有方向 `v`，不只坐标方向。

## 实际使用的 Mathlib 微分 API

`bilinearIteratedFDerivTwo`（`Mathlib.Analysis.InnerProductSpace.Laplacian`，定义为 `(fderiv (fderiv f) x).toLinearMap₁₂`）、
`laplacian_eq_iteratedFDeriv_orthonormalBasis`（经既有 `laplacian_eq_sum_fderiv_fderiv`）、`laplacian_eq_iteratedDeriv_real`（仅一维核对）、
`fderiv_fun_mul`、`fderiv_const_mul`、`fderiv_fun_sum`、`fderiv_fun_add`、`fderiv_fun_sub`、`fderiv_fun_const`、
`HasFDerivAt.clm_apply`、`ContDiff.fderiv_right`、`ContDiff.clm_apply`、`ContDiff.sum`、`ContDiff.mul`、`ContDiff.norm_sq`、`ContDiff.inner`、
`inner_gradient_left`、`gradient_fun_const`、`gradient_eq_deriv'`、`OrthonormalBasis.sum_repr'`、`OrthonormalBasis.sum_sq_inner_left`、
`ConvexOn.monotoneOn_deriv`、`Monotone.deriv_nonneg`、`HasFDerivAt.comp_hasDerivAt`、`HasDerivAt.clm_apply`、`monotoneOn_univ`，
以及本仓库已有的 `bilinearIteratedFDerivTwo_symm`（`B2`）、`inner_gradient_eq_sum_fderiv_mul_fderiv`、`laplacian_eq_sum_fderiv_fderiv`。

## 边界：固定基与不变的 Hilbert–Schmidt 范数

`hessianSqStdBasis f x = Σᵢ Σⱼ (D²f(x)(eᵢ,eⱼ))²` 中的基是 `stdOrthonormalBasis ℝ E`。**本轮没有证明这个双重和与正交基的选取无关**，
因此不引入 `‖Hess f‖²_HS` 之类的不变记号，公开名称保留 `StdBasis`；`B3` 的公开陈述也按路线文件固定标准基。
基无关性（或改用 `Hess f` 作为 `E →L E` 的 Hilbert–Schmidt 范数）是独立义务。

## 零维情形

`E` 为 `Subsingleton` 时 `Fin (finrank ℝ E)` 为空，两个双重和为空和；`gammaTwo_of_subsingleton` 证明 `Γ₂ = 0`，对任意 `U f`、无正则性假设
（任何函数都是常值）。`B3`、`B4` 的一般证明本身不用正维数或基非空。

## 这意味着什么、不意味着什么

已证：有限维欧氏空间上、光滑函数的点态恒等式 `B0`–`B4`。未证也未声称：

- `‖∇P_t f‖² ≤ P_t(‖∇f‖²)` 或 `‖∇P_t f‖ ≤ P_t(‖∇f‖)`（`S0` 的两种候选）；
- `t > 0` 时 `P_t[f]` 的光滑代表；`D(A)` 或闭梯度域在 `P_t` 下稳定；
- 对 `s ↦ P_s Γ(P_{t-s}f)` 求导、积分与极限交换；
- 一般（非光滑、带边界、低维支撑）对数凹律；`C_c^∞` 是 `A` 的 operator core；
- Buser 不等式或常数 `π`。

`thm:logconcave-cheeger-poincare-comparison` 仍无 `\leanok`，26 个证书与 `KLS/Target.lean` 的目标洞不变。

## 状态三栏

| 已有证明 | 仅类型检查 | 仍是非形式化方案 |
| --- | --- | --- |
| `G0`、`G1`、`B2`、`E0`；本轮 `B0`、`B1`、`B3`（固定标准基）、`B4` | `N0` 光滑 tilted 概率模型包 | `hessianSqStdBasis` 的基无关性 |
| 半群生成、`L²` Markov 性、闭梯度能量 `= E^can = 2 Ch` | `S0`：`P_t f` 光滑代表；平方 `Γ` 估计与 `L¹` 梯度交换两种候选 | 半群正则性、域稳定、时间微分、自改进、BGL 反向估计 |
| Cheeger 半与一维常数 12 | — | 一般测度逼近（Mosco/预解/半群/BV 稳定性）及 Buser 拼装 |

## 摩擦记录

- `ContDiff.differentiable` 的第二个参数是 `n ≠ 0`，不是 `≤`；写 `one_ne_zero`。
- `ContDiff.norm_sq`、`ContDiff.inner` 的域 `𝕜` 需显式：`hg.norm_sq (𝕜 := ℝ)`、`hgU.inner ℝ hgf`；且需 `import Mathlib.Analysis.InnerProductSpace.Calculus`；`ConvexOn.monotoneOn_deriv` 需 `import Mathlib.Analysis.Convex.Deriv`。
- `contDiff_of_subsingleton` 要求**值域**平凡；对定义域平凡的情形改写 `f = fun _ => f x` 后用 `contDiff_const`。
- `Fin (finrank ℝ E)` 上 `rw [finrank_zero_of_subsingleton]` 触发 motive 错误；改用 `omega` 处理 `↑i < finrank ∧ finrank = 0`。
- `DifferentiableAt.mul` 若无期望类型会得到 `f * fun y => …` 而非 `fun y => f y * …`，导致 `rw` 找不到模式；用带类型标注的 `have`。
- `simp only [map_sum, …]` 在双线性形式上会调换双重和顺序，随后需 `Finset.sum_comm`。
- `contDiff_id.pow 2` 的类型是 `fun x => id x ^ 2`；需先 `have hf : ContDiff ℝ 3 (fun t : ℝ => t ^ 2) := contDiff_id.pow 2`。

## 验证与复现

从 `formalization/`：

```bash
lake env lean -DwarningAsError=true FunctionalInequalities/Analysis/BakryEmery/Gamma.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Analysis/BakryEmery/Bochner.lean
lake env lean -DwarningAsError=true ../research/audits/BakryEmeryBochnerAudit.lean
lake env lean -DwarningAsError=true ../research/audits/BakryEmeryRouteStatements.lean
lake build
```

四个文件零错误零警告；审计 70 条公理报告全部标准，0 `sorryAx`。默认 `lake build` **3550 jobs** 通过
（聚合根 `FunctionalInequalities.lean` 新增 `BakryEmery/Gamma`、`BakryEmery/Bochner`），其中唯一的 `sorry` 警告仍是 `KLS/Target.lean` 的目标洞。

从仓库根：

```bash
git diff --check
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests
python3 research/verify.py
```

`check_ledger.py` 26 个证书 0 错误；`check_blueprint.py` 88 个标签 0 错误；`atlas.py check` 75 个节点、26 个证书、无环；104 个单元测试。
`tasks.json` 中 `thm:logconcave-cheeger-poincare-comparison` 的 infrastructure 证据加入本轮文件的 sha256（`BakryEmeryRouteStatements.lean`
的哈希同步刷新），第一条缺口改写为剩余义务；进度图 `BE` 节点保持 partial、描述更新，视图按 `AGENTS.md` 从临时索引中暂存的 canonical records
重新生成，真实索引不变。根 `python3 research/verify.py` 在本轮末重跑，其收据记录在 `build/audit/bochner-identification/final-snapshot.json`。

## 下一步

半群侧的最小下一任务是路线记录第 6 节的第 1–2 项：**`t > 0` 时 `P_t[f]` 的正则代表与 `P_t` 对 `D(T̄)` 的保持**。
在没有这两项之前，`B4` 的 `Γ₂ ≥ 0` 无法接到 `Γ(P_t f) ≤ P_t Γ(f)`：插值量 `s ↦ P_s Γ(P_{t-s} f)` 的时间微分需要 `P_{t-s} f` 至少 `C³`
且其 `Γ`、`ℒ` 落回 `L²`。可先证明的独立局部片段是 `hessianSqStdBasis` 的基无关性（把 `B3` 右端改写为不变量），
但它不是半群接口的阻塞项。第 3、4 层（operator core、闭包等同）如需使用须单独证明。
