# 2026-09-11 — `cor:conditional-fiber-twelve-bound`：基础设施核对与陈述骨架（仅一条 sorry）

## 决定

- 按 atlas 顺序，`lem:conditional-fiber-energy-comparison` 注册后该推论由 `blocked` 变为可核对。核对结论：
  基础设施 **missing**（具体缺口见下），因此按 statement-only 流程只写陈述骨架，不做证明搜索。
- 新文件 `formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean`（命名空间
  `FunctionalInequalities.KLS.LogConcave`，对数凹推论按 `hμ.` 点记法调用）。**仅一条 `sorry`**：
  `ae_conditionalFiber_logConcave`。其余五条是对已认证输入的直接合成（证明体为一两行的应用），编译通过。
- 不注册（未加入 `FunctionalInequalities.lean` 聚合导入、lakefile `Solutions` 根、ledger、`CERTIFICATES`），
  Blueprint 的 `\lean{}`/`\leanok` 不加；`tasks.json` 该节点改为 `missing` 并登记缺口与证据哈希。
  未 `git commit`、未 `git push`。

## Lean 陈述

```
theorem ae_conditionalFiber_logConcave (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
    ∀ᵐ b ∂baseLaw μ ρ, LogConcave (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ)   -- sorry

theorem conditionalFiber_fiberBound_four … : FiberBound μ ρ 4
theorem conditionalFiber_energy_le_four_mul … (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ 4 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤
theorem conditionalFiber_literatureConstant_le_four_mul … (hform : ∀ f ∈ domain μ ρ, ↑(L2.variance μ f) ≤ ↑C * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * ↑C
theorem conditionalFiber_energy_le_twelve_mul_of_four … : energy μ ρ f ≤ 12 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤
theorem conditionalFiber_literatureConstant_le_twelve_mul_of_four … : Poincare.LocalSlope.Intrinsic.constant μ ≤ 12 * ↑C
```

`hμ`、`hρ` 与 `m`/`hac` 与比较引理的参数约定一致；`κ` 不再出现，常数 `4`/`12` 写在名字里（`research/naming.md`：
"常数 4 写在名字里，不另设参数"，"由 4 推出的版本带 `_of_four` 后缀"）。

## 逐句对齐（Blueprint ↔ Lean）

| Blueprint | Lean | 说明 |
|---|---|---|
| "For a full-dimensional log-concave law with finite second moment" | `hμ : LogConcave μ`、`hac : μ ≪ m`（Haar）、二阶矩来自 `hρ : Admissible μ ρ` | "full-dimensional" 读作绝对连续于 Haar（对数凹律等价于仿射支撑为全空间），与比较引理相同 |
| "$\mathcal D_{\mu,\rho}(f)\le12\int|\nabla f|^2\,d\mu$ on the literature test domain" | `conditionalFiber_energy_le_twelve_mul_of_four`（`Energy.LocalSlope.energy` 在 `hac` 下等于 `∫⁻ ‖∇f‖²`） | 一致；Lean 另给更强的 `4` 版本 |
| "A finite form-gap bound $C$ therefore gives $\CPLit(\mu)\le12C$" | `conditionalFiber_literatureConstant_le_twelve_mul_of_four` | 一致；Lean 另给 `4C` |
| 证明："conditional densities proportional to $t\mapsto\rho_\mu(z+t\theta)$ … These densities are log-concave. The remaining fibers are null" | `ae_conditionalFiber_logConcave`（**sorry**） | 这是唯一的解析内容 |
| 证明："finite second moment gives finite conditional variances almost everywhere" | `Nondegenerate` 的第二字段 + `ConditionalFiber.ae_memLp_id`（`FiberBound` 只约束非退化纤维，故无需单独证明） | 已含 |
| 证明："Apply thm:one-dimensional-logconcave-poincare and then the preceding comparison with κ=12" | `conditionalFiber_fiberBound_four`（用 `hν.localSlope_constant_le_four_evariance`）+ `energy_le_of_fiberBound`/`literatureConstant_le_of_fiberBound` | 一致，且输入为已证的 4 |
| "The same argument accepts any independently established smaller universal input" | 已由参数化的 `FiberBound μ ρ κ` 体现 | 一致 |

Blueprint 推论仍写 `12`；Lean 以 `4` 为主、`12` 为推论，Lean 强于 Blueprint。是否把 Blueprint 陈述改为 `4C`
（同日 `thm:one-dimensional-logconcave-poincare` 记录里预告的加强）是陈述变更，留给 owner 决定；本次未改。

## 基础设施缺口（`tasks.json`：`missing`）

1. **一维 Brunn–Minkowski / Prékopa–Leindler。** 需要"实轴上有对数凹 Lebesgue 密度（`IsBorellDensity`）的概率律是
   紧集对数凹（`KLS.LogConcave`）"。钉住的 Mathlib 没有 Brunn–Minkowski 或 Prékopa–Leindler（`grep` 到的 "Minkowski"
   均为 gauge 泛函，`Analysis/Convex/Gauge.lean`）；仓库只有反方向 `LogConcave.exists_lineDensity`。
2. **沿直线的显式分解。** 对每个方向 θ，Haar 测度沿正交分解 `E ≅ θ^⊥ × ℝθ` 的 Fubini 拆分（Mathlib 有固定正交基坐标的
   保测性 `OrthonormalBasis.measurePreserving_measurableEquiv`，没有随 θ 变化的拆分）；把归一化切片密度
   `t ↦ ρ_μ(z+tθ)` 做成固定乘积基 `Direction E × E` 上的 Markov 核；证明 `baseLaw ⊗ₘ 切片核 = jointLaw`。
   之后与所选核的 a.e. 相等由已有的 `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd` 给出
   （`ConditionalFiber.energyWithKernel_eq_energy` 已用同一模式）。
3. **a.e. 非退化。** 切片方差为正需要 Borell 密度在支撑内部为正（`BorellRepresentation.pos_of_mem_interior_support`）
   限制到直线上；有限二阶矩已由 `ae_memLp_id` 给出。

绕过 1 的可能路线：直接证明"对数凹律的条件律是对数凹的"（对 compact-set 定义直接做，无需密度），但这同样需要
Prékopa–Leindler 型论证；或者证明纯一维事实"对数凹密度 ⇒ 紧集对数凹"用一维 Brunn–Minkowski
（`vol(A+B) ≥ vol(A)+vol(B)`，Mathlib 亦无）。两者都是新的 Mathlib 级工作。

## 编译

```
lake env lean FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean
```

恰好 1 条 `declaration uses 'sorry'`（`ae_conditionalFiber_logConcave`），无其他警告。

## 未做 / 后续

- 未证 `ae_conditionalFiber_logConcave`；未注册；未改 Blueprint 陈述（`12` 与 `4C` 的取舍留给 owner）。
- 若缺口 1–3 补齐并证完：把本文件加入聚合导入，写 `solutions/CorConditionalFiberTwelveBound.lean` 证书，
  ledger/`CERTIFICATES`/route sidecar/Blueprint `\lean{}` 同步；届时 Blueprint 推论块可同时改为 `4C`。
