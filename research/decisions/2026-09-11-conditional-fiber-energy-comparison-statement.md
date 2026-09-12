# 2026-09-11 — `lem:conditional-fiber-energy-comparison`：陈述骨架（仅陈述，无证明）

## 决定

- 为 Blueprint `formalization/blueprint/src/chapters/50-kls-routes.tex`（`lem:conditional-fiber-energy-comparison`,
  L383–397）写出 Lean 陈述骨架，两条 `theorem`，证明体均为 `sorry`，放在新文件
  `formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean`。
- 未改任何既有定义/定理的类型（`Admissible`、`Nondegenerate`、`baseLaw`、`kernel`、`energy`、`form`、`domain`、
  `Poincare.LocalSlope.Intrinsic.constant`、`Energy.LocalSlope.Admissible`/`.energy`、`L2.variance` 均直接复用）。
- 新增一个局部谓词 `FiberBound`（打包 Blueprint 的逐纤维假设），不是 Blueprint 显式命名的对象，但只是对
  展示的不等式的直接转录。
- 未注册（未加入 `formalization/FunctionalInequalities.lean` 聚合导入、`lakefile.toml` 的 `Solutions` 根、
  `research/a-series/ledger.yaml`、`research/check_blueprint.py` 的 `CERTIFICATES`、`research/tasks.json`）；
  未改 Blueprint 的 `\lean{}`/`\leanok`（与另一会话对 `RelativePerimeter.lean`/`Cheeger.lean` 的处理方式一致：
  锚点等证明落地后再加）。未 `git commit`、未 `git push`、未改任何共享文件。

## Lean 陈述

```
def FiberBound (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E)) (κ : NNReal) : Prop :=
  ∀ᵐ b ∂baseLaw μ ρ, Nondegenerate (kernel μ ρ) b →
    Poincare.LocalSlope.Intrinsic.constant
        (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ) ≤
      (κ : ENNReal) * evariance id (kernel μ ρ b)

theorem energy_le_of_fiberBound (μ ρ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m)
    {κ : NNReal} (hfiber : FiberBound μ ρ κ)
    {f : E → ℝ} (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ (κ : ENNReal) * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤

theorem literatureConstant_le_of_fiberBound (μ ρ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m)
    {κ : NNReal} (hfiber : FiberBound μ ρ κ)
    {C : NNReal} (hform : ∀ f ∈ domain μ ρ, (L2.variance μ f : ENNReal) ≤ (C : ENNReal) * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (κ : ENNReal) * (C : ENNReal)
```

`E` carries the same instance stack as the base `ConditionalFiber` module plus
`[CompleteSpace E] [FiniteDimensional ℝ E]`, needed by `Poincare.LocalSlope.Intrinsic.constant`.

## 逐句对齐（Blueprint ↔ Lean）

| Blueprint | Lean | 说明 |
|---|---|---|
| "Let $d\ge1$" | `Admissible.positive_dimension` (`0 < Module.finrank ℝ E`) | 用一般有限维 `E` 而非固定 `ℝ^d`，一致；`d` 就是 `finrank ℝ E` |
| "$\mu\ll\mathrm{Leb}_{\mathbb R^d}$" | `(m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ:Measure E) ≪ m)` | 用一般 Haar 参考测度代替固定 Lebesgue（欧氏空间上二者相差常数倍），与 `Energy.LocalSlope.Gradient` 的既有约定一致 |
| "have finite second moment" | `Admissible.memLp_two` | 已含于既有字段，未重复要求 |
| "$\rho$ be an admissible frame" | `hρ : Admissible μ ρ` | 一致 |
| "one finite $\kappa\ge0$ satisfies $C_P^{lit}(\mu_{\theta,z})\le\kappa\Var_{\mu_{\theta,z}}(T)$ for a.e. nondegenerate fiber" | `FiberBound μ ρ κ` | `κ b` 是纤维律 `μ_{θ,z}`（Markov 核给出概率测度实例）；`Poincare.LocalSlope.Intrinsic.constant` 是既有 `C_P^{lit}`；`evariance id (kernel μ ρ b)` 是 `Var_{μ_{θ,z}}(T)`（`energyAt` 分母同一对象） |
| "Every locally Lipschitz $f\in L^2(\mu)$ with finite gradient energy" | `Energy.LocalSlope.Admissible μ f` | 既有结构，正是"局部 Lipschitz + $L^2$ + 有限梯度能量"三个字段的打包 |
| "$\mathcal D_{\mu,\rho}(f)\le\kappa\int\norm{\nabla f}^2\dd\mu<\infty$" | `energy_le_of_fiberBound` 的结论（合取的两部分） | `energy μ ρ f` 是 `KLS.ConditionalFiber.energy`（$\mathcal D_{\mu,\rho}$ 的既有裸函数版本）；`Energy.LocalSlope.energy μ f` 在 `hac` 下经 `Energy.LocalSlope.Gradient.energy_eq_lintegral_gradient` 等于 $\int\norm{\nabla f}^2\dd\mu$，故 RHS 一致；"$<\infty$" 就是 `≠⊤` 合取项 |
| "Hence $\Var_\mu(f)\le C\mathcal D_{\mu,\rho}(f)$ on the maximal finite form domain, for finite $C\ge0$, implies $C_P^{lit}(\mu)\le\kappa C$" | `literatureConstant_le_of_fiberBound` | `domain μ ρ`（既有，"maximal finite form domain"）、`form μ ρ`（既有，$L^2$ 类版本的 $\mathcal D_{\mu,\rho}$）、`L2.variance μ`（既有，$\Var_\mu$，`NNReal` 值故显式转 `ENNReal`）；结论中 `Poincare.LocalSlope.Intrinsic.constant μ` 就是 `μ` 自身（未取内在化约化前）的 $C_P^{lit}(\mu)$ |

未主张：`\uses` 列出的 `lem:finite-energy-factor-poincare`（`Poincare.L2Energy.Holds.of_energy_le_mul`/
`constant_le_mul_of_energy_le_mul`）本身；这是证明将使用的抽象工具，陈述层面无需出现其具体类型。也未涉及
`cor:conditional-fiber-twelve-bound` 的具体数值 `κ=12`（或已证的 `4`），未处理 `d=0` 退化情形（`Admissible` 已经
排除 `finrank=0`，与 Blueprint 前置的"零维单独处理"一致）。

## 编译

```
lake env lean FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
```

恰好 2 条 `declaration uses 'sorry'` 警告（`energy_le_of_fiberBound`、`literatureConstant_le_of_fiberBound`），
无其他警告；`lake env lean -DwarningAsError=true ...` 同样恰好给出这 2 条（提升为 error），无其他诊断。
（本机 CommandLineTools 的 x86_64 lake / arm64 xcrun 不兼容问题沿用同日其他会话的绕过方式：在 PATH 前插入
一个只 `exec` `/Library/Developer/CommandLineTools/usr/bin/git` 的包装脚本目录，并设置 `GIT_EXEC_PATH`/
`GIT_TEMPLATE_DIR`，未改仓库内容。）

## 未做 / 后续

- 未填 sorry；未注册；未提交、未推送；未改 Blueprint、`FunctionalInequalities.lean`、`lakefile.toml`、
  `solutions/README.md`、`research/tasks.json`、`research/a-series/ledger.yaml` 等共享文件。
- 交给证明会话的提示词见同日
  [`2026-09-11-conditional-fiber-energy-comparison-sorry-prompt.md`](2026-09-11-conditional-fiber-energy-comparison-sorry-prompt.md)。
- 若证完：`cor:conditional-fiber-twelve-bound` 可用 `κ=4`（已证的 `thm:one-dimensional-logconcave-poincare`
  锐常数）实例化 `literatureConstant_le_of_fiberBound`，把 Blueprint 现有的"`12C`"分析推论也升级为 Lean 证明。
