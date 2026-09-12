# 2026-09-11 — 交给证明会话的提示词：填 `KLS/ConditionalFiber/EnergyComparison.lean` 的 sorry

以下提示词可直接复制给另一个模型/会话。

---

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交
db584cd6d46c92f209a44c0f1c829460d327499d；Lake 根目录 formalization/）。

任务：填写 formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean 中的 2 条
sorry。该文件是 Blueprint 节点 lem:conditional-fiber-energy-comparison
（formalization/blueprint/src/chapters/50-kls-routes.tex，L383–397）的陈述骨架；设计与逐句对齐见
research/decisions/2026-09-11-conditional-fiber-energy-comparison-statement.md。先读这两个文件、
formalization/FunctionalInequalities/KLS/ConditionalFiber.lean、
formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean、
formalization/FunctionalInequalities/Energy/LocalSlope/{Basic,Gradient}.lean、
formalization/FunctionalInequalities/Poincare/LocalSlope/Basic.lean 的模块文档。

规则：
1. 不改 EnergyComparison.lean 里两个 theorem（或 FiberBound）的类型。若确认某条为假或不可证，不要改类型：
   在报告里写明反例/障碍并保留 sorry。允许加 private 辅助引理、允许加 import、允许在必要时把大证明拆成
   本文件内的多条私有引理。
2. 命名遵守 research/naming.md。
3. 只在这个文件内工作。不要加进 formalization/FunctionalInequalities.lean、lakefile 的 Solutions 根、
   research/a-series/ledger.yaml、research/check_blueprint.py 的 CERTIFICATES、research/tasks.json、
   Blueprint 的 \lean{}/\leanok。不 git commit、不 git push。决定记录只追加（新建
   research/decisions/2026-09-1X-conditional-fiber-energy-comparison-proofs.md）。
4. 编译命令（在 formalization/ 下）：
     lake env lean FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
   目标：无错误，填完后不再出现 "declaration uses 'sorry'"，无 unusedSectionVars 等其他警告。全部完成后
     lake env lean -DwarningAsError=true FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
   并对填完的每个顶层定理 #print axioms，只允许 propext / Classical.choice / Quot.sound。
5. 若本机 lake 报 `external command 'git' exited with code 1`（CommandLineTools 的 x86_64 lake 与 arm64
   xcrun 不兼容）：在 PATH 前插入一个只 `exec /Library/Developer/CommandLineTools/usr/bin/git "$@"` 的
   包装脚本所在目录，并设置 GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core、
   GIT_TEMPLATE_DIR=/Library/Developer/CommandLineTools/usr/share/git-core/templates。不要改仓库内容
   或系统 git 配置。

两条义务，建议顺序：先做 energy_le_of_fiberBound（更难，是核心分析论证），
literatureConstant_le_of_fiberBound 主要是把它和一个抽象合成引理粘起来。

## 义务 1：`energy_le_of_fiberBound`

目标：`energy μ ρ f ≤ κ * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤`。

建议路线（对应 Blueprint 证明段落 "A finite upper bound... Dividing the assumed fiber inequality..."）：

1. 展开 `energy μ ρ f = energyWithKernel μ ρ (kernel μ ρ) f
   = (finrank ℝ E : ENNReal) * ∫⁻ b, energyAt (kernel μ ρ) b f ∂baseLaw μ ρ`（`energy`、`energyWithKernel` 的
   定义已展开一半，见 ConditionalFiber.lean）。
2. 逐纤维不等式（a.e. `b`，`Nondegenerate` 时）：
   - `hf.locallyLipschitz` 沿方向 `b.1.1` 限制到直线 `t ↦ f (reconstruct b t)` 仍是（一元）局部 Lipschitz
     （`reconstruct b` 是仿射，`LocallyLipschitz.comp`／直接展开定义）。
   - 用 Rademacher 沿这条直线：类比 `Energy.LocalSlope.Gradient.apply_ae_eq_norm_gradient`（一维版本，或者
     直接对 `f` 本身用该引理得到 `apply f x = ofReal ‖gradient f x‖` a.e.，再证明一元切片的局部斜率
     `apply (fun t ↦ f (reconstruct b t)) t = ofReal |⟪gradient f (reconstruct b t), b.1.1⟫|`——链式法则，
     `HasFDerivAt.comp`／`fderiv_comp`，`reconstruct b` 的导数是 `t ↦ t • b.1.1` 方向）。这一步目前仓库里没有
     现成引理，需要新写（可放在本文件，或如果通用则放 Energy/LocalSlope/Gradient.lean，但规则 3 要求不改
     共享文件，故先放本文件的 private 引理）。
   - 应用 Blueprint 假设 `hfiber` 于该 `b`：`Poincare.LocalSlope.Intrinsic.constant ⟨kernel μ ρ b,_⟩ ≤
     κ * evariance id (kernel μ ρ b)`。`Intrinsic.constant` 是 `⨅ C : {C // Holds ...}, C` 的下确界；要把它
     转成"对这一个具体测试 `t ↦ f(reconstruct b t)` 的不等式"，需要形如
     "`Poincare.LocalSlope.Intrinsic.constant ν ≤ X → ∀ g, Admissible ν g → evariance g ν ≤ X * energy ν g`"
     的引理（当前 Poincare/LocalSlope/Basic.lean 没有；`Intrinsic.constant` 本身用 `intrinsicMeasure`，对
     `ν : ProbabilityMeasure ℝ` 需要先确认 `intrinsicMeasure ν` 与 `ν` 本身重合，或者绕过 `Intrinsic.constant`
     直接用 `Poincare.LocalSlope.Holds` 的定义展开——这是本义务里最需要小心处理的一步，可能需要一条新的
     private 引理，例如用 `iInf` 的下确界性质：`Intrinsic.constant ν ≤ X` 且 `Holds` 对 `C` 单调（`C ≤ C' →
     Holds ν C → Holds ν C'`——检查 Poincare/LocalSlope/Basic.lean 是否已有；若无需要证）配合
     `ENNReal.le_iInf_iff`／取标准的"任意 `ε>0` 存在 `C < X+ε` 使 `Holds C`"再让 `ε→0`（配合 `evariance`
     关于 `f` 的具体一个测试是不依赖 `ε` 的常数，可以直接用 `ENNReal.le_of_forall_pos_le_add` 或
     `le_iInf_iff` 之类，把整条不等式在 `f` 固定后转成 `evariance ... ≤ X * energy ...` 而不产生 `ε` 剩余项——
     注意 `X = κ * evariance id (kernel μ ρ b)` 本身可能是 `⊤`（不太可能，因 `Nondegenerate` 给了
     `MemLp id 2`），一般情形请显式处理 `X = 0` 与 `X = ⊤` 的退化分支）。
   - 除以 `evariance id (kernel μ ρ b) > 0`（`Nondegenerate` 的第三个字段给出 `≠ 0`；`ENNReal` 上除法用
     `ENNReal.div_le_iff` 一类），得到 `energyAt (kernel μ ρ) b f ≤ κ * ∫⁻ t, ⟪∇f(reconstruct b t), b.1.1⟫² d(kernel μ ρ b)`。
3. 把第 2 步的逐纤维界代入第 1 步的 `∫⁻ b ... ∂baseLaw`，得到
   `energy μ ρ f ≤ κ * finrank ℝ E * ∫⁻ b, ∫⁻ t, ⟪∇f(reconstruct b t), b.1.1⟫² d(kernel μ ρ b) ∂baseLaw μ ρ`。
   用 `compProd_baseLaw_kernel`（`baseLaw μ ρ ⊗ₘ kernel μ ρ = jointLaw μ ρ`）把双重积分写成对 `jointLaw` 的
   单个 lintegral（`Measure.lintegral_compProd`），再用 `jointLaw μ ρ = (ρ.prod μ).map coordinates`（定义）
   与 `reconstruct_coordinates`（`reconstruct (coordinates p).1 (coordinates p).2 = p.2`）把被积函数换回
   `p = (θ, x) ↦ ⟪∇f x, θ⟫²`（`lintegral_map`）。这一步和 `lintegral_baseLaw` 的证明手法几乎一样，但那条
   引理是对 `F : Direction E × E → ENNReal`（只依赖 `b`）的，这里被积函数还依赖 `t`/`x`，需要单独写（可以
   仿照 `lintegral_baseLaw` 的证明改写，或者证一条通用的 "jointLaw 的 lintegral = 对 (θ,x) 的双重 lintegral"
   private 引理再各自调用）。
4. 对 `(ρ.prod μ)` 用 Tonelli（`lintegral_prod`／`lintegral_lintegral_swap`）把 `∫_θ∫_x` 换成
   `∫_x∫_θ`，再用 `Admissible.frame_identity`（`finrank ℝ E * ∫_θ ⟪θ,u⟫⟪θ,v⟫ dρ = ⟪u,v⟫`，取
   `u = v = ∇f x`）把 `finrank ℝ E * ∫_θ ⟪∇f x,θ⟫² dρ(θ)` 化成 `‖∇f x‖²`，得到
   `energy μ ρ f ≤ κ * ∫⁻ x, ‖∇f x‖² dμ`。
5. 用 `Energy.LocalSlope.Gradient.energy_eq_lintegral_gradient μ m hac f hf.locallyLipschitz`（已证，
   Energy/LocalSlope/Gradient.lean）把 `∫⁻ x, ‖∇f x‖² dμ` 等同于 `Energy.LocalSlope.energy μ f`，得到目标
   不等式。`≠ ⊤` 由 `hf.finite_energy`（`Energy.LocalSlope.Admissible` 的字段）与 `κ * (有限) ≠ ⊤`
   （`ENNReal.mul_ne_top`）给出（`κ` 是 `NNReal`，`(κ:ENNReal) ≠ ⊤` 总成立）。

第 2 步的"逐纤维 Poincaré 界转成具体测试不等式"是本义务里最不确定的一步；如果发现
`Poincare.LocalSlope.Intrinsic.constant`／`Holds` 目前缺一条恰好形状的辅助引理，请在本文件内新增
private 引理（不改 Poincare/LocalSlope/Basic.lean），并在报告里注明"这条辅助引理其实该搬到共享文件"，
留给注册阶段处理。

## 义务 2：`literatureConstant_le_of_fiberBound`

目标：`Poincare.LocalSlope.Intrinsic.constant μ ≤ κ * C`，由义务 1 与 `hform` 推出。

建议路线（对应 Blueprint "The final multiplication by C is the abstract implication in
lem:finite-energy-factor-poincare"）：

- `Poincare.LocalSlope.Intrinsic.constant μ` 用 `Probability.intrinsicMeasure μ`；先确认在本引理的前提
  （`μ` 已经 `≪ m`、正维数、finrank ℝ E 全维）下，`intrinsicMeasure μ` 与 `μ` 本身在恰当的坐标同构下重合
  （可能已有 `thm:affine-isotropic-reduction`/`thm:ambient-intrinsic-relaxation-equality` 一类的既有等价可以
  复用，也可能这里更省事的做法是不绕道 `intrinsicMeasure`，直接展开 `Poincare.LocalSlope.Holds`/
  `Intrinsic.constant` 的定义证明所需不等式）。
- 核心步骤和 Poincare/L2Comparison.lean 里 `Holds.of_energy_le_mul`/`constant_le_mul_of_energy_le_mul` 的
  证明结构几乎一样（那两条是对 `Energy.Functional (Lp ℝ 2 μ)` 版本证的），但 `Poincare.LocalSlope.Holds`
  是对裸函数 `f : E → ℝ` 直接量化的（不是 `Energy.Functional`/`TestFamily` 包装），所以不能直接调用那两条，
  需要照抄其证明思路重新写一遍（`Holds ν C := ∀ f, Admissible ν f → evariance f ν ≤ C * energy ν f`；用
  `hform`（`Var_μ(f) ≤ C·D_{μ,ρ}(f)` 于 `domain μ ρ`）与义务 1（`D_{μ,ρ}(f) ≤ κ·(gradient energy)(f)`）
  链接：对每个 `Energy.LocalSlope.Admissible μ f` 的（对应 `Lp` 类）`f`，先用义务 1 得到
  `f`（或其 `Lp` 代表元）落在 `domain μ ρ` 里，再用 `hform` 与义务 1 的两条不等式相乘/传递，得到
  `evariance f μ ≤ (κ*C) * Energy.LocalSlope.energy μ f`，即 `Poincare.LocalSlope.Holds μ (κ*C)`，再用
  `Intrinsic.constant` 的 `iInf_le` 得到结论）。
- 注意 `Energy.LocalSlope.Admissible`（裸函数版本）与 `domain μ ρ`/`form μ ρ`（`Lp` 类版本）之间需要
  `MemLp.toLp` 搭桥（`ConditionalFiber.form_toLp` 已证：`form μ ρ (hf₂.toLp f) = energy μ ρ f`），
  以及 `L2.variance μ (hf₂.toLp f)` 与裸函数版本 `evariance f μ` 的关系（可能已有 `L2.variance` 相关引理，
  检索 L2/MeanVariance.lean）。

如果这条路线证下来比直接照抄 `Poincare.L2Comparison` 的证明更繁琐，也可以先证一条"裸函数版
`Holds.of_energy_le_mul`"通用引理（放在本文件的 private 区），再用它得到目标；只要不改
`Poincare.LocalSlope`/`Poincare.L2Energy` 的既有定义即可。

请在完成后的报告里，对每条列出：完成/未完成、用到的关键 API、以及如果某条陈述你怀疑有误
（缺前提、方向反了等），具体反例。
```
