# 2026-09-11 — 交给证明会话的提示词：填 `KLS/LogConcave/ConditionalFiber.lean` 的唯一 sorry

以下提示词可直接复制给另一个模型/会话。前置说明：陈述骨架与基础设施核对见
[`2026-09-11-conditional-fiber-twelve-bound-statement.md`](2026-09-11-conditional-fiber-twelve-bound-statement.md)；
上游比较引理已注册为证书（[注册记录](2026-09-11-conditional-fiber-energy-comparison-registration.md)）。

---

```
仓库：/Users/lyuyuwei/Documents/ChatGPT/KLS（Lean 4 / Mathlib v4.33.0，Mathlib 提交
db584cd6d46c92f209a44c0f1c829460d327499d；Lake 根目录 formalization/）。

任务：填写 formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean 中唯一的一条 sorry：

  theorem ae_conditionalFiber_logConcave (hμ : LogConcave μ) (hρ : Admissible μ ρ)
      (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
      ∀ᵐ b ∂baseLaw μ ρ, LogConcave (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ)

这是 Blueprint 节点 cor:conditional-fiber-twelve-bound（formalization/blueprint/src/chapters/50-kls-routes.tex，
"Log-concave conditional fibers" 推论块）证明段的解析内容："Fubini disintegration of the log-concave density gives
conditional densities proportional to t ↦ ρ_μ(z+tθ) wherever the normalizing slice integral is finite and positive.
These densities are log-concave. The remaining fibers are null."  该文件其余五条定理已由这条引理与两个已认证输入
（lem:conditional-fiber-energy-comparison、thm:one-dimensional-logconcave-poincare）合成，不要改它们。

先读：
- research/decisions/2026-09-11-conditional-fiber-twelve-bound-statement.md（陈述设计、逐句对齐、三条基础设施缺口）
- formalization/FunctionalInequalities/KLS/ConditionalFiber.lean（jointLaw、baseLaw、kernel := (jointLaw μ ρ).condKernel、
  coordinates、reconstruct、baseMap、compProd_baseLaw_kernel、energyWithKernel_eq_energy——后者演示了
  "自造 Markov 核 κ 满足 baseLaw ⊗ₘ κ = jointLaw ⇒ κ = kernel a.e." 的用法：
  ProbabilityTheory.eq_condKernel_of_measure_eq_compProd κ hκ.symm）
- formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean（私有引理
  affineSupport_eq_top_of_absolutelyContinuous、ae_ae_reconstruct、ae_memLp_comp_reconstruct 的写法可照抄）
- formalization/FunctionalInequalities/KLS/Definitions.lean（LogConcave：紧集版本）、
  KLS/LogConcave/Borel.lean（BorelLogConcave、innerMeasure、LogConcave.borel_iff）
- formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean（IsBorellDensity 的五个字段：
  measurable、nonneg、upperSemicontinuous、logConcave、withDensity_eq；
  LogConcave.exists_isBorellDensity_of_interior_support_nonempty hlc m hint hac；
  convex_pos、concaveOn_log、pos_of_mem_interior_support）
- formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean 的
  interior_support_nonempty_of_affineSupport_eq_top（由 hac 得仿射支撑为 ⊤，再得支撑内部非空）
- formalization/FunctionalInequalities/KLS/LogConcave/Line/Density.lean（LineDensity、exists_lineDensity：
  注意仓库目前只有"对数凹律 ⇒ 有对数凹密度"，没有反方向）

规则：
1. 不改 ae_conditionalFiber_logConcave 及同文件其余五条定理的类型。若确认不可证，不改类型，在报告里写明障碍并保留 sorry。
2. 需要的新基础设施允许新建文件（建议路径见下），允许在新文件里写公开引理；不改既有共享文件的既有声明
   （如确需把 EnergyComparison.lean 的 private 引理改为公开，只允许去掉 private 与补 docstring，不改类型）。
   命名遵守 research/naming.md（短名不重复命名空间；对数凹推论放 KLS.LogConcave 用 hμ. 点记法）。
3. 不注册：不加进 formalization/FunctionalInequalities.lean、lakefile 的 Solutions 根、research/a-series/ledger.yaml、
   research/check_blueprint.py 的 CERTIFICATES、research/tasks.json、Blueprint 的 \lean{}/\leanok。
   不 git commit、不 git push。决定记录只追加（新建
   research/decisions/2026-09-1X-conditional-fiber-twelve-bound-proofs.md）。
4. 编译（在 formalization/ 下）：新文件用 lake build FunctionalInequalities.<模块名> 产生 olean 后，
     lake env lean FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean
   目标：无错误、无 "declaration uses 'sorry'"、无 unusedSectionVars 等警告；全部完成后对每个新文件与本文件
     lake env lean -DwarningAsError=true <文件>
   并对 ae_conditionalFiber_logConcave 与 conditionalFiber_literatureConstant_le_four_mul #print axioms，
   只允许 propext / Classical.choice / Quot.sound。
5. 若本机 lake 报 `external command 'git' exited with code 1`：在 PATH 前插入一个只
   `exec /Library/Developer/CommandLineTools/usr/bin/git "$@"` 的包装脚本所在目录，并设置
   GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core、
   GIT_TEMPLATE_DIR=/Library/Developer/CommandLineTools/usr/share/git-core/templates。不改仓库内容或系统 git 配置。

建议路线（三个子义务，可分三个新文件；A 与 B 互不依赖，C 用 A、B）：

## 子义务 A：一维"对数凹密度 ⇒ 紧集对数凹律"
建议文件 formalization/FunctionalInequalities/Probability/Line/BrunnMinkowski.lean（一般工具）与
formalization/FunctionalInequalities/KLS/LogConcave/Line/OfDensity.lean（对数凹结论）。钉住的 Mathlib 没有
Brunn–Minkowski 或 Prékopa–Leindler（grep 到的 "Minkowski" 都是 gauge 泛函）。

A1. 一维 Brunn–Minkowski（紧集）：K L : Set ℝ 非空紧 ⇒ volume (K + L) ≥ volume K + volume L
    （Set.add 即 Minkowski 和，或写成 {z | ∃ x ∈ K, ∃ y ∈ L, z = x + y}）。
    证明：a := sSup K、b := sInf L（IsCompact.sSup_mem / sInf_mem）；(K + {b}) ∪ ({a} + L) ⊆ K + L，
    两块的交只含 a + b（K + b ≤ a + b ≤ a + L），故 volume (K+L) ≥ volume (K+{b}) + volume ({a}+L) − volume {a+b}
    = volume K + volume L（measure_union_add_inter、Real.volume_singleton、平移不变
    measure_preimage_add / Measure.IsAddRightInvariant）。
A2. 一维 Prékopa–Leindler（lintegral 版本）：f g h : ℝ → ENNReal 可测，t ∈ (0,1)，
    ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y) ⇒ (∫⁻ f) ^ t * (∫⁻ g) ^ (1 - t) ≤ ∫⁻ h。
    证明：先处理 ∫⁻ f 或 ∫⁻ g 为 0 或 ⊤ 的退化分支；再归一化到 ∫⁻ f = ∫⁻ g = 1（齐次性：
    f/‖f‖、g/‖g‖、h/(‖f‖^t‖g‖^{1−t}) 仍满足假设）。层饼公式 lintegral_eq_lintegral_meas_lt
    （Mathlib/MeasureTheory/Integral/Layercake.lean）把三个积分写成 ∫⁻ s in Ioi 0, volume {x | s < ·}；
    对每个 s>0 有 {h > s} ⊇ t • {f > s} + (1 − t) • {g > s}（若 f x > s、g y > s 则
    h(tx+(1−t)y) ≥ s^t s^{1−t} = s；注意用严格不等式版本时需 s < f x ⇒ … 略作调整），
    用 A1 在内正则逼近的紧子集上（Real.volume 是 InnerRegular：MeasurableSet.measure_eq_iSup_isCompact
    或 Measure.InnerRegular）得 volume {h>s} ≥ t·volume{f>s} + (1−t)·volume{g>s}（缩放：Real.volume_smul /
    Measure.addHaar_smul），积分后 ∫⁻ h ≥ t·1 + (1−t)·1 = 1 = 1^t·1^{1−t}。
A3. 结论：ν : ProbabilityMeasure ℝ，p : ℝ → ℝ 满足 IsBorellDensity ν volume p ⇒ LogConcave ν。
    证明：对紧集 K₀ K₁ 与 t，取 f := 1_{K₀}·ofReal∘p、g := 1_{K₁}·ofReal∘p、
    h := 1_{tK₀+(1−t)K₁}·ofReal∘p；IsBorellDensity.logConcave 给逐点假设（x ∈ K₀, y ∈ K₁ ⇒
    tx+(1−t)y ∈ 组合集），A2 给 ∫⁻ h ≥ (∫⁻ f)^t (∫⁻ g)^{1−t}，再用 withDensity_eq 把三个积分换成
    ν 的测度（withDensity_apply、lintegral_indicator）。组合集 {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t•x+(1−t)•y}
    紧（KLS.LogConcave.isCompact_combination 在 Borel.lean）故可测。

## 子义务 B：沿直线的显式分解核
建议文件 formalization/FunctionalInequalities/KLS/ConditionalFiber/SliceKernel.lean（命名空间 KLS.ConditionalFiber）。
对给定的密度 p : E → ℝ（可测、非负）定义：
  sliceMass p b := ∫⁻ t, ENNReal.ofReal (p (reconstruct b t))            -- Z(θ,z)
  sliceKernel p : Kernel (Direction E × E) ℝ :=
    在 {b | 0 < sliceMass p b ∧ sliceMass p b < ⊤} 上为
      (volume.withDensity fun t ↦ ENNReal.ofReal (p (reconstruct b t))) 除以 sliceMass p b
      （Kernel.withDensity (Kernel.const _ volume) (fun b t ↦ ofReal (p (reconstruct b t)) / sliceMass p b)，
       被积函数关于 (b,t) 可测：measurable_reconstruct、Measurable.lintegral_kernel_prod_right'），
    否则为 Kernel.const _ (Measure.dirac 0)（Kernel.piecewise，集合可测）。
  证明 IsMarkovKernel（好集上质量为 Z/Z = 1：lintegral_div_const / ENNReal.div_self）。
B1. 关键恒等式：IsBorellDensity μ m p（或只需 m.withDensity (ofReal ∘ p) = μ）⇒
    baseLaw μ ρ ⊗ₘ sliceKernel p = jointLaw μ ρ。
    证法：Measure.ext_of_lintegral 或对可测集 s 比较。右边 = ∫⁻ θ ∫⁻ x 1_s(coordinates (θ,x)) ofReal(p x) dm dρ
    （jointLaw 定义、lintegral_map、withDensity、lintegral_prod）。对固定 θ 需要沿直线的 Fubini：
    m 是 Haar，(z,t) ↦ z + t•θ 是 (θ⊥ × ℝ) ≃L[ℝ] E 的连续线性等价 T_θ
    （Submodule.prodEquivOfIsCompl (ℝ∙θ)ᗮ (ℝ∙θ) + 一维子空间与 ℝ 的等价，或直接手写
     LinearEquiv 再 LinearEquiv.toContinuousLinearEquiv），故 map T_θ (m_θ.prod volume) 也是 Haar
    （ContinuousLinearEquiv.isAddHaarMeasure_map），与 m 相差常数 c_θ（Measure.isAddLeftInvariant_eq_smul /
    addHaarMeasure_unique）。于是 ∫⁻ x, G x dm = c_θ ∫⁻ z ∫⁻ t, G (z + t•θ) dt dm_θ。
    取 G x := 1_s((θ, x − ⟪x,θ⟫θ), ⟪x,θ⟫) ofReal(p x)；对 z ∈ θ⊥ 有 coordinates (θ, z + tθ) = ((θ,z),t)
    （z ⊥ θ、‖θ‖ = 1），得右边 = ∫⁻ θ c_θ ∫⁻ z ∫⁻ t 1_s((θ,z),t) ofReal(p(z+tθ)) dt dm_θ dρ。
    左边 = ∫⁻ b, sliceKernel p b (Prod.mk b ⁻¹' s) dbaseLaw（Measure.compProd_apply）；baseLaw = map baseMap (ρ.prod μ)
    （baseLaw_eq_map），同样的 Fubini 给 baseLaw 的 θ 截面在 θ⊥ 上有密度 c_θ·Z(θ,z)（对 m_θ），于是
    左边 = ∫⁻ θ c_θ ∫⁻ z Z(θ,z) · [Z(θ,z)⁻¹ ∫⁻ t 1_s ofReal(p(z+tθ)) dt] dm_θ dρ，在好集上与右边逐点相等；
    坏集 {Z = 0} ∪ {Z = ⊤}：Z = 0 处两边被积函数都是 0；Z = ⊤ 的 z 是 m_θ-零测集
    （∫⁻ Z dm_θ · c_θ = 1 有限，ae_lt_top）。c_θ 在两边完全相同，无需算出。
    如果觉得随 θ 变化的 T_θ 与 m_θ 太重，可替代路线：只对每个固定 θ 做上述计算（θ 固定后
    m_θ := 任一 Haar on (ℝ∙θ)ᗮ，如 Measure.addHaar），外层用 lintegral_prod 先固定 θ；
    lintegral_baseLaw 已经给出 baseLaw 积分 = ∫⁻ θ ∫⁻ z F(θ,z) d(map (x ↦ x − ⟪x,θ⟫θ) μ) dρ，
    因此只需对每个 θ 证明"投影律 map (x ↦ x − ⟪x,θ⟫θ) μ 对 m_θ 有密度 c_θ Z(θ,·)"与
    "∫⁻ x G x dm = c_θ ∫⁻ z ∫⁻ t G(z+tθ) dt dm_θ"两条，不必把 c_θ、m_θ 做成关于 θ 可测的对象。
B2. 由 B1 与 ProbabilityTheory.eq_condKernel_of_measure_eq_compProd (sliceKernel p) hκ.symm 得
    ∀ᵐ b ∂baseLaw μ ρ, sliceKernel p b = kernel μ ρ b（照抄 energyWithKernel_eq_energy 的用法，
    (jointLaw μ ρ).fst 定义上就是 baseLaw μ ρ）。
B3. 好集几乎处处：∀ᵐ b ∂baseLaw, 0 < sliceMass p b ∧ sliceMass p b < ⊤（Z = ⊤ 零测同 B1；
    Z = 0 的基点集合在 baseLaw 下质量 = ∫⁻ 1_{Z=0} · Z = 0）。

## 子义务 C：装配 ae_conditionalFiber_logConcave
1. hac + hμ ⇒ 仿射支撑为 ⊤（EnergyComparison.lean 的私有引理 affineSupport_eq_top_of_absolutelyContinuous，
   照抄或去掉 private）⇒ 支撑内部非空（interior_support_nonempty_of_affineSupport_eq_top）⇒
   取 p 满足 IsBorellDensity μ m p（exists_isBorellDensity_of_interior_support_nonempty）。
2. 对好集上的 b，sliceKernel p b 是 ℝ 上的概率律，密度 t ↦ ofReal(p(z+tθ)) / Z 对 volume；
   它是 Borell 密度：可测、非负、上半连续（p 上半连续 ∘ 连续仿射）、对数凹（IsBorellDensity.logConcave 沿仿射直线
   t•(z+xθ)+(1−t)•(z+yθ) = z + (tx+(1−t)y)θ，再除以常数 Z 保持）、withDensity_eq 按定义。
   用子义务 A3 得 LogConcave (sliceKernel p b)。
3. filter_upwards [B2, B3] 把结论搬到 kernel μ ρ b（Subtype 相等用 ProbabilityMeasure 的 ext / 直接 rw 测度相等）。

坑与提示：
- LogConcave 定义的组合集写法是 {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}，在 ℝ 上 t • x = t * x（smul_eq_mul）。
- ENNReal 中 zero_le 参数隐式（写 exact zero_le）；mul_le_mul_left'/right' 已不存在，用 mul_le_mul_left / mul_le_mul_right
  （注意这两个在 Mathlib 当前版本里的左右约定：mul_le_mul_right (h : b ≤ c) a : a * b ≤ a * c）。
- ⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ 的 toMeasure 就是 kernel μ ρ b（Subtype.val 归约），
  a.e. 相等的核可用 congrArg/Subtype.ext 换掉。
- Nondegenerate 的判定不需要在这里证明：FiberBound 只对非退化纤维约束，且 conditionalFiber_fiberBound_four
  已经写好。本引理只需 a.e. 对数凹。
- 若子义务 A 的 Prékopa–Leindler 太长，可先把 A2 写成关于 ENNReal 值可测函数的独立引理并用 sorry 占位，
  先跑通 B、C 的装配，再回头填 A2；报告里写明每条子义务的完成状态。

完成后的报告请列出：每条子义务完成/未完成、新文件与其公开声明、用到的关键 Mathlib API、
若某条陈述你怀疑有误（缺前提、方向反了等）给出具体反例，以及"这些新引理应放到哪个共享文件"。
```
