# 2026-09-11 — Prompt for proof session: replace the sorry placeholders in `KLS/ConditionalFiber/EnergyComparison.lean` with proofs

The following prompt can be directly copied to another model/session.

---

```
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS (Lean 4 / Mathlib v4.33.0, Mathlib submission
db584cd6d46c92f209a44c0f1c829460d327499d; Lake root directory formalization/)

Task: Fill in formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean's 2 entry
sorry. This file is the statement skeleton for Blueprint node lem:conditional-fiber-energy-comparison (formalization/blueprint/src/chapters/50-kls-routes.tex, L383–397); design and sentence-by-sentence alignment see research/decisions/2026-09-11-conditional-fiber-energy-comparison-statement.md. First read these two files,
formalization/FunctionalInequalities/KLS/ConditionalFiber.lean,
formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean,
formalization/FunctionalInequalities/Energy/LocalSlope/{Basic,Gradient}.lean,
formalization/FunctionalInequalities/Poincare/LocalSlope/Basic.lean's module documentation.

Rules:
1. Do not modify the type of the two theorem (or FiberBound) in EnergyComparison.lean. If a statement is confirmed to be false or unprovable, do not change its type:
  In the report, document a counterexample/barrier and retain sorry. Allow adding private auxiliary lemmas, allow importing, and allow splitting large proofs into multiple private lemmas within this file.
2. Naming follows research/naming.md.
3. Work only within this file. Do not add to formalization/FunctionalInequalities.lean, lakefile's Solutions root, research/a-series/ledger.yaml, research/check_blueprint.py's CERTIFICATES, research/tasks.json, or Blueprint's \lean{}/\leanok. Do not git commit or git push. Decisions are recorded only by appending (creating new entries to    research/decisions/2026-09-1X-conditional-fiber-energy-comparison-proofs.md).).
4. Compilation command (in formalization/):
     lake env lean FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
  Goal: No errors, no "declaration uses 'sorry'" after completion, no unusedSectionVars or other warnings. After full completion,
     lake env lean -DwarningAsError=true FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
  for each top-level theorem, run #print axioms, allowing only propext / Classical.choice / Quot.sound.
5. If the local lake reports `external command 'git' exited with code 1` (CommandLineTools' x86_64 lake is incompatible with arm64 xcrun): prepend to PATH a wrapper script containing only `exec /Library/Developer/CommandLineTools/usr/bin/git "$@"`, and set GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core, GIT_TEMPLATE_DIR=/Library/Developer/CommandLineTools/usr/share/git-core/templates. Do not modify repository content or system git configuration.

Two obligations, recommended order: first tackle energy_le_of_fiberBound (more difficult, core analytical argument),
literatureConstant_le_of_fiberBound mainly involves linking it to an abstract composition lemma.

## Obligation 1: `energy_le_of_fiberBound`

Objective: `energy μ ρ f ≤ κ * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤`.

Suggested route (corresponding to Blueprint proof segment "A finite upper bound... Dividing the assumed fiber inequality..."):

1. Expand `energy μ ρ f = energyWithKernel μ ρ (kernel μ ρ) f
   = (finrank ℝ E : ENNReal) * ∫⁻ b, energyAt (kernel μ ρ) b f ∂baseLaw μ ρ` (the definitions of `energy` and `energyWithKernel` are
   already partly unfolded; see ConditionalFiber.lean).
2. Fiberwise inequality (a.e. `b`, when `Nondegenerate` holds):
   - `hf.locallyLipschitz` restricted along direction `b.1.1` to the line `t ↦ f (reconstruct b t)` remains (univariate) locally Lipschitz
     (`reconstruct b` is affine, (`LocallyLipschitz.comp`)/direct expansion definition).
   - Use Rademacher along this line: analogy `Energy.LocalSlope.Gradient.apply_ae_eq_norm_gradient` (one-dimensional version, or
     Apply the lemma directly to `f` itself to obtain `apply f x = ofReal ‖gradient f x‖` a.e. then prove the local slope of univariate slice.
     `apply (fun t ↦ f (reconstruct b t)) t = ofReal |⟪gradient f (reconstruct b t), b.1.1⟫|`——chain rule,
     `HasFDerivAt.comp`/`fderiv_comp`, the derivative of `reconstruct b` is in the `t ↦ t • b.1.1` direction). This step is currently not available in the repository.
     Existing lemma, needs to be newly written (can be placed in this file, or if general, placed in Energy/LocalSlope/Gradient.lean, but rule 3 requires no modification
     Shared file, so place the private lemmas of this file first.
   - Apply the Blueprint assumption `hfiber` to this `b`: `Poincare.LocalSlope.Intrinsic.constant ⟨kernel μ ρ b,_⟩ ≤
     κ * evariance id (kernel μ ρ b)`.`Intrinsic.constant` is the infimum of ⨅ C : {C // Holds ...}, C; to do so
     Convert to "inequality for this specific test `t ↦ f(reconstruct b t)`", requires a form like
     "`Poincare.LocalSlope.Intrinsic.constant ν ≤ X → ∀ g, Admissible ν g → evariance g ν ≤ X * energy ν g`"
     The lemma (current Poincare/LocalSlope/Basic.lean has none; `Intrinsic.constant` itself uses `intrinsicMeasure`, for
     `ν : ProbabilityMeasure ℝ` needs to first confirm that `intrinsicMeasure ν` and `ν` coincide, or bypass `Intrinsic.constant`
     Directly expand using the definition of `Poincare.LocalSlope.Holds` — this is the step most requiring careful handling in the present obligation, possibly requiring a new
     private lemma, for example using the infimum property of `iInf`: `Intrinsic.constant ν ≤ X` and monotonicity of `Holds` in `C` (`C ≤ C' →
     Holds ν C → Holds ν C'`) — check Poincare/LocalSlope/Basic.lean whether it already exists; if not, needs to be proven (in conjunction with)
     `ENNReal.le_iInf_iff`/ Take the standard "for any `ε>0` there exists `C < X+ε` such that `Holds C`" and then let `ε→0` (in conjunction with `evariance`
     A specific test regarding `f` does not depend on the constant from `ε` and can be directly used with `ENNReal.le_of_forall_pos_le_add` or
     `le_iInf_iff` and similar, transform the entire inequality into `evariance ... ≤ X * energy ...` upon fixing `f`, without generating `ε` residual terms——
     Note `X = κ * evariance id (kernel μ ρ b)` itself might be `⊤` (unlikely, since `Nondegenerate` provided
     (`MemLp id 2`), in general cases, explicitly handle the degenerate branches of `X = 0` and `X = ⊤`).
   - Divide by `evariance id (kernel μ ρ b) > 0` (the third field of `Nondegenerate` provides `≠ 0`; division on `ENNReal` uses
     `ENNReal.div_le_iff` (a class), obtain `energyAt (kernel μ ρ) b f ≤ κ * ∫⁻ t, ⟪∇f(reconstruct b t), b.1.1⟫² d(kernel μ ρ b)`.
3. Plug the fiberwise bound from step 2 into the `∫⁻ b ... ∂baseLaw` in step 1, obtaining
   `energy μ ρ f ≤ κ * finrank ℝ E * ∫⁻ b, ∫⁻ t, ⟪∇f(reconstruct b t), b.1.1⟫² d(kernel μ ρ b) ∂baseLaw μ ρ`.
   Use `compProd_baseLaw_kernel` (`baseLaw μ ρ ⊗ₘ kernel μ ρ = jointLaw μ ρ`) to write the double integral as a integral over `jointLaw`
   A single lintegral (`Measure.lintegral_compProd`), then using `jointLaw μ ρ = (ρ.prod μ).map coordinates` (definition)
   Switch the integrand back to `reconstruct_coordinates` (`reconstruct (coordinates p).1 (coordinates p).2 = p.2`)
   `p = (θ, x) ↦ ⟪∇f x, θ⟫²` (`lintegral_map`). This step is almost identical in proof technique to `lintegral_baseLaw`, but that line
   The lemma depends on `F : Direction E × E → ENNReal` (which only relies on `b`), here the integrand also depends on `t`/`x`, requiring a separate treatment (can
   Following the proof of `lintegral_baseLaw`, or prove a general statement: "jointLaw's lintegral = double lintegral over (θ, x)"
   (private lemma called individually).
4. Apply Tonelli to `(ρ.prod μ)` (`lintegral_prod`/`lintegral_lintegral_swap`) to change `∫_θ∫_x` to
   `∫_x∫_θ`, then use `Admissible.frame_identity` (`finrank ℝ E * ∫_θ ⟪θ,u⟫⟪θ,v⟫ dρ = ⟪u,v⟫`, take
   (`u = v = ∇f x`) transforms `finrank ℝ E * ∫_θ ⟪∇f x,θ⟫² dρ(θ)` into `‖∇f x‖²`, obtaining
   `energy μ ρ f ≤ κ * ∫⁻ x, ‖∇f x‖² dμ`.
5. Using `Energy.LocalSlope.Gradient.energy_eq_lintegral_gradient μ m hac f hf.locallyLipschitz` (already proven,
   (Energy/LocalSlope/Gradient.lean) identifies `∫⁻ x, ‖∇f x‖² dμ` with `Energy.LocalSlope.energy μ f`, obtaining the target
   inequality. `≠ ⊤` follows from `hf.finite_energy` (a field of `Energy.LocalSlope.Admissible`) and `κ * (finite) ≠ ⊤`
    (`ENNReal.mul_ne_top`) given  (`κ` is `NNReal`, `(κ:ENNReal) ≠ ⊤` always holds).

The transformation of the "fiber-wise Poincaré inequality into concrete test inequality" in step 2 is the most uncertain step in this obligation; if it is found that
`Poincare.LocalSlope.Intrinsic.constant`/`Holds` currently lacks a helper lemma of the exact form required, please add a private lemma (without modifying Poincare/LocalSlope/Basic.lean) within this document, and note in the report that "this helper lemma should actually be moved to a shared file," to be handled during the registration phase.

## Obligation 2: `literatureConstant_le_of_fiberBound`

Goal: `Poincare.LocalSlope.Intrinsic.constant μ ≤ κ * C`, deduced from obligations 1 and `hform`.

Suggested route (corresponding to Blueprint "The final multiplication by C is the abstract implication in lem:finite-energy-factor-poincare"): ")

- `Poincare.LocalSlope.Intrinsic.constant μ` use `Probability.intrinsicMeasure μ`; first verify under the premise of this lemma
  ( `μ` already `≪ m`, positive dimension, finrank ℝ E full dimension ) under the appropriate coordinate isomorphism, `intrinsicMeasure μ` and `μ` coincide
  (There might already be `thm:affine-isotropic-reduction`/`thm:ambient-intrinsic-relaxation-equality` class of equivalent statements)
  Reuse, or perhaps a more straightforward approach here would be not to detour `intrinsicMeasure`, directly expand `Poincare.LocalSlope.Holds`/
  (Proof of the inequality required by the definition of `Intrinsic.constant`).
- Core steps and Poincare/L2Comparison.lean with `Holds.of_energy_le_mul`/`constant_le_mul_of_energy_le_mul`
  The proof structure is almost the same (those two are for the `Energy.Functional (Lp ℝ 2 μ)` version), but `Poincare.LocalSlope.Holds`
  It is a direct quantification of the bare function `f : E → ℝ`, not `Energy.Functional`/`TestFamily` wrapping, so it cannot directly invoke those two,
  Need to copy its proof idea and rewrite it (`Holds ν C := ∀ f, Admissible ν f → evariance f ν ≤ C * energy ν f`; use
  `hform` (`Var_μ(f) ≤ C·D_{μ,ρ}(f)` at `domain μ ρ`) and duty 1 (`D_{μ,ρ}(f) ≤ κ·(gradient energy)(f)`)
  Link: For each `Energy.LocalSlope.Admissible μ f` (corresponding to `Lp` class) `f`, first obtain using obligation 1
  `f` (or its `Lp` representative) lies in `domain μ ρ`, and then multiplying/propagating the two inequalities from `hform` and obligation 1, we obtain
  `evariance f μ ≤ (κ*C) * Energy.LocalSlope.energy μ f`, i.e. `Poincare.LocalSlope.Holds μ (κ*C)`, then use
  (`Intrinsic.constant`)'s (`iInf_le`) yields the conclusion).
- Note `Energy.LocalSlope.Admissible` (naked function version) and `domain μ ρ`/[`form μ ρ`] (`Lp` class version) between
  `MemLp.toLp` Bridging (`ConditionalFiber.form_toLp` proven: `form μ ρ (hf₂.toLp f) = energy μ ρ f`),
  And the relationship between `L2.variance μ (hf₂.toLp f)` and the bare function version `evariance f μ` (possibly with a related lemma `L2.variance`,
  (Search L2/MeanVariance.lean).

If the route proved turns out more cumbersome than directly copying the proof of `Poincare.L2Comparison`, we may first prove a general lemma in the "bare function version" `Holds.of_energy_le_mul` (placed in the private section of this file), then use it to obtain the target; as long as we do not alter the existing definitions of `Poincare.LocalSlope`/`Poincare.L2Energy`.

In the final report, for each statement listed: completed/not completed, key APIs used, and if you suspect a statement is incorrect (lacking premises, wrong direction, etc.), provide a specific counterexample. ```
```
