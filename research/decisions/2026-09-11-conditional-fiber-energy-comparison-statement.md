# 2026-09-11 — `lem:conditional-fiber-energy-comparison`: Statement skeleton (only statements, no proofs)

## Decision

- Write a Lean statement skeleton for Blueprint `formalization/blueprint/src/chapters/50-kls-routes.tex` (`lem:conditional-fiber-energy-comparison`, L383–397), two `theorem`s, with proof bodies both being `sorry`, placed in a new file `formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean`.
- Do not modify the types of any existing definitions/theorems (`Admissible`, `Nondegenerate`, `baseLaw`, `kernel`, `energy`, `form`, `domain`, `Poincare.LocalSlope.Intrinsic.constant`, `Energy.LocalSlope.Admissible`/`.energy`, `L2.variance` all directly reused).
- Add a local predicate `FiberBound` (packaging the fiberwise assumptions of Blueprint), not an explicitly named object of Blueprint, but merely a direct transcription of the inequalities displayed.
- Do not register (do not add `formalization/FunctionalInequalities.lean` aggregate import, `lakefile.toml`'s `Solutions` root, `research/a-series/ledger.yaml`, `research/check_blueprint.py`'s `CERTIFICATES`, `research/tasks.json`); do not modify Blueprint's `\lean{}`/`\leanok` (consistent with the handling of another session's `RelativePerimeter.lean`/`Cheeger.lean`: anchor points and proofs are added only after they are landed). Do not `git commit`, do not `git push`, do not modify any shared files.

## Lean Statement

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

## Sentence-by-sentence alignment (Blueprint ↔ Lean)

| Blueprint | Lean | Description |
|---|---|---|
| "Let $d\ge1$" | `Admissible.positive_dimension` (`0 < Module.finrank ℝ E`) | use general finite-dimensional `E` rather than fixed `ℝ^d`, consistently; `d` is `finrank ℝ E` |
| "$\mu\ll\mathrm{Leb}_{\mathbb R^d}$" | `(m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ:Measure E) ≪ m)` | Replace the general Haar reference measure instead of a fixed Lebesgue measure (the two differ by a constant factor on Euclidean space), consistent with the existing convention in `Energy.LocalSlope.Gradient` |
| "have finite second moment" | `Admissible.memLp_two` | already included in existing fields, no repetition required |
| "$\rho$ be an admissible frame" | `hρ : Admissible μ ρ` | consistent |
| "one finite $\kappa\ge0$ satisfies $C_P^{lit}(\mu_{\theta,z})\le\kappa\Var_{\mu_{\theta,z}}(T)$ for a.e. nondegenerate fiber" | `FiberBound μ ρ κ` | `κ b` is the fiber law `μ_{θ,z}` (Markov kernels provide probability measure instances); `Poincare.LocalSlope.Intrinsic.constant` is equipped with `C_P^{lit}`; `evariance id (kernel μ ρ b)` is `Var_{μ_{θ,z}}(T)` (the denominator is the same object `energyAt`) |
| "Every locally Lipschitz $f\in L^2(\mu)$ with finite gradient energy" | `Energy.LocalSlope.Admissible μ f` | Has a structure, precisely the package of three fields: "local Lipschitz + $L^2$ + finite gradient energy" |
| "$\mathcal D_{\mu,\rho}(f)\le\kappa\int\norm{\nabla f}^2\dd\mu<\infty$" | `energy_le_of_fiberBound`'s conclusion (the conjunction of two parts) | `energy μ ρ f` is `KLS.ConditionalFiber.energy` (the existing bare function version of $\mathcal D_{\mu,\rho}$); `Energy.LocalSlope.energy μ f` under `hac` equals $\int\norm{\nabla f}^2\dd\mu$ via `Energy.LocalSlope.Gradient.energy_eq_lintegral_gradient`, hence RHS is consistent; "$<\infty$" is just the conjunction term of `≠⊤` |
| "Hence $\Var_\mu(f)\le C\mathcal D_{\mu,\rho}(f)$ on the maximal finite form domain, for finite $C\ge0$, implies $C_P^{lit}(\mu)\le\kappa C$" | `literatureConstant_le_of_fiberBound` | `domain μ ρ` (existing, "maximal finite form domain"), `form μ ρ` (existing $L^2$-class version of $\mathcal D_{\mu,\rho}$), and `L2.variance μ` (existing $\Var_\mu$, explicitly coerced from `NNReal` to `ENNReal`); in the conclusion, `Poincare.LocalSlope.Intrinsic.constant μ` is $C_P^{lit}(\mu)$ for `μ` itself, before applying the intrinsic reduction |

Not expressed at the statement level: the tool listed by `\uses`, `lem:finite-energy-factor-poincare` (`Poincare.L2Energy.Holds.of_energy_le_mul`/
`constant_le_mul_of_energy_le_mul`). This abstract tool is intended for the proof; its concrete type does not occur in the statements.
The specific value in `cor:conditional-fiber-twelve-bound` (or the proved `κ=12`, `4`) is not addressed here.
The degenerate `d=0` case is not handled: `Admissible` already excludes `finrank=0`, consistent with Blueprint's separate treatment of dimension zero.

## Compilation

```
lake env lean FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
```

Exactly 2 `declaration uses 'sorry'` warnings (`energy_le_of_fiberBound`, `literatureConstant_le_of_fiberBound`),
no other warnings; `lake env lean -DwarningAsError=true ...` likewise provides exactly these 2 (promoted to error), no other diagnostics.
(The x86_64 lake / arm64 xcrun incompatibility issue for the CommandLineTools on this machine continues to use the same workaround as in other sessions of the same day: by prepending a directory containing only a `exec` `/Library/Developer/CommandLineTools/usr/bin/git` wrapper script to PATH, and setting `GIT_EXEC_PATH`/`GIT_TEMPLATE_DIR`, without modifying the repository content.)

## Not done / Future work

- Proof placeholders remain; no registration, commit, or push; no changes to Blueprint, `FunctionalInequalities.lean`, `lakefile.toml`,
  `solutions/README.md`, `research/tasks.json`, `research/a-series/ledger.yaml` or other shared files.
- Prompt for the proof session is seen on the same day
  [`2026-09-11-conditional-fiber-energy-comparison-sorry-prompt.md`](2026-09-11-conditional-fiber-energy-comparison-sorry-prompt.md).
- If proven: `cor:conditional-fiber-twelve-bound` can be used `κ=4` (already proven `thm:one-dimensional-logconcave-poincare`
  (Sharp constant) instantiate `literatureConstant_le_of_fiberBound`, upgrade Blueprint's existing "`12C`" analysis inference to a Lean proof.
