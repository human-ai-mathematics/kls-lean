# Semigroup Generation Path: `S7` (Semigroup Law and Strong Continuity) and `S8` (Generator) Path

2026-09-19, follows [`S6` round](2026-09-19-yosida-limit-route.md). This round **only writes definitions and statements, no proofs**; proofs are delegated to parallel Opus sessions, dependency relations determine three batches. No commit, no push.

## Definition module (this round has been written and compiled)

`formalization/FunctionalInequalities/Analysis/Semigroup/Generated.lean`: Name the limiting quantified operator in `S6` as an operator.

| Statement | Content |
| --- | --- |
| `semigroupApply T hT hd t f` | `t ≥ 0` when `exists_limit_exp_neg_smul_yosida` is taken from `Classical.choose`, `t < 0` when `f` is taken |
| `semigroupApply_spec` | `t ≥ 0` ⟹ `exp(-t • L_s) f → semigroupApply t f` (ε–δ) |
| `semigroupApply_of_not_nonneg` | the agreed value of `t < 0` |

Formally `P_t f = exp(-t T†T) f`. The linearity and contraction of `P_t` along the path are pending proofs (`P2`, `P3`), so here we only define the function, the `ContinuousLinearMap` version is left for the proof module to package.

## Statement file

`research/audits/GeneratedSemigroupRouteStatements.lean`, contains only `#check`, all 11 pass type checking:

| Number | Content | Input | Risk |
| --- | --- | --- | --- |
| `P1` | Uniqueness of limit: the ε–δ convergence satisfies `g` equals `P_t f` | `semigroupApply_spec` | low |
| `P2` | `P_t` linear | `P1` | low |
| `P3` | `‖P_t f‖ ≤ ‖f‖` | `S5` + limit | low |
| `P4` | `⟪P_t f, g⟫ = ⟪f, P_t g⟫` | `yosida_symm` → `IsSelfAdjoint (L_s)` → `IsSelfAdjoint.exp` → `adjoint_inner_left`, take limit | Medium to low: Mathlib's star = adjoint structure |
| `P5` | `P_0 = 1` | `exp_zero` + `P1` | low |
| `P6` | `P_{t+u} = P_t P_u` | `exp_add_of_commute` + `S5` + `P1` | Medium |
| `P7` | `‖P_t f − f‖ → 0` (`t ↓ 0`) | `Y6` (`B = 0`)+ `Y5` + dense + `P3` | Medium |
| `P8` | `ContinuousOn (t ↦ P_t f) (Ici 0)` | `P6` + `P3` + `P7` | medium-low |
| `G1` | `S6` convergence is uniform over `τ ∈ [0, t]` | The `Y6` bound is uniform for `τ ≤ t`, plus density and contraction | Medium |
| `G2` | `‖e^{-tA} f − f + t·Af‖ ≤ C·t`, if `‖e^{-τA}(Af) − Af‖ ≤ C` on `[0,t]` | `hasDerivAt_exp_smul_const'` + mean value inequality; no need for `A` non-negative | medium-low |
| `G3` | `S8`: `f ∈ D(T†T)` ⟹ `‖(P_t f − f)/t + T†T f‖ → 0` | `P7` + `G1` + `G2` + `Y5` + `S5` | **High-Medium**: The core assembly of this route |

The proof of `G3` deliberately avoids Bochner integral: it does not write `P_t f − f = −∫₀ᵗ P_τ T†T f dτ`, but instead applies the mean value inequality (`G2`) to `φ(τ) = e^{-τL_s} f − f + τ L_s f`,
The derivative bound relies on `Y5` (`L_s f ≈ T†T f`), `G1` (`e^{-τL_s} g ≈ P_τ g` uniformly with respect to `τ ≤ t`), and `P7` (`P_τ g ≈ g`), then take `s ↓ 0`.

## Division (three batches)

1. Session A: `P1`–`P8`, new module `Analysis/Semigroup/SemigroupLaws.lean`, audit `research/audits/SemigroupLawsAudit.lean`.
2. Session B (in parallel with A): `G2`, bounded operator, new module `Analysis/Semigroup/ExpMeanValue.lean`, audit `research/audits/ExpMeanValueAudit.lean`.
3. Session C (after A, B): `G1`, `G3`, new module `Analysis/Semigroup/Generator.lean`, audit `research/audits/GeneratorAudit.lean`,
   import modules from A, B.

Rules as before: create only new files, use only `lake env lean -DwarningAsError=true`, do not `lake build`, do not `verify.py`, do not git, do not modify existing files, zero `sorry`.

## Work excluded from this round

Once `S7`–`S8` are proved, the semigroup generation route (gap one) will be complete, but the Buser half will still require Markov property (gap two), Bakry–Émery Γ calculus (gap three), and small-time heat estimate (gap four). `thm:logconcave-cheeger-poincare-comparison` No progress marked, `tasks.json` unchanged (registered uniformly during integration).

## Append: `P1`–`P8`, `G1`–`G3` all proven, `S7`, `S8` closed; semigroup generation path `S1`–`S8` completed (same day, three batches of Opus sessions approximately 13, 4, 8 minutes)

| Number | Statement | Module |
| --- | --- | --- |
| `P1` | `eq_semigroupApply_of_tendsto` | `SemigroupLaws.lean` |
| `P2` | `semigroupApply_smul_add` (with additional implications `semigroupApply_sub`, and `semigroupCLM` bundled) | `SemigroupLaws.lean` |
| `P3` | `norm_semigroupApply_le` | `SemigroupLaws.lean` |
| `P4` | `inner_semigroupApply_left` | `SemigroupLaws.lean` |
| `P5` | `semigroupApply_zero` | `SemigroupLaws.lean` |
| `P6` | `semigroupApply_add` | `SemigroupLaws.lean` |
| `P7` | `exists_delta_norm_semigroupApply_sub_self_lt` (quantitative version `norm_semigroupApply_sub_self_le`: `‖P_t f − f‖ ≤ t(‖T†T f‖ + 1)`) | `SemigroupLaws.lean` |
| `P8` | `continuousOn_semigroupApply` | `SemigroupLaws.lean` |
| `G1` | `exists_delta_norm_exp_neg_smul_yosida_sub_semigroupApply_lt` | `Generator.lean` |
| `G2` | `norm_exp_neg_smul_sub_add_smul_le` (general complete real normed space; `InnerProductSpace` unused, word-for-word packaging `route_G2`) | `ExpMeanValue.lean` |
| `G3` = `S8` | `exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt` (quantitative version `norm_semigroupApply_sub_self_add_smul_le`) | `Generator.lean` |

Audit: `SemigroupLawsAudit.lean` 29 , `ExpMeanValueAudit.lean` 5 , `GeneratorAudit.lean` 8 `#print axioms`,
**42 statements contain only `propext, Classical.choice, Quot.sound`, 0 `sorryAx`**; 11 route statements are token-by-token identical to the route file (recompiled independently and mechanically compared in this session).
Four new modules (`Generated`, `SemigroupLaws`, `ExpMeanValue`, `Generator`) have been integrated into the aggregate root, `lake build` 3532 jobs have passed,
Fourteen semigroup audit / route files undergo strict recompilation and exit 0. Except for `InnerProductSpace` of `G2`, no route assumptions can be removed.

### Differences from draft

* **`G3` Draft's ε splitting does not yield a strict inequality**: After dividing the ε/3 trisection by `t`, only `≤ ε` is obtained, while the statement requires `< ε`. Actually using `ε/8 + ε/4 + ε/4 + ε/8 = 3ε/4`,
  endpoint `7ε/8 < ε`. Route file unchanged.
* `G1` First prove `≤ ε` form on `D(T†T)` (taking limit over auxiliary parameter `r` yields only non-strict), generally `g` then restore strictness via three strict ε/3.
* `G2` Using unprimed `hasDerivAt_exp_smul_const` completely eliminates the need for the exchange lemma, passing compilation once.

### Semigroup generation route (gap one) completed

`S1`–`S8` are all local hole-free Lean proofs, `Analysis/Semigroup/` below 14 modules. For closed and densely defined `T : H₀ →ₗ.[ℝ] H₁`,
`semigroupApply T hT hd` (`semigroupCLM`) is a strongly continuous self-adjoint contraction semigroup on `H₀`, `P_0 = 1`, `P_{t+u} = P_t P_u`,
The generator is `−T†T` on `D(T†T)`. This is only the first of the four preliminary statements in Buser's program: Gap Two (Markov property), Three (Bakry–Émery Γ calculus),
Four (small time heat estimate) remains unchanged, `thm:logconcave-cheeger-poincare-comparison` no `\leanok`, the constant π is untouched.
`tasks.json` This node `infrastructure.status` remains `missing`, the first gap is augmented with the note "semigroup construction is complete", the other three gaps remain unchanged.

### Friction (for the next round)

`NormedSpace.exp_add_of_commute` lacks `NormedAlgebra ℚ` instance on `H₀ →L[ℝ] H₀`, use `exp_add_of_commute_of_mem_ball (𝕂 := ℝ)` + `expSeries_radius_eq_top ℝ _`. `abs_add` does not exist, use `abs_add_le`. `IsSelfAdjoint.smul` requires `show IsSelfAdjoint (-t) from star_trivial _`.
`push_neg` is deprecated in this pin (reports error under `-DwarningAsError`), use `rw [not_le]`. `div_add_div_same` does not exist.
`field_simp` closing the goal by itself and then `ring` will report "No goals".
