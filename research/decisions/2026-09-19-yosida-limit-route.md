# Semigroup generation route: `S6` (Strong convergence of Yosida exponent) path cycle

2026-09-19, followed by [von Neumann round](2026-09-19-von-neumann-route.md). This round **only writes definitions and statements, without proofs**; proofs are delegated to two parallel Opus sessions, `Y8` is combined by this session during integration. No commit, no push.

## A Correction to an Earlier Path

The **abstract** formulation of `S6` in `SemigroupGenerationRouteStatements.lean` asserts that for any family satisfying only non-negativity and commutativity,
`L : ℝ → H₀ →L[ℝ] H₀`, `exp(-t • L s) f` converges as `s ↓ 0` —— **false**. Counterexample: `L s = c(s) • 1`,
`c` Take `0` and `1` at points tending to `0⁺` in each column, then `exp(-t • L s) f = e^{-t c(s)} f` has no limit.
By convention, the byte-level file remains unchanged, counterexamples are explicitly stated and delivered with proofs as `Y0`; the corrected abstract `S6` is `Y7`
(With the additional assumption of "Cauchy on a dense set"), the Yosida approximation `S6` is `Y8`.

## Definition module (this round has been written and compiled)

`formalization/FunctionalInequalities/Analysis/Semigroup/YosidaApproximation.lean`:
`yosida T hT hs := s⁻¹ • (1 - resolventCLM T hT hs)`, i.e. `L_s`, plus `yosida_apply` and `smul_yosida_apply` two `simp`-level lemmas.
`-DwarningAsError=true` passed, olean has been generated.

## Statement file

`research/audits/YosidaLimitRouteStatements.lean`, contains only `#check`, all 9 pass type checking:

| Number | Content | Input | Risk |
| --- | --- | --- | --- |
| `Y0` | abstract `S6` is false on `H₀ = ℝ` | none | low to medium: construct `c`, prove the limits of two subsequences are different |
| `Y1` | `0 ≤ ⟪L_s f, f⟫` | `norm_resolventCLM_le` | low |
| `Y2` | `⟪L_s f, g⟫ = ⟪f, L_s g⟫` | `resolventCLM_symm` | low |
| `Y3` | `L_s L_r = L_r L_s` | `R3` | low |
| `Y4` | `L_s f = J_s (T†T f)`, `f ∈ D(T†T)` | `V5` | low |
| `Y5` | `L_s f → T†T f`, `f ∈ D(T†T)` (ε–δ) | `Y4` + `R2` | low |
| `Y6` | `‖e^{-tA} f − e^{-tB} f‖ ≤ t‖Af − Bf‖`, `A, B` bounded non-negative commutative | `S5`, `hasDerivAt_exp_smul_const`, `Commute.exp_right`, mean value inequality | **High**: the analytical core of this route |
| `Y7` | Corrected abstract `S6`: Cauchy on dense set ⟹ pointwise convergence | `Y6` + `S5` + completeness | Medium: ε/3 argument |
| `Y8` | Yosida approximation `S6` | `Y7` + `Y1` + `Y3` + `V4` + `Y5` | Low: combinatorial |

All `s ↓ 0` limits use the ε–δ formulation (`resolventCLM` and `yosida` carry `0 < s`), with families written as `∀ s, 0 < s → H₀ →L[ℝ] H₀`;
Only `Y0` uses `Tendsto` and `𝓝[>] 0`, in direct correspondence with the original `S6`.

## Division of labor

* Session A: `Y0`–`Y5`, new module `Analysis/Semigroup/YosidaFamily.lean`, audit `research/audits/YosidaFamilyAudit.lean`.
* Session B: `Y6`–`Y7` (bounded operators only, no import of any `T`), new module `Analysis/Semigroup/SemigroupLimit.lean`,
  audit `research/audits/SemigroupLimitAudit.lean`.
* `Y8` = `Y7 ∘ (Y1, Y3, V4, Y5)`, after completion of both sessions, combined into `YosidaFamily.lean` or as an independent small module, and incorporated into audit.

Rules as before: create only new files, use only `lake env lean -DwarningAsError=true`, do not `lake build`, do not `verify.py`, do not git, do not modify existing files, zero `sorry`.

## Out of scope

`S7` (semigroup law of limits and strong continuity), `S8` (generator is `T†T`) un-stated. Markov property, Γ calculus, small-time heat estimate, Buser inequality are not included in this round.
`thm:logconcave-cheeger-poincare-comparison` no progress marked, `tasks.json` unchanged (registered uniformly during integration).

## Appendix: `Y0`–`Y8` all proven, `S6` closed (same day; two parallel Opus session runs for approximately 9 and 11 minutes, `Y8` from the combination of this session)

| Number | Statement | Module | Notes |
| --- | --- | --- | --- |
| `Y0` | `not_forall_exists_tendsto_exp_neg_smul` | `YosidaFamily.lean` | abstract `S6` is false, coefficients taken `Set.indicator` in `{1/(n+1)}`, second column `2/(2n+3)` |
| `Y1`–`Y3` | `yosida_nonneg`, `yosida_symm`, `yosida_comp_comm` | `YosidaFamily.lean` | draft |
| `Y4`, `Y5` | `yosida_apply_eq_resolventCLM_adjointComp`, `exists_delta_norm_yosida_sub_adjointComp_lt` | `YosidaFamily.lean` | **`Dense` is actually used** (V5 via `inner_adjointComp` dependent adjoint with non-garbage values), contrary to the guess about the route table |
| `Y6` | `norm_exp_neg_smul_sub_le` | `SemigroupLimit.lean` | interpolation path takes `exp(τ•(-A))(exp((τ−t)•B) f)`, use non-prime `hasDerivAt_exp_smul_const`; the mean value inequality in this pin only requires a derivative bound on `Ico` |
| `Y7` | `exists_limit_exp_neg_smul` | `SemigroupLimit.lean` | Cauchy step invokes the assumption at `ε/(t+1)` to accommodate `t = 0` |
| `Y8` | `exists_limit_exp_neg_smul_yosida` | `YosidaLimit.lean` | `Y7 ∘ (Y1, Y3, V4, Y5)`, written in this session and passed on the first attempt |

Audit: `YosidaFamilyAudit.lean` 26 , `SemigroupLimitAudit.lean` 11 , `YosidaLimitAudit.lean` 4 `#print axioms`,
**41 statements contain only `propext, Classical.choice, Quot.sound`, 0 `sorryAx`**; 9 route statements are token-by-token identical to the route file (recompiled independently and mechanically compared in this session).
Four new modules (`YosidaApproximation`, `YosidaFamily`, `SemigroupLimit`, `YosidaLimit`) have been integrated into the aggregate root, `lake build` 3528 jobs have passed,
Ten semigroup audit client recompilations strictly exit 0. **No route assumptions can be removed**, each assumption of `Y6` and `Y7` is used.

### Semigroup path status

`S1`–`S6` proved. Remaining `S7` (the limit `P_t f := lim exp(-t L_s) f` is a strongly continuous self-adjoint contraction semigroup: `P_{t+u} = P_t P_u`, `P_0 = 1`, `t ↦ P_t f` continuous, `‖P_t f‖ ≤ ‖f‖`, symmetric) and `S8` (the generator is `T†T`: `f ∈ D(T†T)` ⟹ `(P_t f − f)/t → −T†T f`).
Next, we first name the quantified limit `g` in `Y8` as the operator `P_t` (via a selection function or `limUnder`), then state `S7`, `S8`.

### Friction (for the next round)

`NormedSpace.exp_smul` is about the conjugate of `MulSemiringAction`, not a scalar; `ℝ →L[ℝ] ℝ` on `exp(a•1) x = Real.exp a * x`
using `NormedSpace.map_exp` along algebraic mappings. `ContinuousLinearMap.mul_apply` and `smul_apply` are deprecated in this pin (an error under `-DwarningAsError`),
using `mul_def` + `comp_apply`, root namespace `smul_apply`. `div_le_div_iff` has been removed, use `div_le_div_iff₀`.
`ℝ →L[ℝ] ℝ` on `ext f` triggers `unusedRCasesPattern`, using `refine ContinuousLinearMap.ext fun f => ?_`. `⟪x, y⟫_ℝ = x * y` is `Real.inner_apply`, not `rfl`.
