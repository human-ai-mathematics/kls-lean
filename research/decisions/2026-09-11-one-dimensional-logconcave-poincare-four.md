# 2026-09-11 — `thm:one-dimensional-logconcave-poincare`: strengthening the constant from 12 to 4

## Decision

- Change Blueprint node `thm:one-dimensional-logconcave-poincare` from `C_P^lit(ν) ≤ 12 Var_ν(T)` to `C_P^lit(ν) ≤ 4 Var_ν(T)`. This is a **statement change** (strengthening), not a new node. Retain Bobkov's 12 as a corollary and its independent proof (`KLS/LogConcave/Line/Poincare.lean` unchanged).
- Evidence: collaborator audit `research/explorations/2026-09-11-poincare-constant-4-audit.md`, supplied by the user on 2026-09-11 and checked step by step. See supplements one and two of the 2026-09-10 decision for the literature check: Alonso-Gutiérrez–Bastero p.11 cites 4 without proving it. Organize the local Lean proof by the audit's x-coordinate version, without introducing a quantile function.
- Constant 4 is attained by the exponential law; no smaller universal constant can be asserted.
- No commit or push, per user instruction.

## Lean statements (formech style)

Claim (`Solutions.ThmOneDimensionalLogConcavePoincare.certificate`): for every
`ν : ProbabilityMeasure ℝ` and `hν : KLS.LogConcave ν`:

1. `Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (4 * variance id ν)`;
2. `Poincare.LocalSlope.Intrinsic.constant ν ≤ 4 * evariance id ν`.

Typed applications: finiteness of the constant; `≤ ENNReal.ofReal (12 * variance id ν)` derived
from 4; Dirac-law constant `≤ 0`; and `Poincare.SmoothTest.Holds ν (4 * variance id ν)` when
the support interior is nonempty.

Non-claims: a smaller constant, higher-dimensional bounds, Cheeger inequality, raw-energy
conclusions, or strengthening `cor:conditional-fiber-twelve-bound` (still `12C`, in chapter 50,
being edited by another session and left for later).

Additional finiteness restrictions: none. Dimension zero: singleton affine support has
direction space `⊥` and constant 0, reusing `Line/Poincare.lean`.

## Clause-by-clause alignment (Blueprint ↔ Lean)

| Blueprint | Lean | Assessment |
|---|---|---|
| Supporting line `ρ ≤ A(1−F)+BF`, `A,B ≥ 0` | `d.le_affine_of_supergradient`, `d.affine_pos_of_bound`, `Probability.Line.nonneg_of_affine_pos` | Aligned; Lean uses supporting exponent `d.exists_supergradient` at `x₀ ∈ Ω` |
| `q∘F` is 1-Lipschitz, `Var_{[0,1]}(q) ≤ σ²` | Inside `d.variance_ge_of_affine_bound`: `Var Ψ(X) ≤ E(Ψ X − Ψ E)² ≤ E(X−E)²`, mean `E ∈ Ω` (`LogConcave.mean_mem_interior_support`) | Aligned; Lean uses the mean instead of an arbitrary anchor |
| `Var_{[0,1]}(q) ≥ (√A+√B)^{-4}` | `Probability.Line.one_div_le_variance_affineQuantile` (closed form `variance_affineQuantile` plus `mul_mul_log_sub_sq_le`, the latter via `t ≤ sinh t`) | Aligned |
| Profile bound `F(1−F) ≤ σρ` | `d.cdf_mul_one_sub_cdf_le_sd_mul` (perturb `A+ε, B+ε`, then take limits) | Aligned |
| Truncated tests, `∫h² = −∫_a^b f'G̃` | `KLS.clip`, `clipCentered`, `tailIntegral`, `d.integral_sq_clipCentered_eq` | Aligned |
| Ground-state identity and boundary terms | `d.groundState_inequality` on larger `[c,e]`, `d.boundaryTerm_le_of_le`, `d.neg_boundaryTerm_le_of_ge`, `d.integral_sq_div_le` (ε argument with `F c → 0`, `F e → 1`) | Lean is stronger: explicitly gives boundary term `h(a)²F(c) + h(b)²(1−F(e))` |
| `Var(f_ab) ≤ 4σ²∫f'²` | `d.variance_clip_le` (AM–GM `−f'G̃ ≤ G̃²ρ/(8W²) + 2f'²W²/ρ` plus profile bound) | Aligned |
| Vanishing tails | `d.setIntegral_Iic_sq_sub_le_of_le`, `d.setIntegral_Ioi_sq_sub_le_of_le` (generalizations of median versions in `Hardy.lean`, with anchor `p` on the same side of the median and unchanged `1/ρ(m)²`) plus `Probability.exists_pos_forall_setIntegral_le` (absolute continuity of the integral with respect to measure) and `exists_cdf_eq` selecting `F a = t` | Aligned; the audit split bounded/unbounded-below Ω cases using `f(a)²F(a)` and `∫_{Iic a} f²`; Lean avoids this split with anchored Hardy bounds |
| `(1+δ)` splitting and limits | `Probability.add_sq_le_split`, `d.variance_le_four_variance_mul` (`le_of_forall_pos_le_add`) | Aligned; the audit used Minkowski, Lean uses δ splitting without square roots |
| Smooth-test optimum = literature optimum | `LogConcave.smoothTest_constant_eq_localSlope` (certified) | Aligned |

## Mathematical correction during the proof

- The first plan truncated the ground-state identity directly on `[a,b]`, but boundary signs were reversed (`Ξ(a) ≥ 0 ≥ Ξ(b)`), so it failed. Instead integrate over a larger `[c,e] ⊆ Ω` containing `[a,b]`, use `G̃ = h(a)F` for `x ≤ a` and `G̃ = −h(b)(1−F)` for `x ≥ b` to bound `Ξ(c) ≤ h(a)²F(c)` and `−Ξ(e) ≤ h(b)²(1−F(e))`, then let `F(c) → 0` and `F(e) → 1`.

## Files

- New: `Probability/Line/AffineProfile.lean`, `KLS/LogConcave/Line/Profile.lean`, `Line/SharpHardy.lean`, `Line/SharpPoincare.lean`.
- Modified: `Probability/Line/Cdf.lean` (`exists_cdf_eq` for general `t`, `cdf_pos/lt_one_of_mem_interior_support`), `KLS/LogConcave/Line/Hazard.lean` (`le_add_mul_cdf_sub_of_mem`, median version as a corollary), `KLS/LogConcave/Line/Hardy.lean` (four half-line/interval Hardy lemmas generalized to `_of_le`; old names retained as `p = m` wrappers).
- Certificate: `solutions/ThmOneDimensionalLogConcavePoincare.lean` changes its claim to 4 and adds 9 axiom guards.
- Registration: ledger statement/source, `tasks.json` (new evidence files and hashes), Blueprint `\lean{}` and statement/proof, publication reference in `route-composition.yaml`, imports in `FunctionalInequalities.lean`, and README/HANDOFF/verification/naming documents.

## Next

- `cor:conditional-fiber-twelve-bound` (chapter 50) can strengthen `12C` to `4C` after the other session finishes ConditionalFiber work.
- The location of constant 4 in the original KLS 1995 paper remains unchecked; the local proof no longer depends on that attribution.
