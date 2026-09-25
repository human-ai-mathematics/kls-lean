# Reverse local Poincaré inequality and Bakry's L¹ self-improvement

## Placement and scope

This continues the [square-estimate record](2026-09-23-heat-gradient-square-estimate.md). The
placement plan was recorded in `HANDOFF.md` before editing. The two estimates proved here are
the heat-semigroup inputs of the sharp Buser route in the
[Bakry–Émery route](2026-09-20-bakry-emery-route.md): De Ponti–Mondino (28) and their
Proposition 3.1 (32)–(33), for `K = 0`.

| Module | Change | Content |
| --- | --- | --- |
| [BakryEmery/Calculus.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean) | extended | `laplacian_comp` |
| [BakryEmery/Gamma.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean) | extended | `weightedLaplacian_comp` |
| [BakryEmery/Bochner.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner.lean) | extended; imports Mathlib `Deriv.Inv` and `Sqrt` | `norm_gradient_norm_gradient_sq_le`, `weightedLaplacian_sqrt_sub_div_nonneg` |
| [BakryEmery/RegularizedNorm.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/RegularizedNorm.lean) | new; imports WeakGamma | the function `N_ε` and its pointwise and tested calculus |
| [Semigroup/Generated/TimeDerivative.lean](../../formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean) | extended | `hasDerivAt_apply_of_pos` |
| [HeatSemigroup/ReversePoincare.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/ReversePoincare.lean) | new; imports GradientEstimate | carré identity and reverse local Poincaré |
| [HeatSemigroup/SelfImprovement.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/SelfImprovement.lean) | new; imports GradientEstimate and RegularizedNorm | the `L¹` self-improvement |

`RegularizedNorm.lean` is a separate module because the regularized norm is its own object.
The root imports the three new modules. No existing declaration changed. The baseline is
`build/audit/heat-bgl-selfimprovement/baseline/`.

## Formalized in Lean

**Chain rule.** Suppose `h` has derivative `h'(G y)` at every value `G y`, and `h'` has
derivative `h''(G x)` at `G x`. Then
`Δ(h∘G) = h'(G)ΔG + h''(G)|∇G|²` and `ℒ(h∘G) = h'(G)ℒG + h''(G)Γ(G)` for `C²` `G`. No
global smoothness of `h` is needed, so `h = √(ε + ·)` is allowed on `G ≥ 0`.

**Improved Bochner.** For a `C²` convex `U` and a `C³` `f`,
`‖∇‖∇f‖²‖² ≤ 4‖∇f‖² Γ₂(f)` (`norm_gradient_norm_gradient_sq_le`). The proof uses
`∂ᵢ‖∇f‖² = 2Σⱼ ∂ⱼf D²f(eᵢ,eⱼ)`, Cauchy–Schwarz in `j`, the Bochner identity, and
`D²U(∇f,∇f) ≥ 0`. It follows that for `ε > 0`,
`0 ≤ ℒ(√(ε+Γ(f)) - √ε) - Γ(f,ℒf)/√(ε+Γ(f))`
(`weightedLaplacian_sqrt_sub_div_nonneg`): with `r = √(ε+Γ)` the expression is at least
`εΓ₂(f)/r³`.

**Regularized norm.** `N_ε(a) = √(ε+‖a‖²) - √ε` and `U_ε(a) = a/√(ε+‖a‖²)`, with these
properties:

- `0 ≤ N_ε ≤ ‖·‖`, and `N_ε` is `1`-Lipschitz;
- `‖U_ε‖ ≤ 1`, and `U_ε` is `2/√ε`-Lipschitz;
- the Taylor bound `|N_ε(b) - N_ε(a) - ⟪U_ε(a), b-a⟫| ≤ ‖b-a‖²/√ε`;
- `N_ε → ‖·‖` as `ε → 0⁺`.

The tested layer, on a finite measure, has four results:

- joint convergence of `∫ qᵢ N_ε(uᵢ)`, for uniformly bounded multipliers converging in `L²`;
- convergence of `∫ ψ ⟪U_ε(uᵢ), wᵢ⟫`;
- the product rule for `s ↦ ∫ q s · N_ε(u s)`, whose remainder is controlled by the Taylor
  bound;
- the dominated limit `ε → 0⁺`.

**Carré identity** (`integral_adjointComp_mul_apply_sub_eq`). For `g ∈ D(A)` and `ψ ∈ D(A)`
with `ψ` and `Aψ` bounded:

```text
∫ (Aψ) g² dν - 2∫ ψ g (Ag) dν = -2∫ ψ Γ(T̄g, T̄g) dν.
```

On `C_c^∞` it is `ℒ(q²) = 2qℒq + 2Γ(q)` tested by generator symmetry. It is transferred along
the operator core, and the gradient field converges by `‖T̄x‖² ≤ ‖Ax‖‖x‖`.

**Reverse local Poincaré** (`two_mul_integral_mul_weakGamma_le`). It holds for arbitrary
`f ∈ L²(ν)`, `t > 0` and nonnegative `φ ∈ C_c^∞`, with smooth convex `U`:

```text
2t ∫ φ Γ(T̄P_t f) dν ≤ ∫ (P_t φ) f² dν - ∫ φ (P_t f)² dν.
```

The proof uses the interpolation `Λ(s) = ∫ (P_s φ)(P_{t-s} f)² dν`:

- The time derivative of `P_{t-s} f` for arbitrary `f` comes from `hasDerivAt_apply_of_pos`.
- The product rule and the carré identity give `Λ'(s) = 2∫ (P_s φ) Γ(T̄P_{t-s} f)`.
- By the square estimate, `Λ'(s) ≥ 2∫ φ Γ(T̄P_t f)`.
- A right-derivative comparison with an affine function on `[0, t]` finishes the proof.

`two_mul_integral_mul_weakGamma_le_of_bounded` covers bounded data: if `|f| ≤ M`, then
`2t ∫ φ Γ(T̄P_t f) ≤ M² ∫ φ`. This is the tested form of `|T̄P_t f| ≤ M/√(2t)`. It uses
positivity and mass conservation of `P_t`.

**`L¹` self-improvement** (`integral_mul_norm_le`). It holds for every `f ∈ D(T̄)`, `t ≥ 0`
and nonnegative `φ ∈ C_c^∞`, with smooth convex `U`:

```text
∫ φ |T̄P_t f| dν ≤ ∫ (P_t φ) |T̄f| dν.
```

The proof has five steps:

1. On smooth data (`integral_regularizedNorm_smooth_nonneg`),
   `0 ≤ -∫ (Aψ)N_ε(∇q) + ∫ ψ⟪U_ε(∇q), ∇(-ℒq)⟫`. This is the pointwise inequality tested by
   generator symmetry; `√(ε+Γ(q)) - √ε` is `C_c^∞`.
2. The inequality transfers to every `F ∈ D(A)` with `AF ∈ D(T̄)` along the two-field core
   (`integral_regularizedNorm_nonneg`).
3. `r ↦ ∫ (P_{t-r} φ) N_ε(T̄P_r g)` is monotone on `[a, t]`: its right derivative is minus
   the quantity of step 2.
4. Let `a → 0⁺` using form-domain continuity.
5. Let `ε → 0⁺` by dominated convergence.

## Clients

[BakryEmeryReverseSelfImprovementAudit.lean](../audits/BakryEmeryReverseSelfImprovementAudit.lean)
checks:

- the reverse inequality for arbitrary `f` and for bounded `f`, and its zero test;
- the `L¹` estimate for arbitrary `f ∈ D(T̄)` and for heat data `P_ε g`;
- both pointwise inputs, for an arbitrary `C²` convex potential.

Twenty-seven transitive axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`.

## Not claimed

Every statement is integrated against nonnegative `C_c^∞` tests. No pointwise a.e. form is
claimed: neither `|T̄P_t f| ≤ P_t|T̄f|` a.e. nor `‖T̄P_t f‖_∞ ≤ ‖f‖_∞/√(2t)`. Passing from
tests to an a.e. inequality needs a positivity analogue of
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, which is not proved here. Also not proved:

- the `K ≠ 0` forms;
- the small-time BV estimate `‖f - P_t f‖₁ ≤ J(t) |Df|`;
- the general-law passage, the constant π, Buser's inequality and KLS.

Smoothness and convexity of `U`, and the tilted representation, remain explicit premises.

## Verification

Strict source and client checks, the full build and the project verifier are logged under
`build/audit/heat-bgl-selfimprovement/`. Its `final-snapshot.json` records the verifier
outcome, report and source snapshot. Pinned dependency artifacts are trusted. There was no
remote CI, commit, push or change to the real Git index.
