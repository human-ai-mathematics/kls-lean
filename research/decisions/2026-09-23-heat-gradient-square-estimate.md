# Time interpolation and the integrated square gradient estimate

## Placement and scope

This continues the [heat-test frontend](2026-09-23-heat-test-extension-frontend.md). It
implements steps 3–5 of §6 of the [Bakry–Émery route](2026-09-20-bakry-emery-route.md):
time differentiation of the interpolation, the justified limits, and the square estimate
`Γ(P_t f) ≤ P_t Γ(f)` in integrated form. The placement plan was recorded in `HANDOFF.md`
before editing. One deviation from that plan: the multiplier/field convergence lemma and the
tested product rule went into
[WeakGamma.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/WeakGamma.lean)
rather than into the KLS module, since they are generic statements about tested weak `Γ`.

| Module | Change | Content |
| --- | --- | --- |
| [L2/BoundedMultiplier.lean](../../formalization/FunctionalInequalities/L2/BoundedMultiplier.lean) | extended | `exists_clamp_integral_lt`, `tendsto_integral_mul_of_tendsto` |
| [BakryEmery/WeakGamma.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/WeakGamma.lean) | extended; imports BoundedMultiplier and Mathlib slopes | `tendsto_integral_mul_of_tendsto_multiplier`, `hasDerivWithinAt_integral_mul_apply_self` |
| [Semigroup/Generated/TimeDerivative.lean](../../formalization/FunctionalInequalities/Analysis/Semigroup/Generated/TimeDerivative.lean) | new; imports Smoothing | generic time derivatives and continuity |
| [HeatSemigroup/GradientEstimate.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/GradientEstimate.lean) | new; imports TestClassExtension and TimeDerivative | difference bound, interpolation, square estimate |

The root imports the two new modules. No existing declaration changed. The baseline is
`build/audit/heat-gradient-square/baseline/`.

## Formalized in Lean

**Generic `L²`/`L¹` pairing.** On a finite measure, let `qᵢ → q₀` in `L²` along any filter,
with a uniform a.e. bound `D`. Then `∫ qᵢ G → ∫ q₀ G` for every integrable `G`, square
integrable or not. The proof truncates `G` at level `M`, and dominated convergence controls
the `L¹` tail (`tendsto_integral_mul_of_tendsto`).

**Tested weak `Γ`.** `tendsto_integral_mul_of_tendsto_multiplier` combines the pairing lemma
with the existing `abs_integral_mul_sub_le`. Multipliers converge in `L²` under a uniform
bound, and fields converge in `L²`. The result is joint convergence of `∫ qᵢ Γ(uᵢ, vᵢ)`.

`hasDerivWithinAt_integral_mul_apply_self` is a product rule. Suppose `q` and `u` have
derivatives `q'` and `u'` within `S` at `r`, and `q r`, `q'` and the difference quotients of
`q` are a.e. bounded by one `D`. Then `s ↦ ∫ q s Γ(u s, u s)` has derivative
`∫ q' Γ(u r, u r) + 2 ∫ q r Γ(u r, u')`.

**Generic time derivatives.** Take `T` closed and densely defined, with `A = T†T`.

- `hasDerivWithinAt_apply_Ici`, `hasDerivWithinAt_apply_Iic` and `hasDerivAt_apply`:
  for `f ∈ D(A)`, `t ↦ P_t f` has derivative `-A P_t f`. This is one-sided at `t ≥ 0` and
  two-sided at `t > 0`.
- `norm_map_sq_le_mul`: `‖T x‖² ≤ ‖A x‖ ‖x‖` on `D(A)`.
- `adjointComp_apply_mem_adjointComp_domain_of_pos`: `A P_t g ∈ D(A)` for arbitrary `g`
  and `t > 0`.
- `hasDerivWithinAt_map_apply_Ici`: the gradient orbit `t ↦ T P_t g` has right derivative
  `-T A P_t g`. The proof bounds `‖T x_h‖² ≤ ‖A x_h‖ ‖x_h‖` for
  `x_h = h⁻¹(P_h F - F) + AF`, with `F ∈ D(A²)`.
- `continuousOn_map_apply`: the gradient orbit is continuous on `(0, ∞)`.
- `tendsto_map_apply_zero`: for `f ∈ D(T)`, `T P_s f → T f` as `s → 0⁺`. The proof uses the
  graph-norm density of `D(A)` and the contraction on `D(T)`.

The partially defined orbit is passed as any function agreeing with it where defined; no
total extension of `T` is introduced.

**Difference-quotient bound.** `ae_abs_operator_sub_le` (arbitrary weight `B`): if `ψ ∈ D(A)`
and `|Aψ| ≤ D` a.e., then `|P_h ψ - ψ| ≤ h D` a.e. for `h ≥ 0`. Fix a measurable set `s`.
The real function `τ ↦ ∫_s (P_τψ - ψ)` has right derivative `-∫_s P_τ(Aψ)`, and Markov
contraction bounds its absolute value by `D ν(s)`. A right-derivative comparison
(`image_le_of_deriv_right_le_deriv_boundary`) then bounds `|∫_s (P_hψ - ψ)| ≤ h D ν(s)` for
every `s`, and this set-integral bound gives the a.e. bound.

**Interpolation.** The setting is `ν = m.tilted (-U)` with a smooth convex potential and
unit weight. `integral_mul_weakGamma_le_of_pos` holds for arbitrary `g ∈ L²(ν)`,
`0 < a ≤ t` and nonnegative `φ ∈ C_c^∞`:

```text
∫ φ Γ(T̄P_t g, T̄P_t g) dν ≤ ∫ (P_{t-a} φ) Γ(T̄P_a g, T̄P_a g) dν.
```

This is `Ψ(t) ≤ Ψ(a)` for `Ψ(r) = ∫ (P_{t-r} φ) Γ(T̄P_r g, T̄P_r g) dν`. On `[a, t)`:

- The test factor has right derivative `A P_{t-r} φ`: the left derivative of `P`, composed
  with `r ↦ t - r`.
- Its difference quotients are `P_{t-s}((s-r)⁻¹(φ - P_{s-r} φ))`. They are bounded by
  `sup |ℒφ|` via the difference bound and Markov contraction.
- The gradient orbit has right derivative `-T̄AP_r g`.

The product rule gives `Ψ'(r) = ∫ (Aψ)Γ(T̄F,T̄F) - 2∫ ψ Γ(T̄F,T̄AF)`, with `ψ = P_{t-r}φ` and
`F = P_r g`. This is `-2` times the frontend `integral_weakGamma_operator_nonneg`, so
`Ψ' ≤ 0`. `Ψ` is continuous on `[a, t]` by joint convergence.

**Square estimate.** `integral_mul_weakGamma_le` holds for every `f ∈ D(T̄)` and `t ≥ 0`:

```text
∫ φ Γ(T̄P_t f, T̄P_t f) dν ≤ ∫ (P_t φ) Γ(T̄f, T̄f) dν.
```

At `t = 0` both sides are equal. For `t > 0` it is the limit `a → 0⁺` of the interpolation:
`P_{t-a} φ → P_t φ` under a uniform bound, and `T̄P_a f → T̄f`. Since `Γ(T̄f)` is only `L¹`,
the right side is the meaning of `∫ φ P_tΓ(f)` by symmetry of `P_t`. No `L²` semigroup is
applied to `Γ(T̄f)`.

## Clients

[BakryEmeryGradientEstimateAudit.lean](../audits/BakryEmeryGradientEstimateAudit.lean)
checks:

- `arbitrary_data`: arbitrary `g`, `0 < a ≤ t`;
- `form_domain`: arbitrary `f ∈ D(T̄)`, `t ≥ 0`;
- `heat_data`: `f = P_ε g`, arbitrary `g`;
- `time_zero`: both sides coincide at `t = 0`;
- `zero_test`: `φ = 0`; both sides vanish and the estimate applies;
- `difference_bound`: `|P_h φ - φ| ≤ h D` with one `D` for all `h ≥ 0`.

Twenty-two transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

## Not claimed

This record does not prove any of the following:

- a pointwise statement `Γ(P_t f) ≤ P_t Γ(f)` a.e. There is no `L¹` extension of `P_t`,
  and the integrated form is against `C_c^∞` tests only.
- the exponential or `K`-dependent versions;
- the `L¹`-type self-improvement `|T̄P_t f| ≤ P_t |T̄f|`, which is De Ponti–Mondino (28);
- the reverse Bakry–Gentil–Ledoux estimate and the `L^∞ → Lip` regularization (their (32)
  and (33));
- the small-time BV estimate, the general-law passage, the constant π, the Buser inequality,
  or KLS.

Smoothness and convexity of `U` and the tilted representation remain explicit premises.

## Verification

Strict source and client checks, the full build and the project verifier are logged under
`build/audit/heat-gradient-square/`. Its `final-snapshot.json` records the verifier outcome,
report and source snapshot. Pinned dependency artifacts are trusted. There was no remote CI,
commit, push or change to the real Git index.
