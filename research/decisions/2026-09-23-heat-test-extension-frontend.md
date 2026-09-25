# Heat-test extension: two-field convergence and the arbitrary-data frontend

## Placement and scope

This completes the route of the
[wave-approximation record](2026-09-22-heat-test-wave-approximation.md#from-this-construction-to-the-requested-two-fields),
after the [form-range continuation](2026-09-23-wave-splitting-form-range.md). The placement
plan was recorded in `HANDOFF.md` before editing:

- [VonNeumann.lean](../../formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean)
  gains two generic `V1`-level results (namespace `Analysis.Semigroup`, no new import).
- [FormRange.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/FormRange.lean)
  gains the concrete two-field core. It adds an explicit `VonNeumann` import, which was
  previously transitive.
- New module [TestClassExtension.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/TestClassExtension.lean)
  (namespace `KLS.LogConcave.HeatSemigroup`) imports TestClass and FormRange. This keeps
  TestClass free of the wave-splitting chain.

The library root imports the new module. No existing declaration changed; the only edits to
existing files are the additions above and their module docstrings. The baseline is
`build/audit/heat-test-splitting-two-field/baseline/`.

## Formalized in Lean

**Second-order graph norm (generic).** Let `T : H₀ →ₗ.[ℝ] H₁` have dense domain, with
`A = T†T` (`adjointComp`) and `J = I + A`. For `e ∈ D(A)` with `Ae ∈ D(T)`,
`norm_add_adjointComp_sq_add_norm_sq` proves

```text
‖e + Ae‖² + ‖Te + T(Ae)‖² = ‖e‖² + 3‖Te‖² + 3‖Ae‖² + ‖T(Ae)‖².
```

Both cross terms are `V1`: `⟪e, Ae⟫ = ‖Te‖²` and `⟪Te, T(Ae)⟫ = ‖Ae‖²`. Neither closedness
nor completeness of `H₁` is used.

`tendsto_of_tendsto_add_adjointComp` is the sequential consequence. Let `xₙ, F ∈ D(A)` with
`Axₙ, AF ∈ D(T)`. Suppose `xₙ + Axₙ → F + AF` and `Txₙ + T(Axₙ) → TF + T(AF)`. Then all four
fields converge: `xₙ → F`, `Txₙ → TF`, `Axₙ → AF` and `T(Axₙ) → T(AF)`. The proof applies
the identity to `xₙ - F` and bounds each square by the vanishing left side.

**Two-field smooth core.** The setting is `ν = m.tilted (-U)` log-concave with nonempty
interior support, `U` smooth, and `T̄` the closed unit-weight gradient.
`exists_seq_smooth_tendsto_two_fields` covers every `F ∈ D(A)` with `AF ∈ D(T̄)`. It gives
`qₙ ∈ C_c^∞(V)` with, in `L²(ν)`:

```text
[qₙ] → F,  [∇qₙ] → T̄F,  [-ℒqₙ] → AF,  [∇(-ℒqₙ)] → T̄(AF).
```

The proof has three steps:

1. Apply the density theorem to `z = F + AF ∈ D(T̄)` with tolerance `1/(n+1)`.
2. Convert the graph-norm bound into the two hypotheses of the generic lemma. This uses
   linearity of `T̄` on its domain.
3. Identify the four fields through `closedWeightedOperator_toLp_eq` and
   `adjointComp_toLp_eq`. For the last field, `-ℒqₙ ∈ C_c^∞` is used.

The fields are classes of actual `C_c^∞` functions and their classical gradients.

**The frontend.** `integral_weakGamma_operator_nonneg` has these premises:

- `hν : LogConcave ν`, `hi`, `hνU : ν = m.tilted (-U)`;
- `hU : ContDiff ℝ ∞ U` and `hconv : ConvexOn ℝ univ U`;
- arbitrary `g ∈ L²(ν)` and `r > 0`;
- `φ ∈ C_c^∞` with `φ ≥ 0`, and `s ≥ 0`.

Put `F = P_r g` and `ψ = P_s[φ]`. Then:

- `(Aψ) Γ(T̄F, T̄F)` is integrable;
- `ψ Γ(T̄F, T̄(AF))` is integrable;
- `0 ≤ -(∫ (Aψ) Γ(T̄F, T̄F) dν)/2 + ∫ ψ Γ(T̄F, T̄(AF)) dν`.

Here `Γ` is `WeakGamma.apply`, and the domain witnesses are
`mem_closedWeightedOperator_domain_of_pos`, `mem_adjointComp_domain_of_pos` and
`mem_closedWeightedOperator_domain_adjointComp_of_pos`. The inequality is
`integral_weakGamma_nonneg_of_mem_domain_of_tendsto`, applied with the essential bounds of
`exists_bounds_operator_toLp`, heat-flow positivity, `uₙ = [∇qₙ]`, `wₙ = [∇(-ℒqₙ)]` (equal a.e.
to `-∇ℒqₙ` by `gradient_neg`) and the two limits of the core. The integrabilities are
`integrable_operator_toLp_weakGamma`.

The signature keeps every arbitrary-data quantifier. It has no wave, core, residual, sequence,
regularity or extra potential-bound premise.

## Clients

[BakryEmeryHeatTestExtensionAudit.lean](../audits/BakryEmeryHeatTestExtensionAudit.lean)
checks:

- `arbitrary_data`: the frontend for arbitrary `g`, `r > 0`, `s ≥ 0` and `φ ≥ 0`;
- `time_zero`: at `s = 0`, `ψ = [φ]` and `Aψ = [-ℒφ]`, so
  `0 ≤ -(1/2)∫(-ℒφ)Γ(T̄F,T̄F) + ∫ φ Γ(T̄F,T̄(AF))` with the classical `φ`;
- `zero_test`: for `φ = 0` both pairings are `0`;
- `graph_norm_identity`: the second-order expansion at `F = P_r g`;
- `two_field_core`: the two required field limits at `F = P_r g`.

Nine transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

## Not claimed

This record does not prove:

- the time interpolation `s ↦ ∫ (P_s φ) Γ(T̄(P_{t-s} f)) dν`, or its differentiation and
  limits;
- `Γ(P_t f) ≤ P_t Γ(f)` or any pointwise or square gradient estimate;
- small-time heat bounds, the passage to general log-concave laws, the Buser constant π, or
  KLS.

The tilted representation, smoothness and convexity of `U` remain explicit premises.

## Verification

Strict source and client checks, the full build and the project verifier are logged under
`build/audit/heat-test-splitting-two-field/`. Its `final-snapshot.json` records the verifier
outcome, report and source snapshot. Pinned dependency artifacts are trusted. There was no
remote CI, commit, push or change to the real Git index.
