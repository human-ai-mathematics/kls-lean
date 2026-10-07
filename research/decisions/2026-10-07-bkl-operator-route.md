# 2026-10-07 BKL Theorem 3.1 through the operator domain

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1 (PDF SHA-256 `86824722…bb0db`), Theorem 3.1
(p. 10) and its proof (Sections 2–3, pp. 5–17). Owner decision of 2026-10-07: prove the **exact
statement** of Theorem 3.1 by the operator route, keeping all of its hypotheses and a universal
final constant; first establish the weak Hessian and tensor identities on the generator domain and
justify the approximate-eigenfunction argument with controlled errors; leave Lemma 2.1 on `𝒜`
partial until temperate representatives are proved; reassess the timeline after these steps.

## Why not the source route

The source builds the iterates `h_i` in the class `𝒜` (smooth, every derivative of polynomial
growth). That needs Lemma 2.1 on `𝒜` (local elliptic regularity, a maximum-principle growth bound,
interior gradient estimates) and the existence of a first eigenfunction (compact resolvent, i.e.
Rellich compactness plus tightness). None of this exists locally or in the pinned Mathlib
(2026-08-10, which has Fourier-side `H^s` but no multiplication by smooth functions, local
bootstrapping, local Sobolev embedding or Rellich).

The proof of Theorem 3.1 uses `𝒜` only through (15), (16) and (48) applied to the iterates, and the
eigenfunction only through four quantities (below). In `L²(ν)`, `C_c^∞` is an operator core of
`A = T̄†T̄ = -ℒ` (`exists_seq_smooth_tendsto_adjointComp`), so (16) and (48) extend to `D(A)` by
graph-norm approximation, and an approximate eigenfunction exists without compactness.

## The approximate-eigenfunction argument with explicit errors

Let `λ = 1/C_P(μ)` (finite and positive: `C_P ≤ 1/a` for a regular law in positive dimension;
dimension `0` is trivial). Fix `ε = 1/10` and take `f ∈ D(A)` centered with `‖f‖₂ = 1` and
`‖Af − λf‖₂ ≤ ελ` (obligation `O2`). Set `h₁ = f` and define `h_{i+1}`, `α_{i+1}` by (30)–(31)
componentwise in `D(A)` (Lemma 2.1, operator-domain part, already proved). The source uses
`Lf = −λ₁ f` exactly in four places; each changes as follows.

1. `v₁ = ‖∇f‖² = ⟨Af, f⟩ ∈ [λ, (1+ε)λ]`: the lower bound is the Poincaré gap for centered `f`,
   the upper bound is `⟨Af, f⟩ ≤ λ + ‖Af − λf‖`.
2. `‖Lh₁‖ = ‖Af‖ ≤ (1+ε)λ`, so `Σ_i χ_i ≤ ‖Lh₁‖² ≤ (1+ε)²λ² ≤ 1.21 λ²` (summing (45)).
3. `p₁ = |∫∇f dμ|² = Σ_j ⟨Af, x_j⟩² ≤ ‖Af‖² ‖Cov μ‖_op ≤ (1+ε)²λ²` (pair `T̄f` with
   `T̄x_j = e_j`; `Af` is centered and `Cov μ ≤ Id`).
4. For `2 ≤ i ≤ N` (with `N` minimal such that `v_{N+1} < λ/2`, which exists because `v₁ ≥ λ`
   and `v_N → 0` by Corollary 3.5), `α_i² = ‖Lh_i‖²/v_i ≤ (1+ε)²λ²/(λ/2) ≤ 2.42 λ ≤ 3λ`
   instead of `2λ` in (54).

Lemmas 3.2–3.4 and Corollary 3.5 do not use the eigen-equation. With (4), the operator
`α_j ∇₀(−L)⁻¹` has norm at most `√3` in (42)–(43), so (41) holds with `q⁴ 3^q (4/3)/λ` in place
of `q⁴ 2^q/λ`, again of the form `C^q/λ`. Lemma 3.8 holds with `(3λ)^d` in (57), hence with a
larger universal `C`. Lemma 3.9 becomes `Σ_{i≤N} p_i ≤ (1+ε)²λ² + 3λ S₁`.

In the final argument, `Σ_{i≤N} p_i = v₁ − v_{N+1} > λ − λ/2 = λ/2` still holds by (36). The
bound (63) reads `S_d ≤ (Cλ)^d S_{2d} + (2d−1)λR^{2d} + 2d·C^d R^{2d}·1.21λ ≤ (Cλ)^d S_{2d} +
5d C^d λ R^{2d}`. Under the contradiction hypothesis `λR² ≤ 1/(100C²)`:
`(Cλ)^{d−1} S_d ≤ (Cλ)^{2d−1} S_{2d} + 5d/100^d`, so `S₁ ≤ 5 Σ_{d≥1} d/100^d < 0.052`, and with
`λ ≤ 1/100`, `Σ p_i ≤ 1.21λ² + 3λ S₁ < λ (0.0121 + 0.156) < λ/2`, a contradiction. Hence
`C_P(μ) ≤ 100 C² R²` with the enlarged universal `C`. The statement of Theorem 3.1 is unchanged;
only the value of its universal constant differs from the source's proof.

## Step 1 obligations and placement

The obligations are the `#check` propositions of
[`research/audits/BKLOperatorRouteStatements.lean`](../audits/BKLOperatorRouteStatements.lean).

```text
O1  Object and role:   approximate eigenvectors of A = T†T at the bottom λ of A on (ker T)ᗮ;
                       generic tool for closed densely defined T between real Hilbert spaces.
    Scope:             explicit errors √(η/8), λ√(η/2); no compactness, no spectral theorem.
    Destination:       Analysis/Semigroup/Generated/ApproximateEigenvector.lean (create),
                       namespace Analysis.Semigroup.Generated; imports Generated/Inverse,
                       Resolvent/Form, VonNeumann.
O2  Object and role:   heat-model specialization at λ = 1/C_P.
    Destination:       KLS/LogConcave/HeatSemigroup/ApproximateEigenfunction.lean (create);
                       imports O1, HeatSemigroup/Inverse, HeatSemigroup/Curvature.
O3  Object and role:   weak Hessian of F ∈ D(A) and the curvature form of (16) on D(A).
    Destination:       KLS/LogConcave/HeatSemigroup/Hessian.lean (create); imports
                       HeatSemigroup/InteriorRegularity (operator core), Bochner/Temperate.
O4–O5 Object and role: tilt identity (48) and Lemma 3.6 on D(A).
    Destination:       KLS/LogConcave/HeatSemigroup/Tilt.lean (create); imports
                       HeatSemigroup/InteriorRegularity, Tilt/SquareIntegrable.
Extend/split/create: create; each is a new property of an existing object with its own
                     dependency set (spectral, second-order, tilt), none fits an existing module.
Public API changes:  additions only.
Validation:          strict compilation, an audit client restating O1–O5 verbatim with axiom
                     reports, full lake build and research/verify.py.
```

## Non-claims

No iterate is constructed and Theorem 3.1 is not stated or proved in this step. Lemma 2.1 on `𝒜`
and the eigenfunction facts (19) stay `◐`; the lemmas proved through `D(A)` will be marked `⇑`
(different proof route) only once their statements are reviewed against the source.

## Step 1 results (2026-10-07)

All five obligations are proved with standard axioms only; each audit client restates its route
propositions verbatim.

| Obligation | Declarations | Module | Audit client |
| --- | --- | --- | --- |
| `O1` | `Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap` | `Analysis/Semigroup/Generated/ApproximateEigenvector.lean` | `BKLApproximateEigenfunctionAudit.lean` |
| `O2` | `KLS.LogConcave.exists_centered_approx_eigenfunction` | `KLS/LogConcave/HeatSemigroup/ApproximateEigenfunction.lean` | same |
| `O3` | `compLp_innerSL_mem_closedWeightedOperator_domain`, `compLp_innerSL_closedWeightedOperator_comm`, `sum_norm_sq_closedWeightedOperator_add_le` | `KLS/LogConcave/HeatSemigroup/Hessian.lean` | `BKLWeakHessianAudit.lean` |
| `O4`, `O5` | `tiltAverage_adjointComp_eq`, `taylorTensor_adjointComp_eq` | `KLS/LogConcave/HeatSemigroup/Tilt.lean` | `BKLGeneratorTiltAudit.lean` |

Integration moved the generic helpers to their owners: `tendsto_apply_of_tendsto_adjointComp`
to `Analysis/Semigroup/VonNeumann.lean`, the tilt averages of `L²` classes to
`Analysis/BakryEmery/Tilt/SquareIntegrable.lean` (namespace `Analysis.BakryEmery`), and
`convexOn_of_eq_tilted` (a log-concave law `m.tilted (-U)` with continuous `U` has convex `U`) to
`KLS/LogConcave/Density/Tilted.lean`. Notes: the `O1` library theorem omits the unused premise
`0 ≤ η`; the membership part of `O3` needs no curvature hypothesis because convexity of `U` is
derived from log-concavity; the identity form of (16) on `D(A)` is not stated. Blueprint nodes
`lem:bkl-approximate-eigenfunction` and `lem:bkl-generator-domain` register the results; Lemma
3.6, (48) and (16) keep the relation `⇑`, and Theorem 3.1 stays `○`.

## Reassessed timeline (after step 1)

Step 1 took one working session with three parallel provers. The remaining work to the exact
statement of Theorem 3.1, in dependency order:

1. **Iterates in `D(A)`.** Families of components indexed by `Fin k → Fin n`, the centered
   gradient `∇₀`, the componentwise inverse, `α_i`, `v_i`, `p_i`, `χ_i`, the recursive
   construction from the approximate eigenfunction; (33), (35)–(36), Lemmas 3.2, 3.4 and
   Corollary 3.5 restated for them (the `𝒜` versions exist; the `D(A)` versions use `O3`).
2. **Lemma 3.3 for every `q`** (transpositions, (42), telescoping) and **Corollary 3.7 on `D(A)`**
   (from `O5`). These are independent of each other and can run in parallel.
3. **Lemma 3.8** through coefficient arrays and the proved Lemma 2.2.
4. **Lemma 3.9 and the final summation** with the constants of this record, then the
   **statement of Theorem 3.1** for a centered regular law with `Cov ≤ Id` and hypothesis (29)
   in the Hilbert–Schmidt norm, through the `RegularPotential` adapter.

Estimate: about four to six further sessions of the same size, so roughly one week of elapsed
time to Theorem 3.1, which is within the original one-to-two-week estimate. The largest risk is
item 1 (dependent index types for the recursion). Theorem 1.1 still needs Theorem 4.1 (Eldan
localization), Proposition 7.1 and the regular approximation, and those estimates are unchanged.
