# Finite wave splitting: the finite time average and the exact `J q - h` identity

## Placement and scope

This continues the [weighted-energy continuation](2026-09-23-wave-splitting-weighted-energy.md).
The placement plan was recorded in `HANDOFF.md` before editing.
[TimeAverage.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/TimeAverage.lean)
imports Compatibility, because the defect enters the identity. It also imports Mathlib's
parametric interval differentiation, finite-dimensional smoothness characterization and
interval integration by parts. The library root imports it. No existing file, declaration or
API changed. The baseline is `build/audit/heat-test-splitting-average/baseline/`.

The generic parametric-integral results are placed in this module. Pinned Mathlib has no
smoothness theorem for interval integrals of jointly smooth functions, and this module is
their only consumer.

## Formalized in Lean

**Parametric interval integrals.** Let `F : ℝ × E → ℝ` be jointly smooth, with `E`
finite-dimensional. Then `y ↦ ∫_c₀^c₁ F(θ,y) dθ` is differentiable, and every directional
derivative is the integral of the slice derivatives (`hasFDerivAt_intervalIntegral_slice`,
`fderiv_intervalIntegral_slice`). The dominating bound comes from compactness of
`[c₀,c₁] × closedBall(x,1)`. The integral is also `C^∞` (`contDiff_intervalIntegral_slice`).
The proof is an induction through directional derivatives, via `contDiff_succ_iff_fderiv_apply`;
all derivatives stay scalar-valued, so the induction has no universe issue.

**Operator and divergence.** The classical operator is
`formOperator a b f = f - Σ_j (D_(a_j) D_(a_j) f - b_j D_(a_j) f)`. For orthonormal directions
and `b = grad U` it is `J_cl = I - Δ + ⟨grad U, grad ·⟩`; that identification is not
asserted. `weightedDivergence a b P = Σ_j (D_(a_j) P_j - b_j P_j)`. The operator is additive
over finite sums of smooth functions and commutes with the parametric time integral. The
velocity of the actual generator splits exactly:
`(waveGenerator Y).v = -J_cl u + div_b (p - D u)` (`waveGenerator_v_eq`).

**The time average.** The average is defined cell by cell, with horizon `L = N δ`:

```text
timeAverage a b js δ Y N = Σ_(k<N) ∫_0^δ (1 - (kδ+θ)/(Nδ)) u(cell_k(θ)) dθ.
```

It is `C^∞` for smooth `Y` (`contDiff_timeAverage`). It vanishes outside the common support ball
of the cells, so it has compact support for supported `Y` (`hasCompactSupport_timeAverage`). No
smoothness across grid nodes is used.

**Exact identity.** Let `L = N δ ≠ 0`. Let `e_k` be the actual residual of the step started at
node `k`, and `d = p - D u` the actual compatibility defect of the cell. Then
`formOperator_timeAverage` proves, at every point:

```text
J_cl q - v(0) = (u(0) - u_N)/L + (1/L) Σ_k ∫_0^δ e_(k,u)
              + Σ_k ∫_0^δ (1 - (kδ+θ)/L) (div_b d(cell_k(θ)) + e_(k,v)).
```

Its proof takes these steps:

- commute `J_cl` with the time integral;
- rewrite the integrand through the split of `v'`;
- integrate the velocity derivative by parts in time on each cell;
- replace `∫ v` by `[u] - ∫ e_u` with the fundamental theorem of calculus;
- telescope the endpoint values over the actual nodes. The final velocity term carries the
  factor `1 - L/L = 0`.

For initial data `(0,h,0)` this is

```text
J_cl q - h = -u(L)/L + (1/L) Σ ∫ e_u + Σ ∫ (1 - t/L)(div_b d + e_v).
```

This is the route's identity. The only changes are that the time integrals are cellwise sums
and that the actual residual and defect appear explicitly.

## Clients

[WaveSplittingTimeAverageAudit.lean](../audits/WaveSplittingTimeAverageAudit.lean) checks:

- `q` is `C_c^∞` for compact smooth `h`;
- the `J_cl q - h` identity for `(0,h,0)`;
- the exact generator split;
- the single-cell case `N = 1`;
- dimension zero, where `J_cl` is the identity, the residual vanishes and there is no defect,
  so the identity is `q - v(0) = (u(0) - u(L))/L`.

Twelve transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

## Remaining obligations

Two identifications are still needed:

- `J_cl` on `C_c^∞` with the class-level `I + A` of the tilted law, via the existing generator
  identification for orthonormal directions and `b = grad U`;
- the square energies with the `L²(ν)` and form norms.

The quantitative consequence `||J[q] - [h]||_E <= ||h||/L + C δ` is also unproved. It needs
`E`-norm bounds for the three remainder terms: from the weighted form bound, the defect bound
with one coefficient derivative, and Minkowski for time integrals. Form-range density,
two-field convergence and the arbitrary-data heat-test frontend remain open. No Buser,
dimension-free KLS, route-completion or certificate claim changes.

## Verification

Strict source/client checks, the full build and the project verifier are logged under
`build/audit/heat-test-splitting-average/`. Its `final-snapshot.json` records the actual final
verifier outcome, report and source snapshot. Pinned dependency artifacts are trusted. There is
no remote CI, commit, push or real Git-index change.
