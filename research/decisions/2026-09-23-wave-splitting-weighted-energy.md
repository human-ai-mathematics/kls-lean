# Finite wave splitting: weighted forced energy and the gradient compatibility defect

## Placement and scope

This continues the [residual continuation](2026-09-23-wave-splitting-residual.md). The placement
plan was recorded in `HANDOFF.md` before editing. Two modules extend `Analysis/WaveSplitting`:

- [WeightedEnergy.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/WeightedEnergy.lean)
  imports Residual and Mathlib's Haar integration by parts, parametric differentiation and
  quadratic discriminants. It contains the Hilbert-seminorm facts for the square energies,
  the weighted skew identity, differentiation of the weighted energy along a curve, and
  forced energy on actual steps, nodes and cells.
- [Compatibility.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Compatibility.lean)
  imports WeightedEnergy. It contains the compatibility defect, its exact evolution, its
  mesh-uniform bounds, and the combined weighted form-energy client.

They are separate modules because the defect is a separate object with its own derivative
count. The library root imports both. No existing file, declaration or API changed. The
baseline is `build/audit/heat-test-splitting-weighted/baseline/`.

## Formalized in Lean

Let `w` be a `C^1` weight with `w >= 0` and `D_(a_j) w = -b_j w` for every coordinate. The
potential weight `w = exp(-U)` with `b_j = D_(a_j) U` satisfies this relation. The weighted
energy is `W(Y) = ∫ w (u^2 + v^2 + Σ_j p_j^2) dm`; `weightedPairing` is the associated bilinear
form. The measure is an additive Haar measure on a finite-dimensional space. `W` is not
normalized by `∫ exp(-U)`, and it is not identified with an `L²(ν)` norm.

**Seminorm facts.** Cauchy–Schwarz and Minkowski are proved for `W`, from a nonnegative
quadratic polynomial and its discriminant. Minkowski is also proved for the ordered-coordinate
derivative energy `E_k` (`derivativeEnergy_addState_le_sq`): every ordered derivative is
reduced to the unit-weight case, and the resulting finite sums use the finite-sum Minkowski
lemma. Thus `sqrt E_k` is a seminorm on supported smooth states.

**Skew identity.** `weightedPairing_waveGenerator` proves `⟨Y, waveGenerator a b Y⟩_w = 0`
for every supported smooth `Y`. Pointwise, the weighted integrand equals
`Σ_j D_(a_j)(w v p_j)`, and each such term integrates to zero by Haar integration by parts.
The identity holds without `p = grad u`.

**Forced energy.** `hasDerivAt_weightedEnergy` differentiates `W` along a jointly smooth curve
that is supported in one ball near the time point. The dominating bound is obtained on the
compact product of a time ball and the support ball. The derivative of the actual step is the
split generator plus the actual residual. With the skew identity and Cauchy–Schwarz this gives
`d/ds W ≤ 2 sqrt(W) sqrt(W(e))`. A regularized square-root argument turns this into

```text
sqrt W(step θ Y) <= sqrt W(Y) + θ η   when W(residual Y s) <= η^2 on [0,θ].
```

This is iterated over the actual nodes and cells. `exists_weightedEnergy_cell_bound` combines
it with the order-zero case of the localized residual theorem and a bound for `w` on the
propagation ball. For every smooth coefficient without global bounds and every smooth
supported initial state, it gives one `C >= 0` with

```text
sqrt W(cell_k(θ)) <= sqrt W(Y) + C δ,
0 <= θ <= δ <= 1,  k < N,  N δ <= L.
```

The leading term `sqrt W(Y)` has coefficient one and does not depend on the horizon. Only the
remainder does.

**Compatibility defect.** `compatibilityDefect a Y = (0, 0, p_j - D_(a_j) u)`. The wave
generator has zero defect. `compatibilityDefect_timeDerivative_step` proves that the time
derivative of the defect along the actual step equals the defect of the actual residual,
`e_(p_j) - D_(a_j) e_u`. That derivative costs one order:
`E_k(d(e)) <= defectConstant k · E_(k+1)(e)`, with `defectConstant k = 2 + 2 |ι| jetCount k`.

The previous time-integral lemma is applied to `d(step s Y) - d(Y)`. Combined with Minkowski
for `E_k`, it gives `sqrt E_k(d(step θ Y)) <= sqrt E_k(d(Y)) + θ sqrt(defectConstant · M)`
when `E_(k+1)(e) <= M` on `[0,θ]`. The bound is iterated over nodes and cells.
`exists_defect_cell_bound` uses the order-`k+1` localized residual theorem to give

```text
sqrt E_k(d(cell_k(θ))) <= sqrt E_k(d(Y)) + C δ
```

on the same mesh range. This is the `E_2` defect bound `|d|_2 <= C L η` of the route, from
the proved `E_3` residual bound.

**Form energy.** `formState a Y = (u, 0, D_(a_j) u) = (u,0,p) - d(Y)`.
`exists_formEnergy_cell_bound` proves

```text
sqrt(∫ w (u^2 + Σ_j (D_(a_j) u)^2))(cell_k(θ)) <= sqrt W(Y) + C (sqrt E_0(d(Y)) + δ).
```

For orthonormal directions the left side is the weighted form norm of `u`; that
identification is not asserted.

## Clients

[WaveSplittingWeightedEnergyAudit.lean](../audits/WaveSplittingWeightedEnergyAudit.lean) uses
`w = exp(-U)` and `b_j = D_(a_j) U` for an arbitrary smooth potential. It proves the weight
relation and that initial data `(0,h,0)` are compatible. It instantiates:

- skewness for the potential weight;
- `sqrt W(cell) <= sqrt(∫ exp(-U) h^2) + C δ`;
- `sqrt E_2(d(cell)) <= C δ`;
- `sqrt(weighted form energy of u) <= sqrt(∫ exp(-U) h^2) + C δ`;
- no weighted-energy growth in dimension zero, where the residual vanishes;
- the zero-time defect step;
- Minkowski for `E_k`.

Eighteen transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

## Remaining obligations

Still open are the finite time average `q = ∫_0^L (1-t/L) u_δ(t) dt`, its smoothness, the exact
identity for `J_cl q - h`, and the resulting error bound
`||J[q] - [h]||_E <= ||h||/L + C δ`. Also open are the identification of `W` and the
coordinate form energy with the `L²(ν)` and form norms of the tilted law, form-range density,
two-field convergence and the arbitrary-data heat-test frontend. No Buser, dimension-free KLS,
route-completion or certificate claim changes.

## Verification

Strict source/client checks, the full build and the project verifier are logged under
`build/audit/heat-test-splitting-weighted/`. Its `final-snapshot.json` records the actual final
verifier outcome, report and source snapshot. Pinned dependency artifacts are trusted. There is
no remote CI, commit, push or real Git-index change.
