# Finite wave splitting: tame bound for the actual split residual

## Placement and scope

This continues the [generator bounds](2026-09-23-wave-generator-bounds.md). The placement plan
was recorded in `HANDOFF.md` before editing. Two modules extend the existing
`Analysis/WaveSplitting` family:

- [FlowDerivative.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/FlowDerivative.lean)
  imports Consistency and Mathlib's symmetric second derivatives. It contains calculus only:
  all-time chain rules, the ordered sweep derivative, time/space derivative exchange and the
  exact residual identity.
- [Residual.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Residual.lean)
  imports FlowDerivative, GeneratorBounds, Localization and Mathlib's product integrals. It
  contains the energy estimates and the localized grid-cell client.

They are separate modules because the calculus layer needs no measure theory. The library
root imports both. No existing file, declaration, namespace or public API changed. Earlier
source modules and the incoming heat-semigroup changes are untouched. The baseline hashes and
Git diffs are in `build/audit/heat-test-splitting-residual/baseline/`.

## Formalized in Lean

Write `S(t)Y = step a b js t Y`, and let `e_Y(t) = residual a b js Y t` be the residual
defined in Consistency. `E_k` is the existing `derivativeEnergy`: the sum of the squared
integrals of the ordered scalar directional derivatives. It is not a square root, and it is
not identified with any other derivative norm. `T_j`, `R` and `Q_j` are the actual transport
flow, reaction flow and coordinate generator. `G_js` is the actual list generator
`sweepGenerator`, and `R'` is `reactionGenerator`.

**Calculus layer.** Transport and reaction are one-parameter groups, and they act linearly on
states. For a jointly smooth input curve `Z` with temporal derivative `Z'` at any time `t`,

```text
d/dt T_j(t)Z(t) = T_j(t)Z'(t) + Q_j T_j(t)Z(t),
d/dt R(t)Z(t)   = R(t)Z'(t)   + R' R(t)Z(t),
d/dt Sweep(t)Z(t) = Sweep(t)Z'(t) + sweepDerivative(t)Z(t).
```

Here `sweepDerivative(t, j::l, Y) = Sweep_l(t) Q_j T_j(t) Y + sweepDerivative(t, l, T_j(t) Y)`.
Every summand keeps all later flow factors after its generator, in the list order. The
arbitrary-time rules come from the group laws and the existing time-zero rules. For jointly
smooth `F : R x E -> R`, symmetry of the second Fréchet derivative lets the time derivative
commute with every spatial directional derivative. The same holds for every ordered word of
directional derivatives, and for `Q_j` and `G_js` applied along jointly smooth curves.
Therefore

```text
e_Y(t) = R(t) sweepDerivative(t,js,Y) - G_js(S(t)Y).
```

The reaction generator cancels exactly. Neither side is replaced by `G^2 S(t)Y`.

**Time-integral lemma.** `derivativeEnergy_le_of_timeDerivative` assumes that `g` is jointly
smooth, starts at the zero state, and stays in one fixed ball on `[0,t]`. It proves

```text
E_k(g(t)) <= t^2 sup_{s in [0,t]} E_k(dg/ds (s)).
```

For each ordered word, the proof uses the fundamental theorem of calculus at every spatial
point and Cauchy–Schwarz in time. It then applies Fubini on the product of `(0,t]` and the
compact support ball, which is a finite measure for any measure finite on compacts. The time
derivative is clamped to `[0,t]`. At the endpoints, one-sided uniqueness of derivatives shows
that the temporal derivatives vanish outside the ball. All integrability and exchange
obligations are proved.

**Commutators.** Let `Y` be smooth and compactly supported and let `0 <= t <= 1`. Write
`q_k = jetCount k`, `C_k = couplingConstant k B` and `n = length js`. Assume that the squared
coefficient words have bound `B` through order `k+1`. Then

```text
E_k(sweepDerivative(t,js,Y)) <= 4^n q_k E_(k+1)(Y),
E_k(Sweep(t)Q_j X - Q_j Sweep(t)X) <= t^2 4^(n+1) q_k q_(k+1) E_(k+2)(X),
E_k(sweepDerivative(t,js,Y) - G_js Sweep(t)Y) <= t^2 n 4^(n+1) q_k q_(k+1) E_(k+2)(Y),
E_k(R(t)G_js W - G_js R(t)W) <= t^2 reactionCommutatorConstant(js,k,B) E_(k+1)(W).
```

Each commutator is controlled by the time-integral lemma. Its time derivative contains the
actual flow factors and generators in their true order. That derivative is bounded by the
existing transport energy preservation, reaction stability and generator bounds. The sweep
residual telescopes along the actual list. The reaction commutator is not zero, because of
the rotation and the coefficient pairing.

**Residual theorem.** `derivativeEnergy_residual_le` proves, for `0 <= t <= 1`,

```text
E_k(e_Y(t)) <= residualConstant(js,k,B) t^2 E_(k+2)(Y),
residualConstant = 2((2 + 4 C_k) n 4^(n+1) q_k q_(k+1) + reactionCommutatorConstant).
```

It applies to every smooth compactly supported state `Y`. The constant depends only on the
number of coordinates through `jetCount` and `couplingConstant`, on the split list `js`, on
`k`, and on the explicit coefficient bound `B` through order `k+1`. It does not depend on `Y`,
`t`, the mesh size or the step size. The measure must be Borel, finite on compacts and
right-translation invariant, and `E` is finite-dimensional. Empty coordinate families are
admitted. The endpoint `k = 3` bounds `E_3` by `E_5`, with coefficient words through order
four.

**Grid-cell client.** `exists_cell_residual_bound` covers any original smooth coefficient `b`,
with no global derivative bound. It also covers any smooth initial state `Y` supported in a
ball of radius `R`, any derivative order and any fixed horizon `L`. For these data it
constructs one `C >= 0` with

```text
E_order(residual a b js (nodes a b js δ Y k) θ) <= C δ^2
for all N, δ with 0 <= δ <= 1 and N δ <= L, every cell k < N and every 0 <= θ <= δ.
```

The residual is that of the actual step started at the computed node, i.e. of the actual
cell `θ ↦ cell a b js δ Y k θ`. The proof chooses one localized coefficient, which agrees with `b`
on the ball of radius `R + (L+2) travel`, before any mesh parameter is chosen. The residual
depends on steps in a time neighbourhood, because the temporal derivative is local, so
agreement is proved for `|s| <= |θ| + 1`. The grid equality comes from the existing
localization theorem. Stability through order `order+2` and the residual theorem then give
`C = residualConstant · exp((1 + 4C') L) · E_(order+2)(Y)`, where `C'` is the stability
coupling constant of the localized coefficient. `C` depends on the initial data, the horizon,
the directions, the split list and the coefficient's behaviour on the fixed ball. It does
not depend on `N`, `δ`, `k` or `θ`.

## Exact remaining obligations

The mesh-uniform residual estimate on the actual cells is proved in the existing squared
energies. Weighted forced energy, the gradient compatibility defect `p - grad u`, the
residual-controlled finite time average, form-range density and the arbitrary-data
heat-test frontend remain open. They were not attempted in this round. The unweighted
exponential stability factor is still not a horizon-independent leading term. No Buser,
dimension-free KLS, route-completion or ledger-certificate claim changes.

## Verification

[WaveSplittingResidualAudit.lean](../audits/WaveSplittingResidualAudit.lean) independently
checks the following:

- the complete-list residual measured against `waveGenerator`;
- the order-three/order-five endpoint, with the constant fixed before the state and the time;
- the general-order bound;
- zero time, where the bound forces vanishing energy;
- dimension zero, both through the general bound and through the exact vanishing of the
  residual;
- actual grid cells for an arbitrary original smooth coefficient;
- actual grid cells for smooth potential coefficients with compactly supported initial velocity.

Twenty transitive axiom reports cover the clients and the principal new theorems. All of them
use only `propext`, `Classical.choice` and `Quot.sound`. The strict source/client checks, the
full build and the project verifier are logged under `build/audit/heat-test-splitting-residual/`.
Its `final-snapshot.json` records the actual final verifier outcome, report and source
snapshot. Pinned dependency artifacts are trusted. There is no remote CI, commit, push or
real Git-index change.
