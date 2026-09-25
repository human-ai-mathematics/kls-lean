# Finite wave splitting: quantitative error of the time average

## Placement and scope

This continues the [time-average continuation](2026-09-23-wave-splitting-time-average.md). The
placement plan was recorded in `HANDOFF.md` before editing.
[AverageError.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/AverageError.lean)
imports TimeAverage, and the library root imports it. No existing file, declaration or API
changed. The baseline is `build/audit/heat-test-splitting-average-error/baseline/`.

## Formalized in Lean

The measure is an additive Haar measure on a finite-dimensional space. The weight `w` is
`C^1`, nonnegative, and satisfies `D_(a_j) w = -b_j w`. The coefficient `b` is smooth and has
no global bound. The weighted coordinate form energy is

```text
FE_w(f) = ∫ w (f^2 + Σ_j (D_(a_j) f)^2)    (weightedFormEnergy).
```

For orthonormal directions it is the unnormalized weighted form energy of `f`; that
identification is not asserted.

**Tools.**

- `contDiff_primitive_slice`: time primitives of jointly smooth functions are jointly
  smooth, via `∫_0^s g = s ∫_0^1 g(sτ)`.
- `scalarEnergy_intervalIntegral_le`: `E_k(∫_0^δ g) <= δ^2 sup_[0,δ] E_k(g(θ))` for functions
  supported in one ball. It is proved by applying the earlier Fubini time lemma to the
  primitive curve.
- Minkowski's inequality for scalar derivative energies, including finite sums, and for
  `FE_w`.
- `FE_w <= sup_T w · (1 + d) · E_1` on a support ball.
- `scalarEnergy_weightedDivergence_le`: `E_1(div_b d) <= generatorConstant · E_2(d)`. Here
  `div_b d` is identified with the velocity of the wave generator applied to the defect. The
  coefficient is replaced by a localized one that agrees on the support ball.

**Error theorem.** `exists_timeAverage_error_bound` covers compactly supported smooth `h` and
`L > 0`. It gives one `C >= 0` such that for all meshes with `0 < δ <= 1` and `N δ = L`:

```text
sqrt FE_w(J_cl q - h) <= sqrt(∫ w h^2)/L + C δ,
```

where `q = timeAverage a b (finRange d) δ (0,h,0) N` is the actual cellwise average. Each term
of the exact identity is estimated as follows:

- `u(L)/L`: through the forced weighted form bound. The leading coefficient is exactly `1/L`.
- `(1/L) Σ ∫ e_u`: through the time-integral lemma and the order-one mesh-uniform residual
  bound. The result is `sqrt(C_1) δ`.
- `Σ ∫ (1-t/L)(div_b d + e_v)`: through `0 <= 1-t/L <= 1`, the divergence bound with the
  order-two defect bound and the residual bound. The result is `L (sqrt G C_D + sqrt C_1) δ`.

The explicit constant is `C = C_F/L + sqrt((1+d) M_w) (sqrt C_1 + L (sqrt G C_D + sqrt C_1))`.
It depends on `h`, `L`, the directions, the coefficient near the propagation ball and the
weight bound there. It does not depend on `N` or `δ`.

## Clients

[WaveSplittingAverageErrorAudit.lean](../audits/WaveSplittingAverageErrorAudit.lean) takes
`w = exp(-U)` and `b_j = D_(a_j) U` for an arbitrary smooth potential. It proves:

- the mesh-uniform error bound;
- the classical approximation statement: for every `ε > 0` there is an actual `q ∈ C_c^∞`
  with `sqrt FE_w(J_cl q - h) < ε`. The horizon is chosen first and the mesh second;
- the dimension-zero case.

Ten transitive axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

## Remaining obligations

The classical approximation must still be identified with the class-level statement for the
tilted law ν. Three identifications are needed:

- `FE_w` with the form norm `||·||_E` in `L²(ν)`: the constant factor `1/Z`, orthonormal
  directions.
- `J_cl` on `C_c^∞` with `I + A`: the existing generator identification for
  `b = grad U`.
- Density of `[C_c^∞]` in the form domain, to pass from `h ∈ C_c^∞` to arbitrary form-domain
  targets.

Two-field convergence and the arbitrary-data heat-test frontend remain open. No Buser,
dimension-free KLS, route-completion or certificate claim changes.

## Verification

Strict source/client checks, the full build and the project verifier are logged under
`build/audit/heat-test-splitting-average-error/`. Its `final-snapshot.json` records the actual
final verifier outcome, report and source snapshot. Pinned dependency artifacts are trusted.
There is no remote CI, commit, push or real Git-index change.
