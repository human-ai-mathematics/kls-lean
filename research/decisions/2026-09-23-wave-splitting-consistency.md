# Finite wave splitting: consistency and the actual residual

## Placement

[Consistency.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Consistency.lean)
extends the explicit-flow module. It imports Mathlib's parameter differentiation and interval
fundamental theorem of calculus for the actual residual's integral representation. It does not
import the energy/localization extensions or an application-layer heat theorem. The library root
imports both this independent extension and Localization. The placement plan was recorded in
`HANDOFF.md`; the saved baseline is `build/audit/heat-test-splitting-consistency/baseline/`.
Earlier wave-splitting modules and the incoming heat-semigroup work are unchanged.

## Formalized in Lean

`HasTimeDerivative` expresses the classical temporal derivative of every component. The chain
rule is proved for coordinate transport with a time-dependent input state, then for its full
finite composition, and for the reaction with a time-dependent input. The proof accounts for
both the outer flow parameter and the varying input. It does not merely add fixed-input
substep derivatives or assume first-order consistency.

`sweepGenerator` retains the actual sweep list and its multiplicities. Together with the
reaction generator it gives `splitGenerator`, and the explicit step satisfies

```text
(d/dt) S(t)Y |_(t=0) = splitGenerator(Y).
```

For the complete list `List.finRange d`, the generator is proved equal to `waveGenerator`:

```text
u'   = v,
v'   = sum_j (partial_(a_j) p_j) - u - sum_j b_j p_j,
p_j' = partial_(a_j) v.
```

Here the partial derivatives are the actual scalar `fderiv` evaluations on the given directions.
No identification `p=grad u` is imposed. The result admits arbitrary finite dimension, including
zero; the latter is the scalar oscillator `u'=v`, `v'=-u`. Arbitrary lists have their actual list
generator, so omitted or repeated coordinates are not silently treated as a complete basis.
Consistency also holds at the start of every cell, for its computed grid state.

The actual residual is defined as

```text
e_Y(t) = (d/dt) S(t)Y - splitGenerator(S(t)Y).
```

It is proved jointly smooth for smooth input and smooth coefficients, and `e_Y(0)=0` follows
from the full-step consistency theorem. The interval fundamental theorem of calculus then gives
for every component, every spatial point, and every real time

```text
e_Y(t,x) = integral_0^t (d/ds) e_Y(s,x) ds.
```

Integrability of the temporal derivative is discharged using smoothness. This is an exact
identity for the defined residual, not an existence assumption or a hypothetical error field.
The complete-coordinate specialization is the residual against the intended wave system.

## Exact remaining gap

Zero residual at the start and smoothness do **not** prove the mesh-uniform residual estimate.
The next missing statement is a tame quantitative bound, in the existing ordered-coordinate
energies, of the shape

```text
E_3(e_Y(theta)) <= C theta^2 E_5(Y),  0 <= theta <= 1,
```

under the already available localized coefficient bounds, or a sufficient uniform bound on
the time derivative in the exact integral above. Its two derivative losses must be proved for
the actual finite composition. A constant chosen separately for each grid state, or a mere
pointwise continuity argument, would not justify mesh refinement.

The [localization round](2026-09-23-wave-splitting-localization.md) already supplies the original
smooth-coefficient fixed-horizon fifth-order state bound without global derivative hypotheses.
Combining it with the missing tame residual estimate is still required. Weighted forced energy,
gradient compatibility, the finite time average, form-range density, the arbitrary-data heat-test
frontend, Buser and dimension-free KLS remain open. This round changes no route completion marker
or ledger certificate.

## Verification

[WaveSplittingConsistencyAudit.lean](../audits/WaveSplittingConsistencyAudit.lean) independently
checks the complete-coordinate system, every computed cell, residual vanishing at each cell's
start, and the zero-dimensional oscillator. Ten transitive axiom reports cover those clients
and the main chain-rule, smoothness and residual-integral results.

Strict source checks, the separate current-module client artifact view and the full build are
logged in `build/audit/heat-test-splitting-consistency/`. The `final-snapshot.json` there records
the actual final verifier outcome and exact source hash. Pinned dependency artifacts are trusted.
There is no remote CI, commit, push, or real Git-index change.
