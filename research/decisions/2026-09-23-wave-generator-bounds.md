# Finite wave splitting: energy bounds for the actual generators

## Placement and scope

[GeneratorBounds.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/GeneratorBounds.lean)
combines the actual generators from Consistency with the ordered-coordinate energy and product
estimates from Stability. It does not import Localization or application-layer heat results.
The placement plan was recorded before editing in `HANDOFF.md`; baseline hashes and Git diffs
are in `build/audit/heat-test-generator-bounds/baseline/`. The root imports GeneratorBounds and
Localization. Earlier source modules and incoming heat-semigroup changes are unchanged.

## Formalized in Lean

The finite-word append identity is proved for the actual recursive directional derivatives.
Together with the previously proved bridge to `iteratedFDeriv`, it gives a scalar coordinate
estimate without commuting mixed derivatives or identifying a multilinear operator norm with
the existing energy. Write `q_k=jetCount k` and `E_k` for that squared ordered-coordinate energy.

```text
scalarEnergy_k(partial_(a_j) f) <= q_k scalarEnergy_(k+1)(f),
E_k(Q_j Y) <= q_k E_(k+1)(Y),
E_k(Q_i Q_j Y) <= q_k q_(k+1) E_(k+2)(Y).
```

Here `Q_j` in these formulas denotes `coordinateGenerator`, not the coordinate flow. Smoothness,
compact support and all square-integrability obligations are proved for the differentiated
functions. Directions need not form a basis; no derivative-norm equivalence is assumed.

Scalar addition/subtraction energy inequalities, invariance under sign reversal and monotonicity
in the derivative order are proved. The product bound for the actual coefficient pairing is
integrated. Under the explicit bounds on the squared coefficient words through order `k`, with
`C_k=couplingConstant k B`, the actual reaction generator `R` satisfies

```text
E_k(R Y) <= (2+2 C_k) E_k(Y).
```

Thus reaction costs no derivative order. These estimates combine with a finite-list bound to
control the actual split generator `G` and its square:

```text
E_k(G Y) <= K_k E_(k+1)(Y),
E_k(G(G Y)) <= K_k K_(k+1) E_(k+2)(Y),
K_k = 2 (4^(length(js)+1) q_k + 2 + 2 C_k).
```

The square estimate requires coefficient words bounded through order `k+1`. The complete list
`List.finRange d` specializes to the intended `waveGenerator`, by the existing generator identity.

An additional common bound covers every elementary generator, encoded by `Option iota`:
`none` is reaction and `some j` is a coordinate generator. Every ordered pair is controlled by
`A_k A_(k+1) E_(k+2)(Y)`, where `A_k=q_k+2+2C_k`. This includes both mixed orders `R Q_j`
and `Q_j R`, as well as repeated reaction or coordinate generators. No commutation is assumed.
The independent client instantiates the two-order estimates at `k=3`, with fifth-order input
energy and coefficient bounds through order four.

The constants are finite and deliberately non-sharp, and may depend on dimension and list
length. The measure only needs to be finite on compact sets; these generator estimates do not
require translation invariance. Empty coordinate families are admitted for the reaction and
full-generator statements; no division by dimension is used.

## Exact remaining gap

The derivatives lost by these actual generators and their ordered pairs are now controlled.
This does **not** identify the second temporal derivative of the finite split product with
`G^2 S(t)Y`: the constituent generators do not generally commute. Next prove the all-time
chain rules for time-dependent inputs and bound the differentiated finite products, including
flow factors between generators, using the already available flow stability. Then use the
actual residual integral from Consistency to obtain

```text
E_3(residual(theta)) <= C theta^2 E_5(Y).
```

That residual estimate is still unproved. The global bounds on localized coefficients are already
constructible by Localization, but this round's generic generator estimates retain their raw
coefficient-bound hypotheses. Weighted forced energy, gradient compatibility, the finite time
average, form-range density and the arbitrary-data heat-test frontend remain open. No Buser,
dimension-free KLS, route-completion or certificate claim changes.

## Validation

[WaveSplittingGeneratorBoundsAudit.lean](../audits/WaveSplittingGeneratorBoundsAudit.lean)
independently checks the full wave generator squared from order five to three, every ordered
pair of elementary generators at those orders, coordinate bounds at arbitrary order, and empty
coordinates. Ten transitive axiom reports cover clients and principal bounds.

Strict source/client checks and the full build are logged under
`build/audit/heat-test-generator-bounds/`. Its `final-snapshot.json` records the actual final
project-verifier result, report and source snapshot. Pinned dependency artifacts are trusted;
no remote CI, commit, push or real Git-index change is performed.
