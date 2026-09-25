# Finite wave splitting: derivative energy and zero-order stability

## Placement and scope

This continues the [explicit construction](2026-09-22-wave-splitting-construction.md) and the
[wave approximation route](2026-09-22-heat-test-wave-approximation.md). The new integration
extension is [WaveSplitting/Energy.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Energy.lean),
in the existing `FunctionalInequalities.Analysis.WaveSplitting` namespace. The explicit-flow
module is unchanged. This is a basic/extension pair, with dependency direction from energy
estimates to the explicit construction; there is no module move or public-name migration.
The library root imports the extension. The placement plan was recorded before editing in
`HANDOFF.md`. Incoming hashes and both Git diffs are saved in
`build/audit/heat-test-splitting-energy/baseline/`.

## Formalized in Lean

For a finite index type and directions `a`, the new functional is

```text
D_v f(x) = (iteratedFDeriv R n f x)(v),   v : Fin n -> E,
E_0(Y) = integral u^2 dm + integral v^2 dm + sum_j integral p_j^2 dm,
E_k^a(Y) = sum_{n=0}^k sum_{w : Fin n -> iota} E_0(D_(a o w) Y).
```

These are sums of squared **scalar** derivatives. No multilinear operator norm or Pi maximum
norm is treated as a Hilbert norm. The ordered tuples count mixed derivatives with multiplicity;
this record does not assert equality with the unordered-multi-index convention in the exploration.
Directions need not span or be orthonormal for preservation, so the API calls these energies and
does not claim they are norms for arbitrary direction families. No Sobolev completion is created.

The new proofs establish:

- Continuity and compact support of each scalar evaluated iterated derivative; the exact
  commutation of every such derivative with the actual coordinate transport flow.
- Integrability of the squares used in the proof. Haar translation invariance and the scalar
  parallelogram identity give energy preservation for the actual active pair, the whole state,
  every finite derivative energy, and any finite coordinate sweep, at every real time.
- The degree-zero derivative energy equals the original three-component energy. Compact support
  is preserved by coordinate sweeps, reaction and finite iteration.
- The actual reaction formula satisfies, for `0 <= t <= 1`,

```text
u_new^2 + v_new^2 <= (1+t)(u^2+v^2) + 4t (b dot p)^2.
```

  This is proved using the sine/cosine formulas and a quadratic perturbation estimate, then
  integrated with all integrability obligations discharged.
- If the smooth coefficient obeys the explicit bound `sum_j b_j(x)^2 <= B`, `B >= 0`, then

```text
E_0(R(t)Y) <= (1+(1+4B)t) E_0(Y),
E_0(S(t)Y) <= (1+(1+4B)t) E_0(Y),
E_0(S(delta)^k Y) <= (1+(1+4B)delta)^k E_0(Y)
                 <= exp((1+4B) k delta) E_0(Y),   0 <= delta <= 1.
```

  These are actual estimates for the explicit formulas and iteration, not assumed stability
  fields. The fixed-horizon client instantiates `delta=L/N`, `N>0`, `delta<=1`, and the initial
  state `(0,h,0)`, obtaining `E_0(Y_N) <= exp((1+4B)L) integral h^2 dm` for arbitrary compact
  smooth `h`. It imposes no sign restriction on `h`.

The measure hypotheses are finite measure on compact sets and right-translation invariance;
a Haar measure satisfies the relevant hypotheses. Reaction estimates alone do not require
translation invariance. No probability normalization or log-concavity is used here.

## Exact remaining gap

The coefficient bound is an explicit hypothesis of these generic stability estimates. A compact
coefficient equal to the original gradient on the common support has **not** yet been constructed
in Lean. Nothing here asserts global bounds on derivatives of the original potential or adds a
coefficient bound to the final heat-test frontend.

Coordinate transport is now controlled at every finite derivative order. **Reaction and full
split stability are proved only at order zero.** Next prove the higher-order product/Leibniz
bound for the actual coefficient pairing in the ordered-coordinate energy, then the higher-order
reaction stability estimate. The comparison with other finite derivative-norm conventions also
requires an explicit proof if used.

Still unproved: the fifth-order split stability needed by the route, the third-order `C*delta`
residual estimate with two derivative losses, weighted forced energy and the gradient compatibility
defect, the residual-controlled finite time average and its error bound, form-range approximation,
two-field convergence and the arbitrary-data heat-test frontend. In particular, the exponential
unweighted zero-order bound cannot replace the horizon-independent leading term in the later
weighted energy argument. The exploration's minimum substantive approximation target remains open.
Buser, KLS, route completion markers and certificate count are unchanged.

## Verification

[WaveSplittingEnergyAudit.lean](../audits/WaveSplittingEnergyAudit.lean) independently instantiates
all finite derivative orders, a complete coordinate sweep, arbitrary compact smooth initial data
at a fixed horizon, time zero and empty coordinates. The new strict source and client checks and
full library build are saved under `build/audit/heat-test-splitting-energy/`.
The final `final-snapshot.json` there records the actual project-verifier outcome, exact source
snapshot and report path. Read that receipt for its result; earlier receipts certify earlier
snapshots. Pinned dependency artifacts are trusted. No remote CI, commit or push is performed.
