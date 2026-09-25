# Finite wave splitting: the explicit construction layer

## Scope and placement

This implements the first layer of the [wave route](2026-09-22-heat-test-wave-approximation.md).
The owner is generic classical analysis, not the log-concave heat-semigroup interface:
[WaveSplitting.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting.lean),
namespace `FunctionalInequalities.Analysis.WaveSplitting`. The module imports only Mathlib
calculus, trigonometry, finite-dimensional compactness and support tools. The library root imports
it. Existing theorem signatures are unchanged. The placement plan was recorded in `HANDOFF.md`
before editing; the incoming source hashes, unstaged patch and index patch are saved under
`build/audit/heat-test-splitting/baseline/`.

## Formalized in Lean

- Actual displacement, velocity and coordinate-field functions; explicit reaction and
  characteristic translation formulas; finite coordinate sweeps, grid nodes and cell functions.
- The two translated characteristic identities and their pointwise squared-energy identity.
  This is not yet a Haar integral or derivative-norm isometry theorem.
- The two reaction differential equations at every time, and the velocity/active-coordinate
  derivatives of the translation flow at time zero, with the directional Fréchet derivatives.
- Spatial smoothness and joint time-space smoothness for each cell on all real times, assuming
  smooth initial components and smooth coefficients.
- Adjacent cell endpoints agree. A globally glued interpolation has not been defined.
- For any compact smooth initial velocity, all cells in a finite grid have one common compact
  spatial support. Compactness of the initial support supplies the initial radius; it is not
  an extra input to `initial_cells`.

The support bound is deliberately conservative: `R + N * δ * travel a js`, where `travel`
is the sum of the lengths of the directions in the sweep. It is uniform over grid refinement
when `N*δ=L`. With an orthonormal list it is `R+dL`; the sharper coordinate-box/`sqrt(d)L` bound
from the exploration has not been implemented. No propagation speed-one assertion is made.

The coordinate list is explicit and may be empty. The construction theorem is generic over
lists; the independent client uses `List.finRange d`, so every coordinate is swept once.
A zero-dimensional client uses `Fin 0 → ℝ` and reduces the step to the scalar sine/cosine
oscillator. Another client proves that zero initial data remain identically zero in every cell.
Neither construction assumes convexity, bounded potential derivatives, a wave existence theorem,
residual bounds or a higher-order core. The coordinate arrays are not equipped here with a
claimed Hilbert norm; a later norm layer must use sums of squares, not the Pi maximum norm.

## Remaining analytic target

The minimum substantive residual-controlled time-average target in the exploration is **not
completed**. The next implementation is the finite derivative norm and the actual translation
isometry/reaction stability estimates, followed by first-order consistency with two derivative
losses and the uniform cell residual bound. These must be proved for the explicit flows above.
They must not be inserted as hypotheses into the final frontend or packaged as assumed fields.

Still unproved: the coefficient localization, forced weighted energy and compatibility-defect
bounds, the actual finite time average and differentiation under its integral, the residual
identity and error bound, form-range approximation, two-field convergence and the arbitrary-data
heat-test frontend. The current result is a prerequisite construction, not that approximation
or a completion of Buser/KLS. No certificate or completed route marker changes.

## Validation and receipts

The independent client is [WaveSplittingAudit.lean](../audits/WaveSplittingAudit.lean).
Strict source/client compilation, the local full build, and project acceptance verification
are recorded under `build/audit/heat-test-splitting/`; the final snapshot receipt there identifies
the actual outcome and verifier report. A receipt must be read for its recorded snapshot, not
inferred from this document. Pinned dependency artifacts are trusted by the local verification;
no remote CI, commit, push or dependency upgrade is part of this change.
