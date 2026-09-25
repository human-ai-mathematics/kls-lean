# Finite wave splitting: localization of the original smooth coefficient

## Placement and scope

This continues [finite-order stability](2026-09-23-wave-splitting-stability.md).
The placement plan was recorded before editing in `HANDOFF.md`.
[Localization.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Localization.lean)
is a substantive extension of the existing wave-splitting family, importing Stability and
Mathlib's finite-dimensional smooth bumps. The root imports this extension. The old explicit
flow, Energy, Product and Stability modules are unchanged. No declaration migration is involved.
The baseline hashes and Git diffs are in `build/audit/heat-test-splitting-localization/baseline/`.

## Formalized in Lean

For every smooth finite coefficient family `b` on a finite-dimensional real normed space and
every real radius `R`, a single smooth compactly supported family `c` is constructed with
`c_j(x)=b_j(x)` for `norm(x)<=R`. Specifically, multiply by a smooth bump with inner radius
`max(R,0)+1` and outer radius `max(R,0)+2`.

For that same `c`, every finite order and every finite direction family admit a nonnegative
bound on the squares of all ordered directional derivatives up to that order. This follows
from continuity and compact support of the actual evaluated iterated derivatives, followed
by finite sums of scalar bounds. It is proved, not supplied as an assumption. Zero-dimensional
spaces and empty coordinate families are admitted.

Localization preserves the actual finite construction, not merely a formal differential
expression: reaction on a supported state only sees coefficients in its support ball. This
implies equality of complete steps, every grid node through `N`, and every point of each cell
whenever the propagated support remains inside the agreement ball. The node/cell statements
also allow signed step parameters with the corresponding absolute-value support bounds.
No identification `p=grad u` is used.

Combining these facts with the existing finite-order stability proves
`exists_cell_energy_bound`. For smooth original `b`, smooth initial `Y` supported in a ball,
every finite derivative order `k` and fixed horizon `L`, there exists `C>=0` such that

```text
E_k(cell_j(theta)) <= exp(C L) E_k(Y)
```

for all finite meshes with `0<=delta<=1`, `N delta<=L`, `j<N`, and `0<=theta<=delta`.
The constant is chosen before the mesh parameters. There is **no global bound assumption on
the original coefficient or its derivatives**. A single cutoff at radius `R+L*travel` and a
single derivative bound for that cutoff work across all these meshes. Constants can depend
on the fixed horizon, directions, order and local coefficient behavior; no uniform-in-horizon
bound is claimed. This is the existing ordered-coordinate square energy, without a change of
norm convention or an operator-norm identification.

The independent potential client uses `b_j(x)=fderiv U x (a_j)` for arbitrary globally smooth
`U` and initial `(0,h,0)` for arbitrary compact smooth `h`, at order five. It assumes neither
convexity nor global derivative bounds. For orthonormal coordinate directions these are the
usual gradient coefficients; the client itself states the directional-derivative formula and
does not assert an additional generator identification.

## Remaining obligations

The global coefficient-boundedness hypothesis has now been removed from fixed-horizon
stability for the original smooth coefficient. The next obligation is still the actual
third-order split residual estimate with two derivative losses. It was not proved in this round.
Weighted forced energy, the gradient compatibility defect, the residual-controlled finite time
average and form-range density remain open. The unweighted exponential bound cannot replace
the horizon-independent leading term needed for time averaging. No arbitrary-data heat-test
frontend, Buser bound or dimension-free KLS theorem is claimed.

## Verification

[WaveSplittingLocalizationAudit.lean](../audits/WaveSplittingLocalizationAudit.lean) independently
checks one-cutoff/all-orders localization and fifth-order fixed-horizon control for an original
smooth potential. Seven transitive axiom reports cover those clients and the equality and
stability endpoints. Strict source/client checks and the full library build are logged under
`build/audit/heat-test-splitting-localization/`; its `final-snapshot.json` records the actual final
project verification outcome, report and source snapshot. Pinned dependency artifacts are
trusted. No remote CI, commit, push, real-index mutation or certificate change is performed.
