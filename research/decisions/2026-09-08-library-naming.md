# Library-wide file, namespace, and short-name cleanup

The user requested concise naming organized by mathematical object throughout the formalization
library. Continue from the verified uncommitted working tree, without redoing the migration
from Git HEAD. Baseline snapshot:
`7151e3eb054c8f54dd8322c7fe4ea5af9093e23292179a3abcc450e22b5660b4`, corresponding to
`build/verification/20260908T125319.902218Z/report.json`.
HEAD: `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`, branch `main`.

## Organization and interfaces

This round changes 33 public short names, moves 12 modules, and organizes declaration scopes
and qualified paths in 35 library files. Complete maps:
[public names](../api-migration/2026-09-08-library-naming-name-map.json) and
[module paths](../api-migration/2026-09-08-library-naming-module-map.json).

- Local-slope gradient results move from `KLS/LocalSlopeGradient.lean` to `Energy/LocalSlope/Gradient.lean`, under `namespace FunctionalInequalities.Energy.LocalSlope`, with header `theorem apply_eq_norm_gradient`. They depend only on local-slope definitions and differential tools; consumers explicitly import required Poincaré interfaces.
- Smooth-test Basic, Optimal, Transport, Linear, and Comparison belong together in `Poincare/SmoothTest/`.
- LogConcave uses `Covariance`, `Translation`, `ClosedForm`, `WeightedGradient`, `Isotropic`, and `Poincare`, dropping redundant Affine labels. Borel sets remain distinct from Borell representation.
- `L2.Transport` is grouped into Translation, LinearIsometry, and ContinuousLinearEquiv namespaces. Other cross-object comparisons are grouped by actual object under their common parent. No declaration header in the library uses `_root_.FunctionalInequalities.…` anymore.
- Public names retain their object-namespace ownership. `LogConcave` corollaries remain callable from property proofs, such as `hμ.intrinsicCovariance_closedQuadratic`, `hμ.intrinsicSmooth_constant_eq_localSlope`, and `hμ.intrinsicWeightedOperator m B`. `f.energy`, `f.toL2`, and `hf.memLp` are preserved.

Names retain meaningful weighted, covariance, smooth, Lipschitz, intrinsic, ae, finiteness,
and comparison-direction distinctions; types and documentation give all conditions.
No normalization, test class, or carrier changes; no parameter generalization, compatibility
aliases, wrappers, proof placeholders, or disabled linters.

## Semantic and source review

First check that the full baseline source matches the passing receipt, then save source and
resolved reference locations. The full-expression baseline combines the verified 1085-item
snapshot with the subsequent 132-item comparison-renaming closure. Reading old records applies
the previously verified 12-name map before the current map, without reverting approved changes.

- All 881 public source signatures and 189 definition/structure bodies agree individually.
- All 969 declaration bodies, including private helpers, solutions, and examples, agree individually.
- For the 1085 local declarations reachable from all 881 public roots, raw Lean Expr types and definition closures agree after declaration/path mapping and binder alpha normalization, without additions, omissions, or unexplained differences. Universes, parameter order, explicitness, types, and dependencies agree. Compiler command hashes for anonymous instances and declared module moves are normalized separately; local hygiene indices remain checked. Source comparison and Lean checking separately cover theorem proof bodies.
- All 26 statement golden checks pass; golden files and their referenced original decision are unchanged.
- Check all 158 infrastructure source records against baseline files and old hashes before refreshing 58 using the semantic comparison. All 94 existing decisions, explorations, and migration records remain byte-identical.

Review details: [review](../api-migration/2026-09-08-library-naming-review.json) and
[evidence](../api-migration/2026-09-08-library-naming-evidence.json). Raw local audit artifacts
are in `build/api-final-naming/`. The complete current public-name inventory is refreshed from
finally compiled `.ilean` files into `build/name-inventory/current-public-names.md` and `.txt`.

## Acceptance

Default `lake build` passes. All 33 new names resolve and old names do not.
Blueprint PDF, Web, and checkdecls pass. All 37 pages were rerendered and compared pixelwise
with the previous verified PDF, with identical results; pages 7 and 29 were reviewed again
with no layout changes. Final unified acceptance uses root `python3 research/verify.py`;
its final source snapshot and gate receipts, including kernel replay of all local modules,
are authoritative. This work changes only the local working tree; no commit or push.
