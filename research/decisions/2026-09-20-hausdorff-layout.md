# Hausdorff foundations below KLS geometry

Date: 2026-09-20. Remediation scope: LD-003 and LD-004 in the
[technical-debt register](../technical-debt/README.md).

## Placement decision

The generic normalized measure and slicing interfaces are prerequisites of both general
Analysis clients and concrete perimeter geometry. Their ownership is therefore
`Analysis/Hausdorff`. Finite-dimensional Prékopa–Leindler and Brunn–Minkowski extend the existing
one-dimensional Probability interface and belong in `Probability/BrunnMinkowski.lean`.
No new family directory is needed. The existing namespaces remain public mathematical identities;
this is a source-layout migration, not a namespace or theorem-name migration.

| Module | Responsibility and dependencies |
| --- | --- |
| `Probability/BrunnMinkowski` | Finite-dimensional integral/volume inequalities over `Probability/Line/BrunnMinkowski` |
| `Analysis/Hausdorff/Measure` | Unit-ball constant, normalized Hausdorff measure and codimension-one measure; Mathlib only |
| `Analysis/Hausdorff/Isodiametric` | Bounded-set isodiametric inequality using Brunn–Minkowski and the normalization definitions |
| `Analysis/Hausdorff/Volume` | Covering comparison and top-dimensional normalization, including dimension zero |
| `Analysis/Hausdorff/LevelSet` | Local implicit Lipschitz graphs and finite local Hausdorff measure; Mathlib only |
| `Analysis/Hausdorff/SurfaceSlicing` | Normalized slicing bounds and measurability using Volume and the existing Slicing/Content layers |
| `KLS/Geometry/SmoothDomain/Basic` | Smooth-domain structure and its elementary geometry; consumes Volume and LevelSet |
| `KLS/Geometry/SmoothDomain/Homothety` | Weighted surface change of variables and the smooth-domain boundary specialization |

Moving Homothety into the existing SmoothDomain family avoids leaving a one-file Surface
directory. It uses `SmoothDomain.homothetyHomeomorph` and exports a smooth-domain boundary theorem;
this batch does not extract those declarations or rename them.

## Preserved interfaces

The [complete map](../api-migration/2026-09-20-hausdorff-layout-map.json) records one-to-many source
moves and every public source declaration in the affected modules. No old-path forwarding module
or public alias remains. Imports in actual consumers are updated: graph area and vector slicing
consume volume normalization directly instead of importing LevelSet incidentally.

The proofs and mathematical contracts are preserved: arbitrary weights and sets remain arbitrary,
boundedness is retained for isodiametry, the implicit-graph result keeps its Banach-space scope,
and the measure uses natural subtraction in dimension zero. This changes no proof completion,
certificate registration, normalization factor, theorem name, or parameter order.

## Validation and provenance

The actual dirty baseline, source copies, original staging, raw elaborated snapshots and build
logs are in `build/hausdorff-layout/`. The before snapshot uses copied modules from the passing
`20260920T083028.778520Z` receipt, checked against the current baseline sources. Dated decisions,
explorations and earlier migration/audit snapshots remain unchanged. Live guides, task evidence,
and generated progress views are updated without modifying the user's real index.

Acceptance requires source/declaration-map coverage, comparison of public types and definition
closures (with module location changes accounted for), strict compilation of the affected modules
and an actual downstream client, a cycle/missing-import check, a full build, and `research/verify.py`.
The [batch checks](../technical-debt/2026-09-20-hausdorff-checks.json) record local results; the verifier
produces its own snapshot-bound receipt. Remote CI, commit and push are outside this batch.
