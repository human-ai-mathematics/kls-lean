# Route Investigation of Lipschitz Vector Coarea: m-Codimensional Coarea from `C¹` to Lipschitz

2026-09-19. This round is a **route probing**, following the sharp Sard route round on the same day. **No theorem is proved**, no new library modules are added, and no existing `.lean` is modified. The deliverables are: precise localization of gaps, identifying at which step the scalar side route is available and at which step missing, accurate retrieval of Mathlib and this repository, a numbered obligation list (each entry paired with an exact Lean statement, line number, and risk), and a route statement file containing only `#check` `research/audits/LipschitzVectorCoareaRouteStatements.lean`.
**Type-checking a proposition is not a proof**; none of `L0`, `V1`, `V3`–`V5` is proved in this repository.
No hole migration, no commit, no push. Direct holes remain **8 (1/2/5)**, and certification remains **24**.

Origin `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; origin passed verification receipt
`build/verification/20260918T114131.124380Z/report.json` (final verification receipt for sharp Sard route round):
10 gates, 224 local module kernel replay, 617 entries, snapshot `cfd1dab59526eeca9f0584e76825a1d545bde07dd70c38709b2a0235a649f482`.
The origin workspace drift is empty, and concurrent sessions have not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two proof holes) credited to author **Haocheng Wang**, not touched in this round. Sharp finite regular Sard (already established on the same day via a separate path), five holes in Energy, dimension-free KLS, all untouched.
This route only reaches **global Lipschitz** (`LipschitzWith K u`); the local Lipschitz version `M2` is explicitly outside the scope of this route.

## 1. Gap

The `Analysis/RankDeficient/Coarea.lean` `coarea_of_contDiff` (`R9`) is the coarea formula of codimension m,
No assumptions are made on the critical set, but the requirement of **`C¹`** is imposed. Federer's coarea formula holds for mappings that are only Lipschitz;
The scalar side already completed `C¹ → Lipschitz → locally Lipschitz`
 (`KLS/Geometry/{SmoothCoarea,LipschitzCoarea,LocallyLipschitzCoarea}.lean`).
**Vector side stops at `C¹`**—this is the target `L0`: replace `coarea_of_contDiff`'s `ContDiff ℝ 1 u` with
`LipschitzWith K u`, the rest unchanged. Density still written `coareaJacobian (fderiv ℝ u x)`:
`fderiv` At non-differentiable points, it is garbage values, and according to Rademacher, it is a Lebesgue null set, consistent with the scalar `L12` convention using `gradient`.

## How does the scalar side proceed, and at which step is there a gap in dimension m?


`KLS.coarea_of_lipschitz` (`L12`) is divided into three steps:

1. `Analysis.exists_contDiff_pieces` (`L7`) divides the domain into countably many pairwise disjoint measurable pieces, each piece having a `C¹` function that is **first-order compatible** (matching values and derivatives) with the `u`, and the complement having Lebesgue measure zero;
2. On each piece, the `C¹` formula is applied, and first-order compatibility ensures that the density and the slice match;
3. The countable sum is taken, and the zero-measure complement is removed by "removing the zero-measure sets in almost every level slice".

m-codimensional **second-to-last step is ready**: Step 2 is `coarea_of_contDiff`; Step 3 is
`Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`—take `d = k`, whose assumption
`μH[k + m] N = 0` under `k + m = n` via `Analysis.hausdorffMeasure_finrank_eq_smul_volume` is exactly
«`N` Lebesgue null» (`V2`; about ten lines of derivation, not yet committed in this round, only type-checked for derivability).
**Step 1 is absent**: behind `L7`, the entire jet and Whitney chain (`LipschitzJet.exists_compact_jets`,
`WhitneyJet.exists_contDiff_extension`, `exists_contDiff_pieces`) all carry `u : V → ℝ`,
there is nothing in the vector bundle replacing them. **`V1` (vector `C¹` piecewise) is the only truly new component.**

## Three. `V1` How to Proceed: Handle components individually, rather than turning the Whitney extension into a vector target

Take a linear isometry `e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)` (`isometryEquivOfFinrankEq` already in repository).
Each coordinate `fun y => e (u y) i` of `u` is a scalar `K`-Lipschitz function (`V4'`); apply the **proved** `L7` to each
Obtain a countable partition for oneself; `V3` take a countable common refinement of these `m` partitions (`ℕ^m` countable, still indexed by `ℕ`,
The complement is contained in the union of `m` zero-measure sets; on each common patch, all coordinates match their respective `C¹` scalar representatives to first order.
`V4''` derives differentiability of `u` from coordinate differentiability; `V4` upgrades coordinatewise agreement to vector first-order agreement between `u` and `e.symm ∘ (representative)`.
Thus `V1` does not require new analysis, only ledgering plus calculus; `V5` is a scalar `L12` assembly of codimension m, word-for-word replication,
The implication "from `V1` to `L0`" establishes `L0 = V5 ∘ V1`.

**This is the most substantive judgment, and also where it might be wrong**: if `V3`'s common refinement has more difficulty with measurability or disjointness than anticipated,
or if `V4` encounters gaps in Mathlib during its quantization over `fderiv` (the composition of `fderiv` and `e`, or coordinate projections),
then `V1` will have to retreat to the "re-route Whitney extension as a vector target" approach. This round has not verified `V3` or `V4`.

## IV. What does Mathlib have and lack, and what does this repository have and lack?

**Mathlib**: Has Rademacher (`LipschitzWith.ae_differentiableAt`), `differentiableAt_pi`, `fderiv_pi`, `LinearIsometryEquiv` with differential properties; **no coarea formula**.
**This repository**: `L7` (real-valued), `coarea_of_contDiff` (`C¹`, codimension m), codimension m zero slice
`ae_hausdorffMeasure_inter_levelSet_eq_zero_vector` (already the shape required by `V2`), measurability of slices without regularity, `isometryEquivOfFinrankEq`. **Missing**: `V1`, `V3`, `V4`, `V4'`, `V4''`, `V5`, `L0`.

## Five. List of Responsibilities

Precise Lean statements at `research/audits/LipschitzVectorCoareaRouteStatements.lean`, numbered as per this table;
This file contains only `#check` (5 references to proven statements, 10 obligations/diagnoses), no declarations, no proofs, no placeholder axioms,
passed via `-DwarningAsError=true`. **Type checking passing is not a proof.**

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `L0` | **Objective**: Replace `coarea_of_contDiff`'s `ContDiff ℝ 1` with `LipschitzWith K` | — | Composed from `V1` + `V5` |
| `V1` | vector `C¹` slicing (vector version of `L7`) | 80 | center (composed from `V3`+`V4`+`V4'`+`V4''`) |
| `V2` | Lebesgue null-measure complement on almost every level `hausdorffNormalized k` null-measure | 15 | Low (already certified derivable) |
| `V3` | countable common refinement of finitely many countable partitions | 80 | middle (accounting) |
| `V4'` | coordinates of a Lipschitz map are Lipschitz | 15 | low |
| `V4''` | coordinate differentiable ⟹ differentiable | 20 | low |
| `V4` | coordinate-wise first-order agreement ⟹ vector first-order agreement | 60 | middle (`fderiv` quantified) |
| `V5` | Assembly: Along piecewise countably additive (verbatim scalar `L12`) | 150 | Medium |
| `M1` | Diagnosis: Lipschitz does not imply `C¹` | — | Not a step |
| `M2` | Later: local Lipschitz version, **explicitly not part of this route** | — | Scope definition |

Total of approximately **420 lines**. Recommended order: `V4'`, `V4''`, `V4`, `V3`, `V1`, `V2`, `V5`, `L0`.
No pointwise criterion: `V3`, `V4` are both bypassable accounting entries; the actual analysis (`L7`, `R9`, zero slice) has been proven.

## VI. Clarify What Hasn't Been Proven

* This round proved no theorems. `L0`, `V1`–`V5` are all unproven; `V2` is not checked in.
* The local Lipschitz version `M2` is outside the current path; vector-valued Sard, critical value measure, and Whitney counterexamples are also outside the current path.
* Cheeger's two-hole result belongs to Haocheng Wang; Energy five holes, sharp Sard remain untouched; dimension-free KLS is still open.

## VII. Verification

`research/audits/LipschitzVectorCoareaRouteStatements.lean` passed via `lake env lean -DwarningAsError=true`,
15 `#check`s, 0 errors, 0 warnings, logs `build/audit/lipschitz-vector-coarea-route/route-statements.log`;
local import closure excludes WIP files. No library source code modified, no changes to aggregate imports.
Root directory `python3 research/verify.py` rerun at end of this round, final verification receipt recorded at
`build/audit/lipschitz-vector-coarea-route/final-snapshot.json`, snapshot and workspace recalculated individually, drift is empty.
See details in `research/explorations/2026-09-19-lipschitz-vector-coarea-route.json`.

## Note (2026-09-19, after implementation)

`L0`, `V1`–`V5`, `V4'`, `V4''`, `M1` are all proven (`Analysis/Lipschitz/{Componentwise,Refinement,VectorPieces,VectorCoarea}.lean`),
`L0 = V5 ∘ V1` as planned by the route; `V3` uses an injection `(Fin m → ℕ) ↪ ℕ` rather than equivalence (`m = 0` when `Fin 0 → ℕ` is a singleton).
The `M2` outside the range is also proven together with the local Lipschitz route (`N0 = X5 ∘ L0`). See [implementation record](2026-09-19-coarea-sard-proofs.md).
