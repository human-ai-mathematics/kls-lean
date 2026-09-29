# Local Lipschitz vector coarea route exploration: the final step of vector chains

2026-09-19. This round is a **route exploration**, following the same day's Lipschitz vector coarea route, aiming to address the ones that fell outside the range in that round.
`M2`——here recorded as `N0`: the m-codimensional coarea formula holds under the local Lipschitz assumption, without global constants or global moduli.
**No proof of any theorem**, no addition of any library modules, no modification of any existing `.lean`. The deliverable is:
Reduction of scalar `L13` is step-by-step verified in codimension m, focusing on the components that need to be replaced (vector Lipschitz extensions) and the approach that does not require Kirszbraun.
Numbered obligation list, and a route statement file containing only `#check`
`research/audits/LocallyLipschitzVectorCoareaRouteStatements.lean`.
**The proposition passing type checking is not a proof**; `N0`, `X1`, `X3`–`X5` **none of them** are proven in this repository.
No migration, no commit, no push. Direct proof holes remain **8 (1/2/5)**, certification remains **24**.

Origin `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; origin verification receipt
`build/verification/20260918T115012.397782Z/report.json` (Final verification receipt for Lipschitz vector coarea route round):
10 gates, 224 local module kernel replays, 620 entries, snapshot `4793a31700897b94edbb049599ccbc7f2b2dc0feb9fbd58af850eeca63ab5352`. The origin workspace drift is empty, and concurrent sessions have not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) are attributed to author **Haocheng Wang**, untouched in this round.
Sharp finite regular Sard, Energy's five holes, dimension-free KLS, and the domain is not extended to open subsets or manifolds.

## 1. Location

`R9` (`C¹`, proven) → `L0` (global Lipschitz, same path, unproven) → `N0` (local Lipschitz, current path).
Scalar side corresponds to `L11 → L12 → L13`, `L13` is `KLS.coarea_of_locallyLipschitz`, proven. `N0` is a common generalization of `L0` and `R9`:
Global Lipschitz and `C¹` both imply local Lipschitz (`C1`, `C2`).

## Two. Reduction of Scalar `L13`, Step-by-Step Verification

`L13` Reduce using half-open annular bands `A k = ball 0 (k+1) \ ball 0 k` to `L12`:
(1) `u` is Lipschitz on closed ball (with constant `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`);
(2) McShane extension `LipschitzOnWith.extend_real` yields a global Lipschitz `v k`, equal to `u` on closed ball;
(3) The piece `S ∩ A k` is contained in an open ball, and `u = v k` holds in a neighborhood of each point, so the gradient and level sets agree on the piece;
(4) Apply `v k` with `L12`; (5) `lintegral_iUnion`, `lintegral_tsum`, and `AEMeasurable.tsum` are countably summable.

m-codimensional 1, 3, 4, 5 are verbatim copied: 1 is independent of the target (`X2`); 3 uses `Filter.EventuallyEq.fderiv_eq` instead of `gradient_eq`, and the density `coareaJacobian (fderiv ℝ u x)` is consistent accordingly (`X4`); 4 uses `L0`; 5 is the same (`X3` ledger entry).

**Only 2 needs to be changed**: `extend_real` is scalar-valued, Kirszbraun is not in Mathlib. But `L0` only requires the existence of some constant, so coordinate-wise McShane is sufficient: linearly isometric to `EuclideanSpace ℝ (Fin m)`, `WithLp.ofLp` to the sup norm `Fin m → ℝ`, then apply Mathlib's `LipschitzOnWith.extend_pi`, then via `WithLp.toLp` (constant `√m`) and `e.symm` back to `W` (`X1`). This is a ledger entry, not an analysis, and no claims are made about the constant.

`X5` Write these five steps as a single implication: **from `L0` to `N0`**. Thus `N0 = X5 ∘ L0`, the vector chain
C¹ → Lipschitz → local Lipschitz is closed in whole at the moment it is proven in `L0`.

## Three. What is Mathlib and this repository

**Mathlib**: `LipschitzOnWith.extend_pi`, `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`,
`Filter.EventuallyEq.fderiv_eq`, `PiLp` Lipschitz equivalence, `lintegral_iUnion` / `lintegral_tsum`;
**No** Kirszbraun, no coarea. **This repository**: `L13` (template), `R9`. **Missing**: `X1`, `X3`, `X4`, `X5`, `N0`; `L0` has an alternative route.

## Section Four: Obligations List

Precise Lean statements at `research/audits/LocallyLipschitzVectorCoareaRouteStatements.lean` (2 cited proven statements, 9 obligations/diagnoses/consistency),
no declarations, no proofs, no placeholder axioms, passed via `-DwarningAsError=true`. **Type checking passing is not a proof.**

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `N0` | **Objective**: Replace `coarea_of_contDiff`'s `ContDiff ℝ 1` with `LocallyLipschitz` | — | `X5` is used for `L0` |
| `X1` | Vector Lipschitz extension with quantified constants (coordinate-wise McShane, non-Kirszbraun) | 40 | Low (`PiLp` constant transfer) |
| `X2` | local Lipschitz ⟹ Lipschitz on each closed ball | 10 | low (Mathlib directly provides) |
| `X3` | Half-open annular region: measurable, pairwise disjoint, covers, contained in an open ball neighborhood | 40 | Low (verbatim copy of `L13`) |
| `X4` | Equality on an open set implies equal `fderiv` and level sets on the piece | 20 | Low |
| `X5` | Assembly: `L0 ⟹ N0` (verbatim copy of `L13`) | 120 | Medium |
| `D1` | Diagnostic: on the plane, `x ↦ ‖x‖² e₀ + ‖x‖ e₁` is locally Lipschitz, not globally Lipschitz, and not differentiable at 0 | 60 | Not a route step |
| `C1`, `C2` | Consistency: global Lipschitz, `C¹` locally Lipschitz | 5 | Not a step |

Total of approximately **230 lines** (excluding `L0` itself). Recommended order: `X2`, `X3`, `X4`, `X1`, `X5`; `N0` immediately follows `L0`.
No pointwise criterion: all analyses have been completed in `L13` and `R9`.

## Five. Clarify What Has Not Been Proven

* This round proves no theorems. `N0`, `X1`–`X5` are all unproven; `L0` remains open.
* Not the Sard theorem; the constant in `X1` lacks optimality; the domain is not generalized.
* Cheeger's two-hole problem belongs to Haocheng Wang; Energy's five-hole, sharp Sard remain untouched; dimension-free KLS is still open.

## Section 6. Verification

The route file passes through `lake env lean -DwarningAsError=true`, 11 `#check`, 0 errors, 0 warnings, log `build/audit/locally-lipschitz-vector-coarea-route/route-statements.log`; local import closures do not include WIP files.
No library source code is modified, no changes to aggregation imports. The root directory `python3 research/verify.py` is rerun at the end of this round, with final verification receipt recorded at `build/audit/locally-lipschitz-vector-coarea-route/final-snapshot.json`; snapshots and workspaces are recalculated individually, drift is empty.
See details in `research/explorations/2026-09-19-locally-lipschitz-vector-coarea-route.json`.

## Note (2026-09-19, after implementation)

`X1`–`X5`, `D1`, `C1`, `C2` all proved (`Analysis/Lipschitz/{Extension,Annuli,Local}.lean`), `L0` proved on the same day,
thus `N0 = X5 ∘ L0` is `Analysis.coarea_of_locallyLipschitz`. See [implementation record](2026-09-19-coarea-sard-proofs.md).
