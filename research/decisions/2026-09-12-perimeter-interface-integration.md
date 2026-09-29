# 2026-09-12 — Perimeter chain proof integration and module dependency splitting

Owner requests to connect three existing mathematical input interfaces, differing only in direction of dependency, and to lift the "reserved sorry" restrictions on these three;
All other open proofs remain unchanged. This round does not commit or push. Take over
[Current state audit](2026-09-12-status-audit-and-wip-retention.md),
[Outward normal vector interface closeout](2026-09-12-outward-normal-interfaces-closeout.md) and
[CI replay scope and route verification](2026-09-12-ci-replay-scope-and-route-audit.md); the three records remain as their respective
historical snapshots on the date, with counts unaffected by this round's rewrite.

## Module dependency splitting

`AnalyticPrerequisites` imports `mollifiedIndicator` from `RelativePerimeter`, so reverse import is impossible.
Reconnect the general geometric statements to the perimeter layer. Actual dependency checking shows that the original A segment (Prékopa–Leindler, Brunn–Minkowski, isodiametric inequality, Hausdorff normalization) and B segment (Lipschitz graphs of regular level sets and the finiteness of `μH[n−1]`) only use the symbol `KLS.unitBallVolume` in `RelativePerimeter`, and are unrelated to `SmoothDomain`, relative perimeter, and recovery sequences. Thus, perform minimal splitting:

| Layer | module | content | hole |
| --- | --- | --- | ---: |
| Basic definitions | `KLS/Geometry/SurfaceMeasure.lean` (new) | `unitBallVolume`, `hausdorffNormalized`, `surfaceMeasure`, only definitions | 0 |
| General geometry | `Analysis/LevelSet.lean` (new) | Original A, B two segments transferred character by character, names, name spaces, statements unchanged | 0 |
| perimeter applications | `KLS/WIP/RelativePerimeter.lean` | `SmoothDomain`, relative perimeter, recovery sequence; import the two upper layers | 3 |
| Incomplete WIP | `KLS/WIP/AnalyticPrerequisites.lean` | Only remaining: Gauss–Green, coarea, Sard; still importing `RelativePerimeter` | 5 |

Migration is movement, not copying: no new compatibility aliases, no duplicate proofs, no retention of forward declarations. All consumers have migrated (the C segment of `AnalyticPrerequisites` now references `Analysis.exists_hausdorffMeasure_levelSet_lt_top`). The rules for the newly added `FunctionalInequalities/Analysis/` directory are: geometric analysis unrelated to KLS must not contain `sorry`. Neither the formal entry point nor the 24 certificates import any of these four modules; no changes to the library root or certificate import occurred in this round.

## Three Goals

1. `KLS.hausdorffNormalized_finrank_eq_volume` (`RelativePerimeter.lean`).
   Given by `Analysis.hausdorffMeasure_finrank_eq_smul_volume` for `μH[n] = (2^n/ω_n) • volume`,
   and the factor `ω_n/2^n` of `hausdorffNormalized` is exactly its inverse; `ω_n = √π^n / Γ(n/2+1) > 0` holds for all dimensions, so the product of two `ENNReal.ofReal` is `1`. No separate branch is needed for zero dimension: the general lemma itself has been discussed under `Subsingleton V`, and `ω_0 = 1`, both sides are unit mass on a single point. The normalization constant and the zero-dimensional case are independently verified by separate clients (see below).

2. `KLS.SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` (`RelativePerimeter.lean`).
   Define neighborhoods one by one using the already-proven pointwise regularity of level sets: within the defined neighborhood `W`, `frontier U ∩ W = {φ = 0} ∩ W`
   (the existing `frontier_inter_eq`), while `φ` has nonzero derivative on `W`, thus
   `Analysis.exists_hausdorffMeasure_levelSet_lt_top` provides a finite-measure neighborhood; points outside the boundary are taken as the complement of the closed set
   `frontier U` as a null-measure neighborhood. **Unbounded regions remain within the scope**, the boundary measure can be infinite, with no additional
   finiteness assumptions. For zero-dimensional smooth regions, the boundary is empty, and only the second branch is taken.
   The proof does not use `CompleteSpace V` and `SecondCountableTopology V` (both of which are derived from `FiniteDimensional ℝ V`), and according to the existing text formulation, the unused instances are removed with `omit ... in`, rather than adding a linter suppression; this does not weaken the conclusion.

3. `KLS.Isoperimetry.exists_smooth_approximation_lipschitz` (`CheegerInfimum.lean`).
   By the formal library's `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1` (`a = 0`, `b = 1`)
   Provide a smooth approximating sequence preserving `[0,1]`, preserving the same global Lipschitz constant `K`, and the function and gradient at `L¹(ν)`
   The convergence. The gradient term is exactly what is needed: carry both sides to `Lp V 1 ν`, using `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`
   Obtain `Lp` convergence, then by `Filter.Tendsto.enorm`, `Lp.enorm_toLp`, and `eLpNorm_one_eq_lintegral_enorm`
   Obtain `∫⁻‖∇u_j‖ₑ → ∫⁻‖∇w‖ₑ`. `[0,1]` range, smoothness, global Lipschitz property, and original measure assumptions
   (`m`) is retained, along with (`ν ≪ m`); the statement remains unchanged. This proof does not use `SecondCountableTopology V`; instead it uses
   `omit` processing.

No new axioms, no hidden `sorry`, no weakening of conclusions, no additional substantive assumptions, or no reduction of mathematical scope; the types of the three statements are identical to those before integration (except for the two redundant instances bindable from `FiniteDimensional`).

## Range boundary

This round has no proof of Gauss–Green (C1/C2), coarea, Sard, recovery sequences, nor of the Cheeger comparison for general singular measures, and no other KLS pathways have been initiated. The completion of three interfaces does not imply that the entire perimeter chain has been proven:
`lem:relative-perimeter-smoothing` and `lem:relative-perimeter-cheeger-infimum` task status remains `missing` / `unchecked`; no new ledger nodes have been added, no Blueprint `\lean`/[`\leanok`] anchors; certificate count remains 24.

WIP direct hole reduced from 24 to 21: `RelativePerimeter` 5 → 3, `CheegerInfimum` 9 → 8,
`AnalyticPrerequisites` 5 unchanged, `Energy/WIP/Cheeger` 5 unchanged. Hole count does not equal the number of independent mathematical problems.

## Verification

- **Independent client**: `build/audit/PerimeterInterfaceAudit.lean` (in an ignored directory, use `lake env lean` to directly elaborate, without entering `lake build`, without entering replay sets, without entering certification closure). The five client theorems are all **deductions** rather than restatements of the goal: the normalization constant on the unit ball `ℋ^n(B(0,1)) = ω_n`, the zero-dimensional `ℋ^0(univ) = 1`, a finite measure on any compact piece with smooth boundary (including closed-ball pieces, covering unbounded boundaries), and a single `ε`-approximating function extracted from two limits simultaneously. All five transitive axioms have only `propext / Classical.choice / Quot.sound`, not `sorryAx`.
- **Direct axiom check**: The three goals themselves, along with the migrated `Analysis.hausdorffMeasure_finrank_eq_smul_volume`, `exists_hausdorffMeasure_levelSet_lt_top`, `exists_lipschitzOnWith_levelSet_subset_image`, `isodiametric`, `prekopaLeindler`, `volume_le_ofReal_mul_hausdorffMeasure`, and two Brunn–Minkowski, and `exists_smooth_bounded_L1`, all have only the standard three transitive axioms.
- **Strict mode**: `KLS/Geometry/SurfaceMeasure.lean`, `Analysis/LevelSet.lean`, and audit clients exit 0 under `lake env lean -DwarningAsError=true`. Control group: the same command causes `KLS/WIP/RelativePerimeter.lean` to exit 1 and upgrades 3 of `declaration uses sorry` to error, proving that the option indeed takes effect.
- **WIP with hole**: Four files actually re-elaborate under normal mode, exit 0, and the diagnosis is exactly the expected 3 / 5 / 8 / 5 of `declaration uses sorry`, with no other warnings or errors. **This is not a pass in strict mode**, and cannot serve as evidence of being hole-free.
- Complete default `lake build`, and run `python3 research/verify.py` from the repository root; the final verification receipt is pointed to by `build/verification/latest.json`, matching the final source code snapshot of this round.

All evidence trusts a fixed version of third-party compiled dependencies, does not imply independent rebuilding of Mathlib, remote CI success, or successful Blueprint layout checks. Audit scripts and logs remain in the ignored `build/`. This round does not commit or push as required by owner.
