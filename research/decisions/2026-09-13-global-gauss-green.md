# 2026-09-13 — Global Gauss–Green: Finite Smooth Partition of Unity Stitching and Downstream Closure

Owner requires the use of locally proven chart-based formulas, connected via finite smooth partition of unity, to eliminate the global vector field Gauss–Green
`sorry`, and to verify that the two downstream formulas no longer transmit dependencies `sorryAx`; direct implementation and verification are carried out, with no commit or push in this round. Acceptance of
[subgraph divergence record](2026-09-13-subgraph-divergence-and-local-gauss-green.md),
[boundary chart and area interface record](2026-09-13-boundary-chart-and-area-interface.md),
[Gauss–Green area formula record](2026-09-12-gauss-green-area-formula.md), and
[interface connection record](2026-09-12-perimeter-interface-integration.md). Previous unsubmitted modules, perimeter interface proofs,
graph area formula, boundary charts, subgraph divergence formulas, and local Gauss–Green are all retained, without reset, coverage, or redundant implementation;
historical records maintain their original text and count.

## Conclusion first

| Goal | Status | Transitive Axioms |
| --- | --- | --- |
| 1. Global vector field Gauss–Green `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | **Completed** | Standard three conditions |
| 2. Finite smooth decomposition interface `Analysis.exists_finset_sum_eq_of_isOpen_cover` | **Completed** | Standard three lines |
| 2'. Integrability interface `integrableOn_inner_outwardNormal`, continuity of divergence/compact support/finitely additive | **Completed** | Standard three |
| 3. Scalar form `setIntegral_gradient_eq_integral_smul_outwardNormal` | **Completed** (reduced, no holes) | Standard three lines |
| 3'. Polishing indicator gradient `gradient_mollifiedIndicator_eq` | **Completed** (reduction, no holes) | Standard three rules |
| coarea, Sard, recovery sequence, Cheeger infimum, singular measure comparison | unchanged | still contains `sorryAx` |

The certificate count remains 24, no new ledger nodes have been added, no Blueprint `\lean`/[`\leanok`] anchor points,
the infrastructure status of `lem:relative-perimeter-smoothing` remains `missing`.
WIP direct hole decreased from 20 to **19** (`RelativePerimeter` 3, `AnalyticPrerequisites` 4 → **3**, `CheegerInfimum` 8, `Energy/WIP/Cheeger` 5). **Completing the global Gauss–Green does not equal completing the relative perimeter chain.**

## 1. Statement unchanged

`FunctionalInequalities/KLS/Geometry/GaussGreen.lean`:

```
theorem KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal
    (U : SmoothDomain V) {F : V → V} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∫ x in U.carrier, Analysis.divergence F x
      = ∫ x in frontier U.carrier, ⟪F x, U.outwardNormal x⟫ ∂(surfaceMeasure V)
```

Names, namespaces, assumptions, `surfaceMeasure` normalization and outer normal direction are identical to the previous `sorry` version word for word.
**No** additional assumptions of bounded domains, finite total boundary measure, `F` higher-order smoothness, or `V` nonzero dimension are introduced, and no weakening of the conclusion is made.

## 2. Complete coverage of three types of local blocks

Covers a compact set `K = tsupport F`, indexed type is `Bool ⊕ ↥(frontier U.carrier)`, three families of open sets:

* **Bar chart**: For each boundary point `z`, `exists_boundaryChart` provides a chart, this round's new addition of
  `BoundaryChart.self_mem_cylinder` (`graphCoord x₀ x₀ = 0 ∈ param`, `graphHeight x₀ x₀ = 0 < depth`)
  ensures that `z` falls within its own bar;
* **Interior region** `U.carrier` (open);
* **Exterior region** `(closure U.carrier)ᶜ` (open).

Coverage comes from the openness of `U` `interior U = U`: if a point is not in `U` and not in `frontier U`, then it is not in `closure U`.
**One cannot rely solely on boundary cylinders**—the support might lie entirely inside or outside; two independent clients (discussed below, Client 1, 2) represent these two cases.

Treated in three parts, all within `KLS/Geometry/GaussGreen.lean`:

* **Chart block**: Directly invoke already proven
  `BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`;
* **Interior block** `integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_carrier`:
  `tsupport Gᵢ ⊆ U.carrier` makes `Gᵢ` and `divergence Gᵢ` zero outside `U`, thus
  `∫_U div Gᵢ = ∫_V div Gᵢ = 0` (`setIntegral_eq_integral_of_forall_compl_eq_zero` plus
  (`Analysis.integral_divergence_eq_zero`); the flux side is zero because the open set `U` and `frontier U` are disjoint,
  Hence `Gᵢ` is identically zero on the boundary;
* **External block** `…_of_tsupport_subset_compl_closure`: `U ⊆ closure U` and
  `frontier U ⊆ closure U` Makes both integrand functions on both sides identically zero.

Zero-dimensional spaces, empty supports, and empty boundaries are all covered by the same path: `Subsingleton V` at `frontier U = ∅`, the summation condition of the partition of unity on `tsupport F = ∅` is the empty condition, and the decomposition `F = Σᵢ Gᵢ` holds by `F x = 0` outside the support.
No `Nonempty`, `Nontrivial`, or dimension lower bound assumptions are made throughout.

## 3. Partition of unity: interfaces and the key point of "global equation"

`FunctionalInequalities/Analysis/PartitionOfUnity.lean`, `Analysis.exists_finset_sum_eq_of_isOpen_cover`:
For a finite-dimensional real normed space `V`, a compactly supported map `C^n` from `F : V → E` to `tsupport F`, and an open cover `W`,

```
∃ (s : Finset γ) (G : γ → V → E),
  (∀ i, ContDiff ℝ n (G i)) ∧ (∀ i, HasCompactSupport (G i)) ∧
  (∀ i, tsupport (G i) ⊆ W i) ∧ ∀ x, ∑ i ∈ s, G i x = F x
```

Three points are deliberately included in the statement:

1. **`tsupport (G i) ⊆ W i`, not `support (G i) ⊆ W i`**. The inclusion of closed supports is what makes `G i` zero on a neighborhood of every point outside `W i`, thereby making `fderiv ℝ (G i)` also zero—this is exactly the localizing condition required by each of the three local blocks;
2. **The global identity of `∀ x`** is not merely a pointwise identity on `tsupport F`. An identity valid only on the support cannot be differentiated;
this round therefore **does not** follow the route of "first decomposing on `K`, then differentiating, and then eliminating `Σ ∇χᵢ = 0`", but instead directly applies the finite additivity of `fderiv` to the global function identity, with the derivative terms never appearing in the decomposition;
3. **Finite sum**, not `finsum`. Finiteness arises from
the action of `LocallyFinite.finite_nonempty_inter_compact` on a compact set `tsupport F`: the indices corresponding to disjoint support from `tsupport F` yield a `G i` that is **everywhere** zero, not just zero on the support.

The path is Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, taking manifold `V` as its model
(`𝓘(ℝ, V)`; `V` is Hausdorff, σ-compact, finite-dimensional), `contMDiff_iff_contDiff` replaces the manifold meaning of `C^∞` with `ContDiff ℝ ∞`, then takes `G i = χ i • F`. It does not rebuild bump functions or cover lemmas itself.

## 4. Integrability and finite summation: full proof, no assumptions

`Analysis/Divergence.lean` Added (and moves `fderiv_eq_zero_of_notMem_tsupport` from
`Analysis/SubgraphDivergence.lean` **downward** to this location, name and statement unchanged, original location left without duplicate proof or alternative name):

* `traceLM`: trace functional of `(V →L[ℝ] V) →ₗ[ℝ] ℝ`, automatically continuous on finite-dimensional spaces (`continuous_traceLM`);
* `continuous_divergence`: divergence of `C¹` field is continuous (`traceLM ∘ fderiv`);
* `divergence_eq_zero_of_notMem_tsupport` and `hasCompactSupport_divergence`;
* `divergence_finset_sum`: when pointwise differentiable, divergence is additive over finite families ((`HasFDerivAt.sum`) linearity of trace).

`KLS/Geometry/GaussGreen.lean` new:

* `norm_outwardNormal_le_one`: The outer normal is everywhere compressive (unit vector on the boundary, zero outside the boundary);
* `integrableOn_inner_outwardNormal`: The flux integral of the continuously compactly supported vector field is integrable on `frontier U` with respect to `surfaceMeasure`. The control term is `‖G x‖`, using `abs_real_inner_le_norm` and `‖ν‖ ≤ 1`; the measure side only requires `measurable_outwardNormal` and `isLocallyFiniteMeasure_surfaceMeasure_frontier`, **no** bound on the total quantity of `surfaceMeasure (frontier U)`, so unbounded boundaries remain within the scope.

Thus the integrability assumptions for both `integral_finsetSum` are actually proven: the volume side is given by "continuous + compact support"
`IntegrableOn (divergence (G i)) U.carrier volume`, the boundary side is given by the previous one.
Pointwise decompositions of the integrand are `Analysis.divergence_finset_sum` (volume side) and `sum_inner` (boundary side).
The full-definition integral in Lean indeed would cause non-integrable terms to go into 0, but in this round, no step of integrability check was omitted for that purpose.

## 5. Module Organization and Migration

* General components move to the foundational layer: `Analysis/PartitionOfUnity.lean` (new) and `Analysis/Divergence.lean` (extended);
  `fderiv_eq_zero_of_notMem_tsupport` Move from `SubgraphDivergence` to `Divergence`.
The global conclusion of `SmoothDomain` is placed in the application layer new module `KLS/Geometry/GaussGreen.lean`, located at
  Above `KLS/Geometry/LocalGaussGreen.lean` and below `KLS/WIP/AnalyticPrerequisites.lean`.
* **Minimum splitting migration**: `isLocallyFiniteMeasure_surfaceMeasure_frontier` and
  `integrableOn_smul_outwardNormal` moves unchanged from `AnalyticPrerequisites` into the same new module (same namespace,
  (Same name, same statement), since they are the hole-free boundary integrability interface required by this round of proof. **No** compatible aliases,
  Repeated proof or forwarding of declarations; the only consumer `AnalyticPrerequisites` is changed to import a new module.
* `Analysis/PartitionOfUnity.lean` and `KLS/Geometry/GaussGreen.lean` neither import coarea, Sard or
  Any module with a hole. The directional dependence is still acyclic:
  `Analysis/{AreaFormula, ImplicitGraph, SubgraphDivergence, GraphIntegral, PartitionOfUnity}`
  → `KLS/Geometry/{BoundaryChart, LocalGaussGreen, GaussGreen}` → `KLS/WIP/AnalyticPrerequisites`.
* No new axioms, no hidden `sorry`, no weakening of conclusions, no increase in substantive assumptions. No issues found in the statement, thus the problem remains unchanged.

## 6. Count correction

`AnalyticPrerequisites` There are currently 6 public theorems, 0 definitions: 3 have been filled with proofs
(`ae_forall_fderiv_ne_zero`, `setIntegral_gradient_eq_integral_smul_outwardNormal`,
`gradient_mollifiedIndicator_eq`), 3 have direct `sorry`
(`aemeasurable_lintegral_levelSet`, `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, `sard`);
among the filled 3 entries, **2** lack transitivity of `sorryAx`, only `ae_forall_fderiv_ne_zero` due to `sard` still contains `sorryAx`.
Before migration: 9 public theorems, 5 filled, 4 holes, 2 without `sorryAx`; earlier (before `outwardNormal` migration):
13 public theorems and 1 definitions. Historical records are preserved as originally written.

## 7. Verification

* **Transitive Axioms**: `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`,
  Two local block lemmas, `integrableOn_inner_outwardNormal`, `integrableOn_smul_outwardNormal`,
  `isLocallyFiniteMeasure_surfaceMeasure_frontier`,
  `Analysis.exists_finset_sum_eq_of_isOpen_cover`, `Analysis.divergence_finset_sum`,
  `Analysis.continuous_divergence`, and downstream's
  `setIntegral_gradient_eq_integral_smul_outwardNormal` and `gradient_mollifiedIndicator_eq` ——
  Everything is only `propext / Classical.choice / Quot.sound`.
* **Independent client**: `build/audit/GaussGreenAudit.lean` (ignore directory, `lake env lean` directly elaborate,
  Not advancing `lake build`, replay sets, or certification closure). Eleven client theorems, transitive axioms have only the standard three:
  1. `client_support_inside`: When the support is completely contained within `U`, the Gauss–Green theorem is used to derive `∫_U div F = 0`;
  2. `client_support_outside`: When the support is completely outside `closure U`, the boundary flux is zero;
  3. `client_halfSpace_global`: Using global formulas on the half-space `{⟪a,x⟫<0}` (`‖a‖=1`), without support restrictions,
     The outer normal is concrete `+a`—this is the substantive difference from the previous round of local client charts;
  4. `client_halfSpace_flux_sign`: If the boundary flux is non-negative, then the total divergence is non-negative, **sign check under direction convention**;
  5/6. `client_interval_normal_left` / `_right`: The outer normal to the one-dimensional interval `(α,β)` at the left endpoint is `-1`,
     The right-hand side is `+1`;
  7. `client_interval_endpoints`: The global formula is given on `(α,β)` `∫_α^β F' = F β - F α`,
     The normal signs at both ends are checked (pointwise integrals at two points on `ℋ^0`, `surfaceMeasure ℝ = μH[0]`,
     `unitBallVolume 0 = 1`);
  8. `client_empty_frontier`: When `U = univ`, the boundary is empty, and the formula degenerates into the divergence theorem over the entire space (in any dimension);
  9. `client_subsingleton`: On zero-dimensional spaces, the boundary must be empty, and both sides are zero, without `Nontrivial` assumptions;
  10/11. `client_scalar_form`, `client_mollified_gradient`: two downstream formulas, denoted by
     `∫_U ∇η = ∫_∂U η n` is kept unchanged along with the negative sign of the smoothed indicator gradient.
  The three previous rounds' `AreaFormulaAudit.lean`, `BoundaryChartAudit.lean`, `PerimeterInterfaceAudit.lean`,
  `SubgraphDivergenceAudit.lean` rerun, conclusion and axioms remain unchanged.
* **Strict mode**: `Analysis/{Divergence, PartitionOfUnity, SubgraphDivergence, GraphIntegral,
  ImplicitGraph, AreaFormula, LevelSet}` and `KLS/Geometry/{SurfaceMeasure, BoundaryChart,
  LocalGaussGreen, GaussGreen}`, together with five audit clients, exit 0 under `lake env lean -DwarningAsError=true`.
* **WIP with a hole**: four files in normal mode actually re-elaborated, exit 0, diagnosis is exactly as expected
  3 / 3 / 8 / 5 entries `declaration uses 'sorry'`, no other warnings or errors. **This is not a strict mode pass.**
Complete default `lake build` (3393 jobs), and run `python3 research/verify.py` from the repository root;
  The infrastructure evidence hashes for `lem:relative-perimeter-smoothing` are recomputed from this round’s sources, and the two new modules are added,
  note Synchronized with gaps, status remains `missing`. Final verification receipt pointed by `build/verification/latest.json`,
  Matches the final code snapshot.

Evidence of trust in fixed-version third-party compiled dependencies does not imply independent reconstruction of Mathlib, remote CI, or Blueprint formatting passes.
Audit scripts and logs remain in the ignored `build/`. This round does not submit or push as required by the owner.

## What remains in the completion of the distance-relative perimeter chain

1. **Weighted coarea formula** and its measurability (`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`,
   `Analysis.aemeasurable_lintegral_levelSet`). Mathlib only has the Jacobian area formula for equal-dimensional cases.
2. **Sard's theorem for real-valued functions** (`Analysis.sard`). Mathlib only has the equal-dimensional version
   `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.
3. **Gradient integral estimates for smoothed outer expansions and recovery of relative perimeter sequences**: now it can be advanced using the already closed
   `gradient_mollifiedIndicator_eq` and the local finiteness of the area measure, but no progress has been made in this round.
4. Gaps in `RelativePerimeter` 3 and `CheegerInfimum` 8 and `Energy/WIP/Cheeger` 5 remain,
   the Cheeger comparison for singularities is still open.
