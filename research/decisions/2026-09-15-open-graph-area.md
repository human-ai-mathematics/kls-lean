# Weighted Area of Open Domains (L8)

2026-09-15. This round **proves L8 of the weighted coarea route**: the weighted graph area substitution is extended from "global `C¹` parameter function" to "only on the open set `O` `C¹`". No commit, no push, no alteration of historical decisions. The initial HEAD is
`2965b32bc79bdb24921c633df12102450eaedcc4`; the initial passed verification receipt is
`build/verification/20260915T040555.802878Z/report.json` (byte-for-byte identical to `build/verification/latest.json`), and the recomputed full snapshot matches the receipt: 427 files, SHA256 `61aec2ce1f3db09ecea5c80d51f2c06567fd23f52d55faf4b860434a92cc3b2b`. The byte-for-byte comparison refers to consistent file-level SHA256 (including deleted items) and full snapshot structure, not merely the HEAD.

## Content of this round of proof

New module `formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean`:


```lean
/-- C¹ local extension: on an open set, a C¹ function equals some global C¹ function on some ball around each point -/
theorem FunctionalInequalities.Analysis.exists_contDiff_one_eqOn_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) (hz : z ∈ O) :
    ∃ (ρ : ℝ) (w : E → F), 0 < ρ ∧ Metric.ball z ρ ⊆ O ∧ ContDiff ℝ 1 w ∧
      Set.EqOn w f (Metric.ball z ρ)

/-- Weighted change of variables (with the `setLIntegral_image_graphChartMap` case of `x₀ = 0`) -/
theorem FunctionalInequalities.Analysis.setLIntegral_image_graphMap …

/-- L8 -/
theorem FunctionalInequalities.Analysis.setLIntegral_image_graphMap_of_contDiffOn
    (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1) (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ))
    {O S : Set H} {v : H → ℝ} {f : V → ℝ≥0∞}
    (hO : IsOpen O) (hv : ContDiffOn ℝ 1 v O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hf : Measurable f) :
    ∫⁻ x in graphMap ι e v '' S, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H)
```

Completely consistent with the L8 route record (only replacing the weight variable name in the conclusion with `f`, no additional assumptions introduced):
`S` does not require boundedness or finite measure, weights do not need to be integrable, bounded, or finite (allows constant `⊤`),
`v` has no regularity requirements outside of `O`, both `O = ∅` and `S = ∅` are covered.
Client `target` reproduces and proves the route primitive statement verbatim.

## Why must we perform countable localization?

**Functions of `ContDiffOn` on open sets cannot generally be extended to global `C¹` functions**: `x ↦ x⁻¹` on `(0, ∞)` is a standard counterexample. Therefore, one cannot "first extend then apply existing global theorems" in a single step. What actually holds is `exists_contDiff_one_eqOn_ball`: at each point there is a ball where it equals a certain global `C¹` function (multiplied by a `ContDiffBump` supported within `O`, differentiability being a local property). This is the requirement of the **localization within open sets**; it is **not** the Whitney extension on closed sets—that is a separate, unproven obligation **L6**, which remains untouched in this round.

Assembly: Second countability is obtained from the above ball family by extracting a countable subfamily that covers `O`; `disjointed` transforms it into a countable pairwise disjoint family of `S`
Measurable piecewise; `graphMap` Injective (with `graphMap_injective`) such that the images of each piecewise are pairwise disjoint,
The existing `measurableSet_image_graphMap` gives measurability of the image; both sides of the equality are countably additive over these pieces
(`lintegral_iUnion`), on each piece, use the existing global theorem acting on the local representative of that piece;
The gradients are equal because the two functions are equal on every open ball around each point (`Filter.EventuallyEq.gradient_eq`).

`Analysis/SmoothSard.lean` already has `C^∞` version `exists_contDiff_eventuallyEq` (conclusion is near a point,
`EventuallyEq`, without giving an explicit ball). **We deliberately leave it unchanged in this round**: extending it to general order or strengthening the conclusion would alter a previously published signature, so here we prove the required `C¹` version separately. The client's
`preserved_setLIntegral_image_graphChartMap` confirms the statement of the existing global theorem with named arguments.

## What was not done in this round

* **L9 (regular open domain C¹ coarea) unproven**: Still requires a C¹ implicit function family with level parameters `t`
  (not a fixed level set graph inclusion relationship), same-dimensional Jacobian change of variables and Tonelli, and cancellation of `|det DΦ| = |Du(e)|` and `√(1+‖D_yψ‖²) = ‖∇u‖/|Du(e)|`. L8 only provides area of the graph, not coarea.
* **L11, L12 unproven**; the weighted coarea identity remains a direct proof hole
  (`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and its specializations `C¹`).
  The direct proof hole remains as expected: **2/3/5**, total count **10**.
* **Whitney extension of L6/L6a/L7 remains unchanged**. The current localization is restricted to the interior of an open set, using bump functions only, and does not involve first-order jet extension over closed sets.
* The sharp `C^(finrank)` of `Analysis.sard` still carries `sorryAx`; the sharpness of `smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, equality of two Cheeger constants, and the sharpness of Eilenberg constants remain unproven.

## Verification

* `Analysis/OpenGraphIntegral.lean` compiles successfully with `-DwarningAsError=true` alone.
* `build/audit/OpenGraphAudit.lean` compiles with `-DwarningAsError=true`: 1 statements `#check`
  (The literal recitation of the route record L8) and 6 theorem—`target`, `global_case` (obtained from `O = univ` being globally derivable
  Theorem stating that L8 is a true generalization), `top_weight` (with weights constantly equal to `⊤`), `empty_parameter_set`,
  `inv_on_Ioi` (`x ↦ x⁻¹` at `(0, ∞)`, **no global `C¹` extension**, covered by no global theorem),
  A `preserved_*` named argument signature check—along with 9 `#print axioms`s.
  All  9 statements depend only on `propext`, `Classical.choice`, `Quot.sound`; **not on `sorryAx`**.
* Retrace `CriticalSliceAudit`, `LevelSetMeasurableAudit`, `BorelSliceAudit`,
  `CompactSliceAudit`, `EilenbergMajorantAudit`, `NullSlicingAudit`,
  `WeightedCoareaRouteStatements`, `WeightedCoareaInfrastructure`, `AreaFormulaAudit`,
  `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `SuperlevelSardScope`, `SmoothSardAudit`,
  `SmoothSardRouteStatements`, all strictly compiled successfully, no modifications made.
* Three WIP files were successfully compiled in practice, with direct proof holes respectively **2/3/5**, total **10**.
* Default `lake build` is connected to the root directory `python3 research/verify.py`. Final verification receipt is
  `build/verification/latest.json`, exactly equal to the final complete source code snapshot; evidence JSON is
  `research/explorations/2026-09-15-open-graph-area.json`, final verification and save
  `build/audit/opengraph-final-snapshot.json`. `build/` is gitignored, hence `build/audit`
  The hash is bound solely by evidence JSON.
* Certification still **24**, perimeter infrastructure still **missing**.
