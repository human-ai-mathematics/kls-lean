# 2026-09-13 — Gauss–Green Preliminaries: Divergence Formula on Smooth Subgraphs, Weighted Boundary Substitution, and Local Gauss–Green for Graphs

Owner requests completion of the next prerequisite for Gauss–Green: the local divergence integral formula on smooth subgraphs, completing the required weighted boundary integral change of variables and connecting `SmoothDomain.BoundaryChart`; direct implementation of proof and verification, no commit or push in this round. Acceptance
[boundary chart and area interface log](2026-09-13-boundary-chart-and-area-interface.md),
[Gauss–Green area formula record](2026-09-12-gauss-green-area-formula.md) and
[interface connection log](2026-09-12-perimeter-interface-integration.md). All previously unsubmitted module splitting, perimeter interface proofs,
graph area formula, local chart and outward normal formula remain intact, not reset, not overridden, not redundantly implemented; historical records retain original text and original counts.

## Conclusion first

| Goal | Status | Transitive Axioms |
| --- | --- | --- |
| 1. Divergence formula on globally smooth subgraph `Analysis.integral_divergence_subgraph` | **Completed** | Standard three lines |
| 2. Weighted boundary integral change of variables `Analysis.setIntegral_image_graphChartMap` / `setLIntegral_image_graphChartMap` | **Completed** | Standard three lines |
| 3. Chart-local Gauss–Green `BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal` | **Completed** (support restricted to a single chart column) | Standard three conditions |
| Global vector field Gauss–Green `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | **Incomplete**, still direct `sorry` | Contains `sorryAx` |
| Scalar Gauss–Green, `gradient_mollifiedIndicator_eq` | Proof body is filled, still reduced to vector form | contains `sorryAx` |

This round does not perform finite smooth partition of unity, does not close the complete Gauss–Green, does not advance coarea, Sard, or recover sequences.
The certificate count remains 24, with no new ledger nodes and no Blueprint `\lean`/`\leanok` anchor points,
The infrastructure status of `lem:relative-perimeter-smoothing` is still `missing`.
WIP direct hole total remains unchanged, still 20 (`RelativePerimeter` 3, `AnalyticPrerequisites` 4,
`CheegerInfimum` 8, `Energy/WIP/Cheeger` 5).

## 1. Divergence formula on subgraphs

### Statement

`FunctionalInequalities/Analysis/SubgraphDivergence.lean`, `Analysis.integral_divergence_subgraph`:
Let `H`, `V` be finite-dimensional real inner product spaces, and `hsp : IsGraphSplitting ι e` provide an orthogonal decomposition `V = ι H ⊕ ℝ e`,
`x₀ : V`, `g : H → ℝ` is `ContDiff ℝ 1`, `F : V → V` is a compact support `C¹` vector field. Let


`Ψ = graphChartMap ι e x₀ g`, `S = {x | graphHeight e x₀ x < g (graphCoord ι x₀ x)}`, then

```
∫_S divergence F = ∫_H ⟪F (Ψ y), ι (-(∇g y)) + e⟫ dy .
```

The right-hand side is the **unnormalized** normal flux: along the unit outward normal of the graph is `(ι(-∇g)+e)/√(1+‖∇g‖²)`, the graph Jacobian is exactly `√(1+‖∇g‖²)`, and the two mutually cancel in this expression, neither missing any tangential terms `ι(-∇g)` nor retaining an extra Jacobian factor.

Generality preserved: any orthogonal decomposition and any translation `x₀`; `g` as long as `C¹`, **no** global Lipschitz or bounded gradient required
(This round relaxes the assumption from owner's `C^∞` to `C¹`, with the conclusion unchanged); subgraphs and their boundaries can be unbounded; `F` only requires `C¹` compact support;
`H` can be zero-dimensional, in which case the conclusion reduces to the fundamental theorem of calculus on a one-dimensional half-line (verified by audit client 3).

### Path: Measure Splitting + Shearing + Trace Decomposition + FTC

**(a) Measure splitting, no Jacobian.** `splitIsometry` Identifies `WithLp 2 (H × ℝ)` linearly isometrically with `V`
(`LinearIsometryEquiv.ofSurjective`, the norm identity is given by Pythagoras `IsGraphSplitting.norm_add_smul_sq` and
`WithLp.prod_norm_sq_eq_of_L2`), so `splitHomeomorph (y,t) = x₀ + ι y + t • e` preserves measure
(`WithLp.volume_preserving_toLp` + `LinearIsometryEquiv.measurePreserving` + translation invariance).
Shearing `shearEquiv (y,s) = (y, s + g y)` preserves product measure: by applying Fubini `Measure.prod_apply`, and using per fiber
`measure_preimage_add_right`, it suffices that `g` is measurable (`measurePreserving_shearEquiv`). The composition yields
**Diagram `Ξ (y,s) = x₀ + ι y + (s + g y) • e`**, which is a homeomorphism and measure-preserving
(`measurePreserving_graphChartHomeomorph`), mapping the half-space `{s < 0}` to `S`.
**No** Jacobian determinant is computed, and no unproven Piola identity or general divergence theorem is referenced.

**(b) Trace decomposition of divergence, no basis.** `divergence_eq_tangentDiv_add`:

```
divergence F x = tangentDiv ι (DF x) + ⟪e, DF x e⟫,   tangentDiv ι M = tr_H (P ∘ M ∘ ι)
```

Here `P = graphProj ι` is the adjoint of `ι`. Write the identity map as `ι∘P + e⊗e`; for the normal component use
`Analysis/Divergence.lean` Existing rank-one trace identity `trace_smulRight`, the tangential part by


`LinearMap.trace_comp_comm'` (`tr_V (g∘f) = tr_H (f∘g)`). *Do not select an orthogonal basis*, thus handling zero-dimensional and high-dimensional cases uniformly.

(c) Pointwise identity. In chart coordinates, denote `T(y,s) = Ξ(y,s)`, then

```
divergence F (T(y,s)) = divergence (z ↦ P (F (T(z,s)))) y + d/ds ⟪e - ι(∇g y), F (T(y,s))⟫ .
```

Left side uses (b); right side first term uses chain rule `divergence_graphProj_comp` and
`graphTrace_comp_graphLinear`, yielding `tangentDiv ι (DF) + ⟪∇g y, P (DF e)⟫`; second term is obtained from
`∂_s T = e` to give `⟪e, DF e⟫ - ⟪∇g y, P (DF e)⟫`. The two `∇g` terms **exactly cancel**, which is precisely the source of the tangential `-∇g` term.
Here only `g ∈ C¹` is used: the `z ↦ P(F(T(z,s)))` property of the slice field `C¹` requires only that `T(·,s)` is `C¹`.

(d) Two-term integral. The tangential term integrates to zero over each fixed `s` on `H` (next section); the normal term is integrated along each fiber using the value `HasCompactSupport.integral_Iic_deriv_eq` to `s = 0` via `⟪e - ι(∇g y), F (Ψ y)⟫`. The replacement of `Iio 0` by `Iic 0` uses `Iio_ae_eq_Iic`. Fubini's integrability stems entirely from "continuity + compact support": the compact support is inherited via the homeomorphism `Ξ` (`HasCompactSupport.comp_homeomorph`), and the compact support of the slices and fibers is provided by `hasCompactSupport_comp_of_norm_le` (the parameter norm is controlled by the norm of the image).

### Divergence theorem for boundary-free domains: by induction on dimension

`Analysis.integral_divergence_eq_zero`: compact support `C¹` vector field `W : H → H` satisfies `∫_H div W = 0`.
The divergence theorem in Mathlib only covers rectangular boxes in `Fin (n+1) → ℝ`, so in this round of self-proof, the route is isomorphic to the main theorem,
without introducing additional `EuclideanSpace` coordinates:

* `finrank = 0`: The space is `Subsingleton`, `fderiv W y = 0`, with trace zero;
* `finrank = n+1`: Take the unit vector `u`, and use the newly added `Analysis/ImplicitGraph.lean`'s
  `isGraphSplitting_orthogonal` to obtain the decomposition `H = (ℝ∙u)ᗮ ⊕ ℝu`, `finrank (ℝ∙u)ᗮ = n`;
  By (b) decomposing the integrand, the normal component integrates to zero along each line by `integral_deriv_eq_zero`, while the tangential component integrates to zero for each fixed height by **inductive hypothesis** on `(ℝ∙u)ᗮ`; the integrability of both Fubini's steps also follows from compact support.

`isGraphSplitting_orthogonal` is the result of lifting the proof of `KLS/Geometry/BoundaryChart.lean`'s `isGraphSplitting_tangent` to the generic layer: the theorem name and statement remain unchanged, and the proof body is now a single call.
**No** duplicate proofs are retained, and no alias compatibility is preserved.

## 2. Weighted boundary integral substitution

The existing area formula `hausdorffNormalized_image_graphChartMap` is a *measure identity on a measurable parameter set*, and cannot be directly used as a change of variables for an arbitrary integrand. `FunctionalInequalities/Analysis/GraphIntegral.lean` Completes the required interfaces, and only adds the minimal generic interfaces needed for this round, without extending it into a general area or manifold integral library:

* `measurableSet_image_graphChartMap`: the image is measurable (obtained from the preimage expression of `Analysis/AreaFormula.lean` via `measurableSet_image_graphMap` and translation);
* `graphChartMap_injective_of_perp`: uses only the injectivity implied by orthogonality. The original `graphChartMap_injective (hsp)` retains its name and statement, and is now invoked, **without repeated proof**;
* `map_graphChartMap_withDensity` (core): for measurable `s`,

  ```
  map Ψ ((volume.withDensity √(1+‖∇g‖²)).restrict s) = ℋ^k ⌊ (Ψ '' s) ,
  ```

  Among which `k = finrank ℝ H`. Proof: For any measurable `E`, `(volume.withDensity J)(Ψ⁻¹E)` by the area formula equals
`ℋ^k (Ψ '' (Ψ⁻¹E)) = ℋ^k (E ∩ range Ψ)`, hence `map Ψ (volume.withDensity J) = ℋ^k ⌊ range Ψ`;
then apply `Measure.restrict_map` together with the *injectivity* `Ψ⁻¹(Ψ''s) = s` restricted to `s`;
* `setLIntegral_image_graphChartMap` (non-negative measurable integrand) and
`setIntegral_image_graphChartMap` (Bochner version, assuming only `AEStronglyMeasurable`):

  ```
  ∫_{Ψ '' s} f dℋ^k = ∫_s √(1+‖∇g y‖²) • f (Ψ y) dy .
  ```

  **No** assumption of integrability: `integral_map` and `integral_withDensity_eq_integral_smul` are both `0` when integrability fails,
the equality still holds. The parameter set, the image, and the restricted measure are all explicitly mentioned in the statement.

The Jacobian vanishes pointwise when used in Section 3 together with `BoundaryChart.outwardNormal_graph`:
`J • ⟪F, J⁻¹ • (ι(-∇g)+ν)⟫ = ⟪F, ι(-∇g)+ν⟫`, the denominator is strictly positive (`graphJacobian_pos`), not "almost everywhere nonzero".

## 3. Connect BoundaryChart: Local Gauss–Green of the chart

`FunctionalInequalities/KLS/Geometry/LocalGaussGreen.lean`,
`KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`:
for `U : SmoothDomain V`, `x₀ ∈ frontier U.carrier`, `C : U.BoundaryChart x₀`, and compactly supported `C¹` field `F`,
under the **explicit support condition `tsupport F ⊆ C.cylinder`**,


```
∫_U divergence F = ∫_{frontier U} ⟪F, U.outwardNormal⟫ ∂ surfaceMeasure V .
```

This is a **local version with support restricted to a single chart**, not a global theorem for arbitrary compactly supported fields.

### Handling of Access Details

* Localized at `F` and `divergence F` simultaneously holds. `tsupport F ⊆ C.cylinder` implies the column exterior `F` is identically zero in a neighborhood,
  Thus `fderiv F = 0`, `divergence F = 0` (`BoundaryChart.eq_zero_of_notMem_cylinder`,
  via the general lemma `Analysis.fderiv_eq_zero_of_notMem_tsupport`). This is precisely the condition ensuring that derivatives also vanish outside the cylinder.
* **Volume integral.** `integral_divergence_carrier`: the characteristic function of `U.carrier` and the **global** subgraph
  The characteristic function of `S = {x | graphHeight ν x₀ x < height (graphCoord ι x₀ x)}` is pointwise equal after multiplication by `divergence F`
  — The two sets are identical (`carrier_inter_cylinder`), outside the cylinder `divergence F = 0`. The two sets themselves are not equal:
  The graph of the global extension height function outside the cylinder is independent of `∂U`, and the equality holds only inside the cylinder; it is precisely the support condition that eliminates the difference.
  Then apply the subgraph formula from Section 1 to `S`.
* **Boundary integral.** `integral_inner_outwardNormal_frontier`: the integrand is zero outside `C.map '' C.param`
  — if `x ∈ frontier U` and `x ∉ C.map '' C.param`, then `x ∉ C.cylinder` (otherwise by
  (`frontier_inter_cylinder` falls into the image), hence `F x = 0`. Thus the boundary integral degenerates into **a single image**.
  By the change of variables in Section 2, then canceling the Jacobian using `outwardNormal_graph`; finally pull the parameter integral back from `C.param` to the entire tangent hyperplane.
  — At `y ∉ C.param`, `C.map y` is outside the cylinder (`BoundaryChart.map_notMem_cylinder`), the integrand is zero.
* The boundary integrability is not implicitly assumed. The set replacement is accomplished entirely through pointwise equality of characteristic functions.
  (`integral_indicator` twice), no integrability required; the substitution itself only requires measurability
  (`Measurable.inner` applied to continuous `F` and the already proved measurability of `outwardNormal`).
  Therefore, there is no assumption that `∂U` has finite total measure, nor that `U` is bounded or `V` nontrivial.
  Proved `isLocallyFiniteMeasure_surfaceMeasure_frontier` and `integrableOn_smul_outwardNormal`
  Still in place, not used in this round and not weakened.

## Modules and Scope

| Layer | module | content | hole |
| --- | --- | --- | ---: |
| General geometry | `Analysis/ImplicitGraph.lean` (existing, +1 declaration) | Add `isGraphSplitting_orthogonal`; change `graphChartMap_injective` to use the new `graphChartMap_injective_of_perp` | 0 |
| General geometry | `Analysis/SubgraphDivergence.lean` (new) | `splitIsometry`, `splitHomeomorph`, `shearEquiv`, `graphChartHomeomorph` and their measure-preserving properties; `hasCompactSupport_comp_of_norm_le`, `fderiv_eq_zero_of_notMem_tsupport`; `graphTrace`/[`tangentDiv`] and divergence decomposition; `integral_deriv_eq_zero`, `integral_divergence_eq_zero`; `integral_divergence_subgraph` | 0 |
| General geometry | `Analysis/GraphIntegral.lean` (new) | `measurableSet_image_graphChartMap`, `map_graphChartMap_withDensity`, two integral substitutions | 0 |
| Application layer | `KLS/Geometry/BoundaryChart.lean` (existing) | `isGraphSplitting_tangent` changed to invoke the general lemma, name and statement unchanged | 0 |
| Application layer | `KLS/Geometry/LocalGaussGreen.lean` (new) | Two localizations lemmas and chart-local Gauss–Green | 0 |
| In progress WIP | `KLS/WIP/AnalyticPrerequisites.lean` | Only missing global Gauss–Green (lacks partition of unity), coarea, Sard; this round only updates module descriptions | 4 |

Directional dependency acyclic:

```
Analysis/AreaFormula → Analysis/ImplicitGraph → {Analysis/SubgraphDivergence, Analysis/GraphIntegral}
Analysis/ImplicitGraph → KLS/Geometry/BoundaryChart → KLS/Geometry/LocalGaussGreen
```

`Analysis/` has no `sorry`; the official aggregation entry (library root) and 24 certificates do not import these modules, and the default `lake build` 3393 jobs remain unchanged. No new axioms are added, no `sorry` is hidden, no conclusions are weakened, no substantive assumptions are introduced, no alias compatibility or duplicate proofs are added.

## Counting (recount for this round)

* **Definition**: Added 6 items (`splitIsometry`, `splitHomeomorph`, `shearEquiv`, `graphChartHomeomorph`,
  `graphTrace`, `tangentDiv`), all located in `Analysis/SubgraphDivergence.lean`.
* **Public theorems**: `Analysis/SubgraphDivergence.lean` 26 items (plus 1 items `private` via induction carrier `integral_divergence_aux`), `Analysis/GraphIntegral.lean` 4 items,
  `KLS/Geometry/LocalGaussGreen.lean` 5 items, for a total of **35 new public theorems + 6 new definitions**;
  `Analysis/ImplicitGraph.lean` net gain of 2 public theorems
  (`isGraphSplitting_orthogonal`, `graphChartMap_injective_of_perp`).
  No `sorry`, no transitive `sorryAx`.
* **WIP direct hole**: Still at **20** (3 / 4 / 8 / 5), all four files were actually re-elaborated, exited 0,
  diagnosis precisely identifies these 20 items `declaration uses 'sorry'`, with no other warnings or errors. **This is not a strict mode pass.**
* **Transitive `sorryAx`**: Count of `AnalyticPrerequisites` remains unchanged—9 theorems, 0 definitions,
  5 proofs completed, 4 direct holes, among the completed 5 items, only 2 lack transitive `sorryAx`.
  `integral_divergence_eq_integral_inner_outwardNormal`,
  `setIntegral_gradient_eq_integral_smul_outwardNormal`, `gradient_mollifiedIndicator_eq`,
  `sard`, `ae_forall_fderiv_ne_zero`, two coarea still contain `sorryAx`.

## Verification

* **Direct axiom check** (only allows `propext / Classical.choice / Quot.sound`):
  `Analysis.integral_divergence_subgraph`, `Analysis.integral_divergence_eq_zero`,
  `Analysis.integral_deriv_eq_zero`, `Analysis.divergence_eq_tangentDiv_add`,
  `Analysis.divergence_graphProj_comp`, `Analysis.graphTrace_comp_graphLinear`,
  `Analysis.measurePreserving_splitHomeomorph`, `Analysis.measurePreserving_shearEquiv`,
  `Analysis.measurePreserving_graphChartHomeomorph`,
  `Analysis.integral_comp_graphChartHomeomorph`, `Analysis.isGraphSplitting_orthogonal`,
  `Analysis.map_graphChartMap_withDensity`, `Analysis.setLIntegral_image_graphChartMap`,
  `Analysis.setIntegral_image_graphChartMap`, `Analysis.measurableSet_image_graphChartMap`,
  `Analysis.graphChartMap_injective_of_perp`, `Analysis.graphChartMap_injective`,
  `KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`,
  `…integral_divergence_carrier`, `…integral_inner_outwardNormal_frontier`,
  `…eq_zero_of_notMem_cylinder`, `…map_notMem_cylinder`,
  and the reconstructed `KLS.SmoothDomain.isGraphSplitting_tangent`, `exists_boundaryChart`,
  `BoundaryChart.surfaceMeasure_image` —— All there are just the three standard ones.
  `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`,
  `setIntegral_gradient_eq_integral_smul_outwardNormal`, `gradient_mollifiedIndicator_eq` still contain
  `sorryAx` (as in the table above).
* **Independent client**: `build/audit/SubgraphDivergenceAudit.lean` (ignore directory, `lake env lean` directly
  elaborate, does not increase `lake build`, replay sets or certification closure). Six client theorems:
  1. `client_flat_flux`: The formula on the flat subgraph yields `∫_H ⟪F(x₀+ι y), e⟫`;
  2. `client_flat_flux_sign`: If the field points toward `+e` along the boundary, then the total divergence is non-negative——**a substantive test of direction convention**,
     Agreement of opposite inequalities means negation of the sign;
  3. `client_tilted_tangential`: tilted linear diagram `g y = ⟪c,y⟫` with a **pure tangential** field `η • ι c`,
     The normal component `⟪F, e⟫` is always zero, given by the formula `-‖c‖² ∫ η∘Ψ`—**omitting the `-∇g` term yields 0**;
  4. `client_one_dimensional`: Take `V = ℝ`, the tangent space `(ℝ∙1)ᗮ` (zero-dimensional), the formula degenerates into
     `∫_{(-∞,b)} F' = F b`, where `divergence = deriv` (one-dimensional trace) and the zero-dimensional space `volume univ = 1` were also verified;
  5. `client_local_gaussGreen_halfSpace`: the half-space `{⟪a,x⟫<0}` as `SmoothDomain`,
     For fields whose supports lie within a certain chart column, the local Gauss–Green gives
     `∫_U div F = ∫_{{⟪a,x⟫=0}} ⟪F, a⟫ ∂surfaceMeasure`, the outer normal is a **concrete `+a`**;
  6. `client_halfSpace_chart_exists`: This assumption is nonempty.
  The transitive axioms of six are only the standard three. The upper three rounds' `AreaFormulaAudit.lean`, `BoundaryChartAudit.lean`,
  `PerimeterInterfaceAudit.lean` rerun, the conclusion remains unchanged from the axioms.
* **Strict mode**: `Analysis/SubgraphDivergence.lean`, `Analysis/GraphIntegral.lean`,
  `Analysis/ImplicitGraph.lean`, `KLS/Geometry/BoundaryChart.lean`,
  `KLS/Geometry/LocalGaussGreen.lean` and four audit clients in `lake env lean -DwarningAsError=true`
  Exit below 0.
* **WIP with a hole**: four files in normal mode actually re-elaborated, exit 0, diagnosis is exactly as expected 3 / 4 / 8 / 5
  `declaration uses 'sorry'`, no other warnings or errors. This is not a strict mode pass.
Complete default `lake build` (3393 jobs, same as previous round—new modules not in library root aggregation), and run from repository root
  `python3 research/verify.py`; `lem:relative-perimeter-smoothing`'s infrastructure evidence hash per round
  Recompute the source code and add three new modules, synchronize note and gaps updates, status remains `missing`. Final verification receipt by
  `build/verification/latest.json` points to, matching the final source code snapshot.

Evidence of trust in fixed-version third-party compiled dependencies does not imply independent reconstruction of Mathlib, remote CI, or Blueprint formatting passes.
Audit scripts and logs remain in the ignored `build/`. This round does not submit or push as required by the owner.

## What remains for the full Gauss–Green theorem

**Only partition of unity gluing remains.** Specifically: for a compactly supported `C¹` field `F`, take a finite atlas chart column cover of `tsupport F ∩ frontier U`
(each boundary point is assigned a column via `exists_boundaryChart`), together with the open sets `U` and `(closure U)ᶜ`,
construct a finite smooth partition of unity `{χ_i}` subordinate to this cover, and decompose `F = Σ_i χ_i F`; each `χ_i F` either has its support contained within some chart column (by the local theorem in this round), or its support intersects none of `frontier U` (in which case both sides degenerate: the interior piece uses the same technique from `Analysis.integral_divergence_eq_zero`, and the exterior piece vanishes on both sides). The derivative terms of the decomposition functions cancel out in the sum `Σ_i ∇χ_i = 0`. Mathlib provides `SmoothPartitionOfUnity`/`ContDiffBump` as input.

coarea, Sard, and the recovery sequence remain independently open thereafter.
