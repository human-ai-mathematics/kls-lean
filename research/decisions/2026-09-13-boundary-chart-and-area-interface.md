# 2026-09-13 — Gauss–Green Preliminaries: Local Smooth Graph Representations, Domain Sides, Outer Normal Formula, and Graph Area Interface

Owner requests completion of the next prerequisite task for Gauss–Green: `SmoothDomain` local smooth graph representations near boundary points, side-specific and outer normal formulas, and connecting the results to the existing codimension-one graph area formula; direct implementation of proof and verification, no commit or push in this round. Takes over
[Gauss–Green area formula record](2026-09-12-gauss-green-area-formula.md),
[interface integration record](2026-09-12-perimeter-interface-integration.md), and
[current state audit](2026-09-12-status-audit-and-wip-retention.md). All modules split from the previous round, three interface proofs,
graph area formula, and divergence identity remain intact, not reset or rewritten; historical records retain original text and count.

## Conclusion first

| Goal | Status | Transitive Axioms |
| --- | --- | --- |
| 1. Boundary point near `C^∞` diagram representation (including regional distinction, parametrization injectivity and inverse parametrization) | **Completed** | Standard three conditions |
| 2. Outer normal formula in graph coordinates (with positive denominator, sign determined) | **Completed** | Standard three lines |
| 3. Local diagram and existing area formula interface (local boundary slice equation of `surfaceMeasure`) | **Completed** | Standard three lines |
| vector field Gauss–Green `integral_divergence_eq_integral_inner_outwardNormal` | **incomplete**, still direct `sorry` | contains `sorryAx` |
| scalar Gauss–Green, `gradient_mollifiedIndicator_eq` | proof body is filled, still reduced by C1 | contains `sorryAx` |

This round has no proof of the complete Gauss–Green, subgraph Fubini/FTC identity, partitioning by partition of unity, coarea, Sard, or recovery of sequences.
The certificate count remains 24, with no new ledger nodes and no Blueprint `\lean`/`\leanok` anchor points,
The infrastructure status of `lem:relative-perimeter-smoothing` is still `missing`.
WIP direct hole total remains unchanged, still 20.

## 1. Local `C^∞` graph representation

### Mathematical content

Let `V` be a finite-dimensional real inner product space, `U : SmoothDomain V`, `x₀ ∈ frontier U.carrier`. Take
`ν = U.outwardNormal x₀` (`‖ν‖ = 1`), `H = (ℝ ∙ ν)ᗮ` to be a tangent hyperplane, `ι = H.subtypeₗᵢ` the natural isometric embedding.
Then there exists a global `C^∞` `g : H → ℝ`, a parameter open neighborhood `Ω ∋ 0`, and a semi-height `δ > 0`, such that in the cylindrical neighborhood

```
Cyl = { x | graphProj ι (x - x₀) ∈ Ω ∧ |⟪ν, x - x₀⟫| < δ }
```

Internal:

* `frontier U.carrier ∩ Cyl = Ψ '' Ω`, where `Ψ y = x₀ + ι y + g y • ν`
  (set equality, not "boundary contained in the graph");
* `U.carrier ∩ Cyl = { x ∈ Cyl | ⟪ν, x - x₀⟫ < g (graphProj ι (x - x₀)) }`
  (the region is exactly the side below the graph);
* `g 0 = 0` (center point normalized), `∀ y ∈ Ω, |g y| < δ` (the graph does not touch the cylinder wall).

Parameterized interface provided together: `Ψ` injective (`BoundaryChart.injective_map`), inverse parameter map is `tangentCoord x₀ x = graphProj ι (x - x₀)`, satisfying `tangentCoord x₀ (Ψ y) = y`
(`BoundaryChart.tangentCoord_map`), `Ψ '' s ⊆ frontier U ∩ Cyl` (`image_subset_frontier`),
`Cyl` open (`isOpen_cylinder`).

Lean is packaged as `KLS.SmoothDomain.BoundaryChart U x₀` structure, existence is
`KLS.SmoothDomain.exists_boundaryChart`. The general part is `Analysis.GraphRepr` and
`Analysis.exists_graphRepr` (for any `C^∞` of `φ`, `φ x₀ = 0`, `gradient φ x₀ = c • e`, `c > 0`).

### Regularity route: inverse function theorem, not implicit function theorem

Mathlib's `HasStrictFDerivAt.implicitFunctionOfComplemented` provides only strict differentiability at a point, and the area formula requires `C¹` over a neighborhood. This round applies the inverse function theorem: for

```
Φ x = ι (graphProj ι (x - x₀)) + φ x • e          (Analysis.flattenChart)
```

`Φ` global `C^∞` , `Φ x₀ = 0` , `DΦ(x₀) = flattenCLM ι e c` , its explicit inverse is `flattenCLM ι e c⁻¹`
(`Analysis.flattenEquiv`, constructed from `ContinuousLinearEquiv.equivOfInverse`, with the inverse equality on each side written in one line).
Thus `ContDiffAt.toOpenPartialHomeomorph` yields a local homeomorphism `F`.

A key step is to replace the pointwise conclusion of `ContDiffAt.to_localInverse` with a neighborhood conclusion: the set of invertible operators is open
(`ContinuousLinearEquiv.isOpen`), `x ↦ fderiv ℝ Φ x` is continuous, so
`N = F.source ∩ (fderiv Φ) ⁻¹' range (↑)` is open and contains `x₀`; `T = F.target ∩ F.symm ⁻¹' N` is open
(`OpenPartialHomeomorph.isOpen_inter_preimage_symm`) and contains `0`. For each point in `T`, we can apply
`OpenPartialHomeomorph.contDiffAt_symm`, so `F.symm` is pointwise `ContDiffAt ℝ ∞` on the entire `T`.
Take `Ω₀ = ι ⁻¹' T`, `g₀ y = ⟪e, F.symm (ι y) - x₀⟫`, and from `Φ (F.symm (ι y)) = ι y` take the `⟪e, ·⟫` component to get
`φ (F.symm (ι y)) = 0`, and take the tangential component to get `F.symm (ι y) = x₀ + ι y + g₀ y • e`.
This is `Analysis.exists_local_implicit`.

### Proof of the side property

On the open set of `⟪∇φ, e⟫ > 0`, take a ball `B(x₀, r)` (also lying within the given neighborhood `N₀`), let `δ = r/2`,
`Ω ⊆ ball(0, min(ρ, r/2)) ∩ {|g| < δ}`. Each point in the cylinder satisfies `‖x - x₀‖² = ‖y‖² + t² < r²` (Pythagorean,
`IsGraphSplitting.norm_add_smul_sq`), hence `Cyl ⊆ B(x₀, r)`. For fixed `y ∈ Ω`,
`h(u) = φ(x₀ + ι y + u • ν)` has derivative `= ⟪∇φ(·), ν⟫ > 0` on `Icc (-δ) δ`,
`strictMonoOn_of_deriv_pos` yields strict monotonicity; `h (g y) = 0`, thus

```
φ x < 0  ↔  t < g y        φ x = 0  ↔  t = g y
```

Both are `↔`, so `{φ = 0} ∩ Cyl` and `{φ < 0} ∩ Cyl` are both **equalities** rather than inclusions.
Then use the existing `SmoothDomain.frontier_inter_eq` and the definition `U ∩ W = {φ < 0} ∩ W` (taking `N₀ = W`, so `Cyl ⊆ W`) to convert the statement about `φ` into a statement about `U`; the conclusion does not depend on which definition function was chosen.

### 0-dimensional

`Nontrivial V` No assumption is added to any statement. In zero dimensions (more generally `Subsingleton V`), every set is both open and closed, and the boundary of a smooth region is empty, so all statements under the premise of `x₀ ∈ frontier U.carrier` are vacuously true; the need for non-degeneracy (as in `finrank_tangentSpace`'s `ν ≠ 0`) is derived from `‖ν‖ = 1`, not an additional assumption.

## 2. Outer normal formula

`KLS.SmoothDomain.BoundaryChart.outwardNormal_graph`: for `y ∈ Ω`,

```
U.outwardNormal (Ψ y) = (√(1 + ‖∇g y‖²))⁻¹ • (ι (-(∇g y)) + ν)
```

Division is written in Lean as scalar multiplication of vectors `(graphJacobian (gradient g y))⁻¹ • (…)`;
`graphJacobian a = √(1 + ‖a‖²) > 0` is given by `Analysis.graphJacobian_pos` (`positivity`),
that is, the denominator is always positive, not just "nonzero".

The proof is divided into two parts, both placed at the generic level:

* `Analysis.gradient_eq_smul_of_graph`: `φ ∘ Ψ ≡ 0` on the open set `Ω`, hence
  `fderiv φ (Ψ y) ∘ DΨ(y) = 0`; `DΨ(y) v = ι v + ⟪∇g y, v⟫ • ν`, taking `v` over `H` yields
  `graphProj ι (∇φ(Ψ y)) = β • (-(∇g y))`, where `β = ⟪∇φ(Ψ y), ν⟫`; then using orthogonal decomposition
  `a = ι (graphProj ι a) + ⟪ν, a⟫ • ν` gives `∇φ(Ψ y) = β • (ι (-(∇g y)) + ν)`.
* `Analysis.norm_inv_smul_eq_graphJacobian_inv_smul`: `β > 0` normalized
  `‖a‖⁻¹ • a = (graphJacobian b)⁻¹ • (ι (-b) + ν)`, using
  `‖ι(-b) + ν‖² = ‖b‖² + 1` (Pythagorean).

**The symbols are well-defined, not just "differing by a sign"**: `β = ⟪∇φ(Ψ y), ν⟫ > 0` is guaranteed throughout the column by the structural field
`GraphRepr.inner_gradient_pos` , which originates from `ν` , consisting of the normalized direction of `∇φ(x₀)` plus continuity; the same positivity serves as the basis for the monotonicity on the side in Section 1, both relying on the same fact, and the direction convention does not lead to contradiction.

**Gradient explanation**: `g` is a **global** `C^∞` function (see below), `∇g y` is its Mathlib `gradient` at `y`,
there is no distinction between "local gradient" and "extended gradient" as two separate objects.

## 3. Interface for local charts and area formulas

### Approach: Truncation within the representation theorem, delivering global `C^∞` `g`

The existing `Analysis.hausdorffNormalized_image_graphMap` requires `ContDiff ℝ 1 g` (globally), while the inverse function theorem only provides smoothness in a neighborhood. Of the two candidate approaches, this round selects **the second one**: shrink the parameter neighborhood and construct a global smooth extension.

The specific implementation is written internally in `Analysis.exists_graphRepr`, not left to the caller:

1. Take `ρ > 0` such that `closedBall (0, 2ρ) ⊆ Ω₀` (where `Ω₀` is the smooth neighborhood given by the inverse function theorem);
2. Take `ContDiffBump (0 : H)`, `rIn = ρ`, `rOut = 2ρ`, and define `g = χ · g₀`;
   `g` is globally `C^∞`: it is the product of two `ContDiffAt`s inside `Ω₀`, and `χ ≡ 0` outside `closedBall(0,2ρ)`, hence `g ≡ 0`
   On an open set, the two types of points cover the entire space;
3. The parameter set `Ω ⊆ ball(0, min(ρ, r/2))`, where `χ ≡ 1`, thus `g = g₀`.

Thus, the `BoundaryChart.height` delivered to the caller is itself a global `C^∞` (structural field `contDiff_height : ContDiff ℝ ∞ height`). **The local `ContDiffOn` is not treated as global `ContDiff`, nor is "existence of a global extension" assumed as an additional hypothesis**: the extension is constructed, and the function and its derivative are consistent within the required region (on `Ω`, `g = g₀`, `Ω` open, hence the gradient is also consistent). The area formula itself is not weakened or rewritten.

### `x₀` Measure invariance under translation

The graph map is `graphMap ι e g y = ι y + g y • e`, with no translation term, while the boundary piece is
`Ψ y = x₀ + graphMap ι e g y`. New `Analysis.hausdorffNormalized_image_add_left`:
Translation is isometry, `Isometry.hausdorffMeasure_image` eliminates it, `hausdorffNormalized` is merely a constant multiple of `μH`,
thus `Analysis.hausdorffNormalized_image_graphChartMap` transfers the area formula verbatim to `Ψ`.

### Final equation towards `SmoothDomain`

`KLS.SmoothDomain.BoundaryChart.surfaceMeasure_image`: for a **measurable parameter set** `s`,

```
surfaceMeasure V (Ψ '' s) = ∫⁻ y in s, ENNReal.ofReal (√(1 + ‖∇g y‖²)) ∂volume
```

The integral over the right-end tangent space `H = (ℝ ∙ ν)ᗮ` is `volume`, the Jacobian is `graphJacobian (∇g y)`.
The conversion of indices is `finrank_tangentSpace`: `finrank ℝ H = finrank ℝ V - 1`, together with
`surfaceMeasure V = hausdorffNormalized V (finrank ℝ V - 1)`.

`BoundaryChart.surfaceMeasure_frontier_inter_cylinder` Provide a precisely bounded version:

```
surfaceMeasure V (frontier U.carrier ∩ Cyl) = ∫⁻ y in Ω, ofReal (√(1 + ‖∇g‖²)) ∂volume
```

The left-hand side is **the boundary covered by a single chart** (the portion within the cylinder), not the entire boundary; the distinction is fixed by the set equation in `frontier_inter_cylinder` and the explicit appearance of `param`.

## Module Organization and Dependency Splitting

| Layer | module | content | hole |
| --- | --- | --- | ---: |
| General geometry | `Analysis/ImplicitGraph.lean` (new) | Orthogonal decomposition `IsGraphSplitting`, flattening diagram `flattenChart`, local implicit function `exists_local_implicit`, diagram parameterization and cylinders, gradient formula along diagram, `GraphRepr` and `exists_graphRepr`, area formula under translation | 0 |
| Application layer | `KLS/Geometry/BoundaryChart.lean` (new) | Migrated `outwardNormal` and its four proven lemmas; tangent hyperplanes `tangentSpace`/`tangentEmbedding`/`tangentCoord`, `isGraphSplitting_tangent`, `finrank_tangentSpace`; `BoundaryChart` and `exists_boundaryChart`; two `surfaceMeasure` equality equations | 0 |
| Incomplete WIP | `KLS/WIP/AnalyticPrerequisites.lean` | Remaining only Gauss–Green, coarea, Sard | 4 |

`outwardNormal` Originally coexisted with incomplete Gauss–Green at `AnalyticPrerequisites`, and the boundary graph representation is
the **input** of Gauss–Green, and must appear below it, so a minimal dependency splitting was performed: migrating each of `outwardNormal`,
`outwardNormal_eq`, `norm_outwardNormal`, `continuousOn_outwardNormal`,
`measurable_outwardNormal` word-for-word into `KLS/Geometry/BoundaryChart.lean`, with unchanged names, name spaces, and statements,
without compatibility aliases, without duplicate proofs, without forward declarations; the sole consumer `AnalyticPrerequisites` has been changed to import the new module.
`SmoothDomain` The structure itself has **not** been moved (that was not required in this round), so `BoundaryChart` imports
`SmoothDomain` and `frontier_inter_eq` via import of `KLS/WIP/RelativePerimeter.lean`; it does not use the three incomplete proofs in that file, `#print axioms` has been verified. There is no cyclic dependency:

```
Analysis/LevelSet → Analysis/AreaFormula → Analysis/ImplicitGraph
KLS/Geometry/SurfaceMeasure → Analysis/LevelSet → KLS/WIP/RelativePerimeter → KLS/Geometry/BoundaryChart → KLS/WIP/AnalyticPrerequisites
```

`Analysis/` introduces no `sorry`; the formal aggregation entry (library root) and 24 certificates do not import these modules.
No new axioms, no hidden `sorry`, no weakening of conclusions or reduction of mathematical scope: no statement assumes `U` to be bounded,
The total boundary measure is finite or `V` nontrivial.

## Counting (recounting this round, not carrying over old numbers)

* WIP direct hole total remains at **20**: `RelativePerimeter` 3, `AnalyticPrerequisites` 4,
  `CheegerInfimum` 8, `Energy/WIP/Cheeger` 5. All four files were actually re-elaborated, exited 0,
  diagnosis exactly matches the 3 / 4 / 8 / 5 `declaration uses sorry`s, no other warnings or errors.
* After `AnalyticPrerequisites` migrated out 5 declarations: **9 public theorems, 0 definitions; 5 proofs filled, 4 direct
  holes; among the 5 filled ones, only 2 have no transitive `sorryAx`**
  (`isLocallyFiniteMeasure_surfaceMeasure_frontier`, `integrableOn_smul_outwardNormal`).
* `KLS/Geometry/BoundaryChart.lean`: 23 public declarations (of which 5 were migrated in), all without `sorry`.
* `Analysis/ImplicitGraph.lean`: 58 public declarations, all without `sorry`.

### Correction to Previous Counting

The previous entry wrote: "After `AnalyticPrerequisites` migrated out `divergence`, there are 12 obligations, 8 with proof bodies filled, among which 6 have no transitivity `sorryAx`". The definition `divergence` **defined** was removed from the count of **theorems**. The correct numbers before migration were
**13 public theorems + 1 definitions (`outwardNormal`)**, among which 9 theorems had proof bodies filled, 4 had direct holes, and 6 theorems without transitivity `sorryAx`. Historical record
[2026-09-12 Gauss–Green area formula](2026-09-12-gauss-green-area-formula.md) and
the corresponding paragraph in `research/verification.md` remain unchanged in the original text; corrections are handled by this record and the module description in `KLS/WIP/AnalyticPrerequisites.lean`, while `research/verification.md` starts a new entry for the current status.

## Verification

* **Direct axiom check** (only allows `propext / Classical.choice / Quot.sound`):
  `Analysis.exists_local_implicit`, `Analysis.exists_graphRepr`,
  `Analysis.gradient_eq_smul_of_graph`, `Analysis.GraphRepr.normalized_gradient_map`,
  `Analysis.GraphRepr.zeroSet_inter_cylinder`, `Analysis.GraphRepr.sublevel_inter_cylinder`,
  `Analysis.hausdorffNormalized_image_graphChartMap`,
  `KLS.SmoothDomain.isGraphSplitting_tangent`, `KLS.SmoothDomain.finrank_tangentSpace`,
  `KLS.SmoothDomain.exists_boundaryChart`,
  `KLS.SmoothDomain.BoundaryChart.surfaceMeasure_image`,
  `KLS.SmoothDomain.BoundaryChart.surfaceMeasure_frontier_inter_cylinder`, and after migration
  `outwardNormal_eq`, `norm_outwardNormal`, `continuousOn_outwardNormal`,
  `measurable_outwardNormal` —— All there are just the three standard ones.
  `integral_divergence_eq_integral_inner_outwardNormal`,
  `setIntegral_gradient_eq_integral_smul_outwardNormal`, `gradient_mollifiedIndicator_eq`,
  `sard`, `ae_forall_fderiv_ne_zero`, two coarea still contain `sorryAx` (as in the above table).
* **Independent client**: `build/audit/BoundaryChartAudit.lean` (ignore directory, `lake env lean` directly
  elaborate, does not increase `lake build`, replay sets or certification closure). Eight client theorems use **concrete models with testable directions**:
  Half-space `{⟪a,x⟫ < 0}` (unit `a`) and the unit ball.
  1. The outward normal of the half-space is `+a` (not `-a`);
  2. The **statement** (without construction process) implied by only graphical representations deduces that the height function of any chart in a half-space is constantly `0` on the parameter set.
     The gradient is also `0`;
  3. The normal formula of the chart is computed as `+a`;
  4. Moving from `x₀` along `-ν` stays inside the region and strictly below the graph; moving along `+ν` leaves the region and lies strictly above the graph
     — This is a substantive test of the direction convention; if the direction is reversed, the two conclusions will be interchanged;
  5. The `surfaceMeasure` of the flat boundary slice equals the Lebesgue measure of the parameter set (normalized interface, Jacobian = 1);
  6. Charts exist on flat models;
  7. The outward unit normal at boundary points `x₀` is `+x₀` (direction check on curved models);
  8. There exists a graph on the unit ball.
  The transitive axioms of eight have only the standard three. The `AreaFormulaAudit.lean` and upper two rounds'
  `PerimeterInterfaceAudit.lean` rerun, the conclusion remains unchanged from the axioms.
* **Strict mode**: `Analysis/ImplicitGraph.lean`, `KLS/Geometry/BoundaryChart.lean` and three audit clients
  Exit 0 under `lake env lean -DwarningAsError=true`.
* **WIP with a hole**: four files in normal mode actually re-elaborated, exit 0, diagnosis is exactly as expected 3 / 4 / 8 / 5
  `declaration uses sorry`, no other warnings or errors. This is not a strict mode pass.
Complete default `lake build` (3393 jobs), and run `python3 research/verify.py` from the repository root;
  The infrastructure evidence hashes for `lem:relative-perimeter-smoothing` are recomputed from this round’s sources, and the two new modules are added,
  note Synchronized with gaps, status remains `missing`. Final verification receipt pointed by `build/verification/latest.json`,
  Matches the final code snapshot.

Evidence of trust in fixed-version third-party compiled dependencies does not imply independent reconstruction of Mathlib, remote CI, or Blueprint formatting passes.
Audit scripts and logs remain in the ignored `build/`. This round does not submit or push as required by the owner.

## What remains of the distance Gauss–Green

1. **Local Gauss–Green on a subgraph**: By `V ≃ₗᵢ WithLp 2 (H × ℝ)` Fubini, the normal component is expressed via the fundamental theorem of calculus,
   The tangential component requires differentiation of the variable upper limit integral `y ↦ ∫_{-∞}^{g y} F_i` via Leibniz rule, then integration of the entire expression to zero.
   The required local `C^∞` charts are now available (`exists_boundaryChart`).
2. **Smooth partition of unity**: A finite smooth partition of unity with compact support, used to glue local identities together and cancel the derivative terms of the decomposition functions;
   Then synthesize with `BoundaryChart.surfaceMeasure_image` to obtain a vector field form.
3. Afterward, coarea, Sard, and recovery sequences remain independently open.
