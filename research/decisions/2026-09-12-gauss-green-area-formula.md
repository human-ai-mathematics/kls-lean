# 2026-09-12 — Gauss–Green advancement: codimension one area formula proven, divergence theorem not closed

Owner requests progress on the two Gauss–Green objectives `KLS/WIP/AnalyticPrerequisites.lean` and completion of actual proofs and verification,
lifting the "retained sorry" restrictions on these two objectives in this round, while keeping all other open objectives unchanged; no commit, no push. Take over
[interface integration record](2026-09-12-perimeter-interface-integration.md),
[outward normal proof record](2026-09-12-outward-normal-interfaces-proofs.md) and
[outward normal closeout](2026-09-12-outward-normal-interfaces-closeout.md); all module decompositions and three interface proofs not committed in the previous round are retained, not reset or rewritten. Historical records maintain their original meaning and count.

## Conclusion first: neither of the two goals has been completed

| Goal | Status | Transitive Axioms |
| --- | --- | --- |
| `SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` (C1, vector field form) | **Incomplete**, still a direct `sorry` | contains `sorryAx` |
| `SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal` (C2, scalar test form) | Proof body is filled, but **derived from C1 reduction** | contains `sorryAx` |
| `SmoothDomain.gradient_mollifiedIndicator_eq` | proof body is filled | contains `sorryAx` (via C2 via C1) |

Therefore, the owner's requirement that "the hole of Gauss–Green has disappeared from the dependency chain of `gradient_mollifiedIndicator_eq`" is **not met**, and a completion report cannot be issued. C1 remains the only independent Gauss–Green obligation.

## This round's actual mathematical proof (without `sorry`, using standard axioms)

### 1. Co-dimension one area formula (new module `Analysis/AreaFormula.lean`, approximately 950 lines)

Let `H`, `V` be finite-dimensional real inner product spaces, `ι : H →ₗᵢ[ℝ] V` a linear isometry, `e : V` a unit vector and orthogonal to the image of `ι`,
`g : H → ℝ` is `C¹`, the graph mapping `Ψ y = ι y + g y • e`, Jacobian `J a = √(1 + ‖a‖²)`. Then for any measurable `s`:

* `Analysis.hausdorffMeasure_image_graphMap`: `μH[k] (Ψ '' s) = ∫⁻_s ofReal (J (∇g y)) ∂μH[k]`;
* `Analysis.hausdorffNormalized_image_graphMap`: normalized version, integrated against `volume` on the right end,
  That is, `ℋ^k(graph) = ∫_s √(1+‖∇g‖²)`, exactly the normalization used by `surfaceMeasure` in the perimeter chain.

`k = finrank ℝ H` Arbitrary (including 0); `s` need not be bounded, the total measure of the graph can be infinite; no Lipschitz or bounded gradient assumptions.

Proof structure:

* **Linear case** (`hausdorffMeasure_image_graphLinear`). Decompose the linear map with slope `a = r • u` (`u` units) into `graphLinear ι e a = shearCLM ∘ dilate`: `dilate u c` (`c = √(1+r²)`) is a scaling along `u` on `H`, and `shearCLM` is a linear **isometry** of `H → V`. Thus, the isometry invariance of Hausdorff measure (`Isometry.hausdorffMeasure_image`) cancels `shearCLM`, and `Measure.addHaar_image_linearMap` with `det (dilate u c) = c` (after taking an orthogonal basis with `u` as the first vector, resulting in a diagonal matrix) yields a constant `c = J a`. The conversion from `μH[k]` to `volume` uses the previous round's `Analysis.hausdorffMeasure_finrank_eq_smul_volume`.
  **No** need for polar decomposition, SVD, or general linear area formulas.
* **`C¹` case**. Three steps:
  (a) Local linearization: on a ball where variation of `∇g` ≤ ε, the mean value inequality gives `ApproximatesLinearOn Ψ (graphLinear ι e (∇g y₀)) t ε` (the ball is convex); use `SecondCountableTopology.countable_cover_nhds` to take a countable cover of balls, then `disjointed` yields a countable disjoint measurable partition.
  (b) Sandwich: `Ψ` and `graphLinear` are mutual `(1+ε)`-Lipschitz reparametrizations (both `Ψ` and `graphLinear` do not contract, `‖y-y'‖ ≤ ‖Ψ y - Ψ y'‖`), so the `μH[k]` on both sides differ by a factor `(1+ε)^k` (`LipschitzOnWith.hausdorffMeasure_image_le`). `Ψ` is injective with measurable image: `Ψ '' E = {x | Ψ (P x) = x} ∩ P ⁻¹' E`, `P` is the adjoint of `ι`, the first set is closed, **no need** for Lusin–Souslin.
  (c) Summing and then taking limit as `ε ↓ 0` (in the `μ s < ∞` case, the limit is taken directly in `ℝ≥0∞`; generally, `s` uses ball exhaustion + monotone convergence).

Mathlib's `MeasureTheory/Function/Jacobian.lean` includes only change of variables in equal dimensions and lacks a codimension area formula;
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, although applicable across different dimensions, provides in `A n = f' y` the `y` which only guarantees membership in `s`, not in the piece, so a spherical covering decomposition was independently constructed in this round.

### 2. Divergence and Rank-One Trace (New Module `Analysis/Divergence.lean`)

`divergence F x = tr (DF x)` Moved from WIP to `Analysis/` (same namespace, unchanged declaration name, all consumers automatically remain available). Added `Analysis.trace_smulRight` (`tr (w ↦ φ w • v) = φ v`, via `dualTensorHom` / `contractLeft`) and `Analysis.divergence_smul_const` (`div (η • v) = ⟪∇η, v⟫`, `v` constant vector).

### 3. C2 is reduced from C1 (not an independent proof)

Take `F x = η x • v`: `div F = ⟪∇η, v⟫`, `⟪F x, ν x⟫ = ⟪v, η x • ν x⟫`, and use `integral_inner` at the ends.
Swap with the inner product (volume side uses `∇η` continuous compact support, boundary side uses the already proven `integrableOn_smul_outwardNormal`), then apply `ext_inner_left` to remove `v`. The mathematical scope remains unchanged: any finite-dimensional real inner product space, current `SmoothDomain` definition, compactly supported `C¹` test functions, existing `surfaceMeasure` and `outwardNormal`, without additional boundedness or stronger smoothness assumptions.
This reduction direction is one-way (C1 ⇒ C2), and does not allow mutual cyclic use of the two formulas.

## C1 Still missing specific mathematical lemmas

1. **Graph representation of the boundary**: The defining function `φ` of `SmoothDomain`, with `∇φ(x₀) ≠ 0`, must provide a locally `C^∞`
   `g : e^⊥ → ℝ`, the boundary is locally equal to `g` for the graph, the region is locally equal to the graph below, and
   `outwardNormal = (ι(-∇g) + e)/√(1+‖∇g‖²)`. Barrier: Mathlib's
   `HasStrictFDerivAt.implicitFunctionOfComplemented` Only provides strict differentiability **at a point**,
   No `C¹` on a neighborhood; the area formula requires `ContDiff ℝ 1 g`. A feasible route is through
   `ContDiffAt.to_localInverse` (Inverse Function Theorem preserves `C^k`) takes `Φ x = (P x, φ x)` to a local inverse,
   This round is not yet realized.
2. **Local Gauss–Green on a subgraph**: via `V ≃ₗᵢ WithLp 2 (H × ℝ)` (`LinearIsometryEquiv.measurePreserving`)
   Do Fubini with `WithLp.volume_preserving_ofLp`, normal component by fundamental theorem of calculus, tangential component needs to be integrated
   variable-upper-limit integral `y ↦ ∫_{-∞}^{g y} F_i` differentiation (Leibniz rule) followed by full integration yields zero. This round has not been implemented.
3. **Smooth partition of unity**: a finite smooth partition of unity on a compact support (which can be derived from
   (`exists_contDiff_tsupport_subset` manual assembly), used to glue together local identities and cancel out the derivative terms of the decomposition function.
   This round is not yet realized.

Evaluated alternative routes and reasons for rejection: The divergence theorem in Mathlib only covers boxes and cannot be directly applied to arbitrary smooth regions;
shear diffeomorphisms that flatten the region require the Piola identity (the cofactor matrix having row-wise zero divergence), which in Lean is no cheaper than the original route;
using Minkowski content or coarea to bypass the area formula introduces the same unproven assumptions.

## Module Organization

Add two generic modules without `sorry` under `Analysis/`: `AreaFormula.lean` and `Divergence.lean`.
Dependency direction remains acyclic: `KLS/Geometry/SurfaceMeasure` → `Analysis/LevelSet` → `Analysis/AreaFormula`;
`Analysis/Divergence` is independent of the first three; `KLS/WIP/AnalyticPrerequisites` imports `Analysis/Divergence` and `Analysis/LevelSet`, and continues to import `mollifiedIndicator` with `KLS/WIP/RelativePerimeter`.
Unfinished Gauss–Green, coarea, Sard remain in WIP. No alias compatibility, no duplicate proofs, no forward declarations.
The official entry point and 24 certificates do not import these modules.

## Counting

WIP direct hole reduced from 21 to 20: `RelativePerimeter` 3 (unchanged), `AnalyticPrerequisites` 5 → 4,
`CheegerInfimum` 8 (unchanged), `Energy/WIP/Cheeger` 5 (unchanged).
After `AnalyticPrerequisites` exits `divergence`, a total of 12 obligations remain, 8 of which have been filled with proofs, among which 6 lack transitive `sorryAx`;
`ae_forall_fderiv_ne_zero`, `setIntegral_gradient_eq_integral_smul_outwardNormal`, and `gradient_mollifiedIndicator_eq` have three filled proofs still dependently transitive on `sorryAx`.
"The filled proofs" and "transitive without sorryAx" must be stated separately.

## Verification

- **Direct axiom checks**: `Analysis.hausdorffMeasure_image_graphLinear`, `hausdorffMeasure_image_graphMap`, `hausdorffNormalized_image_graphMap`, `exists_approximating_partition`, `trace_smulRight`, `divergence_smul_const`; the transitive axioms of `propext / Classical.choice / Quot.sound` are only those. C1, C2, and `gradient_mollifiedIndicator_eq` contain `sorryAx` (as in the above table).
- **Independent client**: `build/audit/AreaFormulaAudit.lean` (ignored directory, `lake env lean` is directly elaborated, without entering `lake build`, replaying sets, or certification closure). All six client theorems are derived, not restated: the measure of a flat hyperplane slice equals the measure of the parameter set; the measure of an inclined hyperplane slice is exactly `√(1+‖a‖²)` times; the zero-dimensional point case; the unbounded case of the parameter set taking `univ`; direct computation of the formula for codimension one `surfaceMeasure` (normalized and perimeter chain consistency verified); rank-one divergence identity. All six transitive axioms have only the standard three. The previous `PerimeterInterfaceAudit.lean` still passes.
- **Strict mode**: `Analysis/AreaFormula.lean`, `Analysis/Divergence.lean`, and two audit clients exit 0 under `lake env lean -DwarningAsError=true`.
- **WIP with holes**: four files are re-elaborated in normal mode, exit 0, diagnosis exactly matches expected 3 / 4 / 8 / 5 item `declaration uses sorry`, with no other warnings or errors. **This is not a strict mode pass.**
- Complete default `lake build`, and run `python3 research/verify.py` from the repository root; the verification receipt points to `build/verification/latest.json`, matching the final source code snapshot.

Evidence of trust in fixed-version third-party compiled dependencies does not imply independent rebuilding of Mathlib, remote CI, or Blueprint formatting passes.
Audit scripts and logs remain in the ignored `build/`. This round does not commit or push as required by the owner.
