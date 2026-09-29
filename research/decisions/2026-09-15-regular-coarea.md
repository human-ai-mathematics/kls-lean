# Regular open domain C¹ weighted coarea (L9)

2026-09-15. Complete proof of the two conjunction components of L9 in this round. Not commit, not push, not migrate out WIP hole, not alter historical decisions.
Start HEAD `2965b32bc79bdb24921c633df12102450eaedcc4`; start verification receipt
`build/verification/20260915T082341.547238Z/report.json` is passed, full snapshot item-by-item consistent:
430 entries, SHA256 `d9ffd66ef3308d3469af51177aff4ca5a3adabbe2a8e20fb370fb6a36df26289`,
182 replayed modules. All 20 `build/audit` file hashes bound by the preceding round’s evidence also match.

## Exact Results

`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`, located at
`formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean`:

```lean
IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
MeasurableSet S → S ⊆ O → Measurable g →
AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) volume ∧
(∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
  ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V)
```

The space is assumed to be a finite-dimensional real inner product space equipped with its Borel measurable structure. Implementation omits derivable `CompleteSpace V`;
Independent client `RegularCoareaAudit.target` retains all user instance parameters and verbatim reproduces the full goal.
It matches exactly the text of L9 in the original `WeightedCoareaRouteStatements`, excluding whitespace, and is accompanied by actual proof.
No additional global C¹/Lipschitz, boundedness, finite volume, integrability, connectivity, non-zero dimension, or SFinite assumptions are introduced.
Mathlib `gradient` and repository normalization `surfaceMeasure` remain unchanged; neither existing Lean files nor signatures have been modified.

## Proof path and implementation choice of dimension-preserving change of variables

1. `Analysis/LocalInverse.lean` Depends only on Mathlib: `exists_contDiffOn_localInverse` for any specified
   Construct a local homeomorphism within an open domain, with forward and backward directions being C¹ over their respective entire open domains. Restrict using `restrContDiff` to both directions
   An open set of C¹, not merely asserting that the inverse function is differentiable at the center.
2. `Analysis/RegularChart.lean` Keep joint parameter `(y,t)`. `exists_regularChart` for
   `Φ(x) = P x + u(x)e` By the inverse function theorem, `levelChartHeight(y,t)` are the normal coordinates of a local inverse;
   `levelChart_inverse` proves both that the inverse is the graph point and that `u(graph point) = t`, for every parameter in the joint open domain.
3. Volume change uses **equivalent fiber-wise paths**, without introducing a new n-dimensional determinant identity: already has
   `measurePreserving_splitHomeomorph` under the linear isometric isomorphism of `WithLp 2 (H × ℝ)`, strict proof
   The inner product-induced orthogonal decomposition preserves volume; then on each vertical real fiber, use Mathlib
   `lintegral_image_eq_lintegral_abs_deriv_mul`. The theorem itself is user-suggested
   the one-dimensional specialization of `lintegral_image_eq_lintegral_abs_det_fderiv_mul`. The new module depending only on Mathlib
   `Analysis/FiberIntegral.lean` uses Tonelli to assemble vertical changes of variables on arbitrary Borel pieces, and prove
   `continuous_deriv_snd`, explicitly provides the measurability of the Jacobian with respect to the joint parameters.
4. `abs_deriv_mul_norm_gradient` proof
   `|∂t ψ| * ‖∇u‖ = sqrt(1 + ‖∇y ψ‖²)`. The chain rule gives
   `(∂t ψ) * ⟪∇u,e⟫ = 1`, provided in the horizontal direction
   `∇u = ⟪∇u,e⟫ • (ι(-∇y ψ)+e)`. Use absolute values to allow arbitrary derivative signs.
   The ENNReal version only converts the product of non-negative real numbers, then combines it using the associative law by multiplying by `g`; it does not divide by weights.
   No finite value subtraction, no elimination of `⊤`. Zero weight, `0 * ⊤`, infinite volume, and infinite cross-section retain their original meanings.
5. Use the L8 module of joint height on the parameter ball with `exists_contDiff_one_eqOn_ball` for global C¹
   Representation, apply the already proven global weighted graph area formula within this ball. Here, no assumption is made about the height being defined over the entire original open domain.
   Extensible; equal only on smaller internal balls. The image of any Borel parameter slice proves equality with each level's image.
   `setLIntegral_coarea_graph_family` obtain local coarea.
6. Perform the same internal local representation treatment on the original `u`. `exists_regular_coarea_neighborhood` yields the result
   Return the original function and original gradient, and package `hausdorffNormalized` using the dimension formula of the orthogonal complement as
   `surfaceMeasure`. Second countability takes countable open cover; `disjointed` constructs disjoint Borel pieces; both sides
   Concatenate `lintegral_iUnion` and `lintegral_tsum`.
7. Measurability is proved independently first in `KLS/Geometry/OpenSliceMeasurable.lean`.
   On each interior ball, take a global C¹ representative, obtain a Lipschitz constant on a compact closed ball,
   apply L5 piecewise, then sum countably. **Do not add L5's global continuity assumption to L9**.
   This measurability component also holds without the regular-point hypothesis. Tonelli is used only for volume;
   no SFinite instance is installed for the ambient `surfaceMeasure`.

No use of L10, Sard, WIP, Whitney extension, or the current goal itself as premises.
`ImplicitGraph.lean`, `GraphIntegral.lean` and all existing Lean files are preserved verbatim.

## Verification and Evidence

Five new modules passed strict compilation. The new modules contain 16 theorems and 2 definitions.
`build/audit/RegularCoareaAudit.lean` Strictly compiled passing: complete L9; infinite weights; infinite on empty set
  Weights on both sides are zero; a regular domain in zero dimension must be empty and a complete L9 instance; when `u = id` and `S = ℝ`, the actual values on both sides are
  `⊤`; each real affine linear section in the two-dimensional orthogonal decomposition is `⊤`;
  `jump x = if 0 < x then x else 1` at the complete infinite-weight instance of `(0,∞)`, and independently proved
  `jump` Discontinuous, explicitly excludes misinterpretation relying on global C¹.
* All 29 new statements and client statement axioms output contain only `propext`, `Classical.choice`,
  `Quot.sound`, no `sorryAx`. New module imports of closure have no WIP, CriticalSlice, or Sard modules.
* The user-specified 15 existing client instances were all strictly rerun successfully, including their respective `preserved_*` named arguments
  Check; three WIP files compiled successfully one by one, direct proof hole 2/3/5, total 10.
* The default `lake build` and root directory `python3 research/verify.py` are the final verification steps.
  This round of machine evidence is `research/explorations/2026-09-15-regular-coarea.json`, which precedes the final
  Write verification and finally hashed acknowledgment. Final `build/verification/latest.json` and final source code
  Snapshot exact equality check, save `build/audit/l9-final-snapshot.json`. `build/audit` is ignored,
  Hence, its client and logs are separately hashed by the current evidence JSON; final verification follows item-by-item inspection.

## Exact Incomplete Boundary

This round only completes L9. L11 (general C¹ coarea), L12 (Lipschitz coarea), L6/L6a/L7 Whitney
C¹ extension and exact piecewise remain unproven. Two original equations
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is still a direct proof hole, not migrated out.
Sharp `C^(finrank)` `Analysis.sard` remains a direct hole without downstream consumers; sharpness of the Eilenberg constant,
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`
And the equality of two Cheeger constants has not been proven. Certification is still 24, the perimeter infrastructure is still missing,
No extension of Blueprint leanok or certification scope.
