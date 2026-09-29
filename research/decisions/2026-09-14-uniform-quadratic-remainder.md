# Uniform second-order remainder for a flat point

2026-09-14, following the precise next lemma proposed in [low-dimensional Sard](2026-09-14-low-dimensional-sard.md).
Starting verification receipt `build/verification/20260913T184752.039532Z/report.json` is passed, recalculate confirmation
All 387 files match HEAD exactly. HEAD remains `2965b32`; all previously uncommitted and untracked results are preserved,
No commit, no push, history is not rewritten.

## Scope of completion

Add `formalization/FunctionalInequalities/Analysis/TaylorRemainder.lean`, the only public result being:

```lean
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_uniform_quadratic_remainder {u : V → ℝ} {K : Set V}
    (hu : ContDiff ℝ 2 u) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, fderiv ℝ u x = 0 → iteratedFDeriv ℝ 2 u x = 0 →
        ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ 2
```

Complete name is `FunctionalInequalities.Analysis.exists_uniform_quadratic_remainder`.
Relies only on `propext / Classical.choice / Quot.sound`. Has no direct proof hole, hidden placeholder, or new axioms.

* The same δ is uniformly valid for all x in K satisfying the two zero derivative conditions.
* It is not required that every point in K be flat; y may lie outside K, including the case y = x.
* Empty K, zero-dimensional, and constant functions are all covered, with regularity exactly C², no extension to C³ or C∞.
* After searching existing APIs, it was found that finite-dimensionality is actually unnecessary, so a version for any real normed space is provided.
  Completeness, inner product, domain measure, or additional measurability are not required. This covers the originally intended finite-dimensional case without narrowing the scope of applicability.
* The new module only imports Mathlib's ContDiff.Comp, MeanValue, and HeineCantor; there are no local imports,
  no imports of Sard, KLS, or WIP, and no migration of any existing declarations.
  It is a general analytic estimate, not incorporating the Sard-specific name in theorems or establishing any additional framework.

## Actual Proofs and Reusable API

The previous round proposed integral-type Taylor as a feasible approach; this round's search found that the required non-sharp constant estimate can be achieved more concisely using two `Convex.norm_image_sub_le_of_norm_fderiv_le`, thus no redundant implementation of the Taylor integral formula was carried out.

1. `hu.continuous_iteratedFDeriv` The second-order derivative is continuous.
   `IsCompact.uniformContinuousAt_of_continuousAt` Uniform control for external neighbors on compact sets;
   This is stronger than `UniformContinuousOn`, which only controls pairs of points inside K.
   By `Metric.mem_uniformity_dist` we obtain δ such that for x∈K and ‖z−x‖<δ, the difference of second derivatives is less than ε.
2. Fix a flat base point x. Since D²u(x)=0, obtain ‖D²u(z)‖≤ε on `ball x δ`.
   `norm_iteratedFDeriv_one` and `norm_iteratedFDeriv_fderiv` directly replace this norm with
   `‖fderiv ℝ (fderiv ℝ u) z‖`; no introduction of Hessian, inner product, or determinant framework.
3. C² function u is differentiable, Du is differentiable. On this convex ball, for the first time use the mean value inequality, and use Du(x)=0,
   We have ‖Du(z)‖ ≤ ε‖z - x‖.
4. For the segment [x,y], `norm_sub_le_of_mem_segment` gives ‖z-x‖≤‖y-x‖<δ.
   Hence on this segment ∥Du(z)∥ ≤ ε∥y−x∥. The second mean inequality yields
   |u(y)-u(x)|≤ε‖y-x‖·‖y-x‖.

This is a consistent o(r²) amplitude estimate, **without** asserting that any high-dimensional image set has zero measure.

## Verification and Axiomatic Boundaries

* The new module passes `lake env lean -DwarningAsError=true` strictly, and independent module builds pass.
* `build/audit/QuadraticRemainderAudit.lean` passes strictly: 9 clients and the main theorem share 10 axioms, all containing only standard three axioms. Covers general spaces without finite-dimensional/completed/inner-product/metric instances, empty K, arbitrary functions in zero-dimensional spaces, constant functions; second-order derivatives at zero for cubic functions are zero; for K={0,1] with non-flat points, and separately proves x=1 is non-flat; for K={0}, actual value is y=δ/2≠0, and outside compact sets the required estimates hold.
* `SardLowDimAudit`, `AreaFormulaAudit`, and `SuperlevelSardScope` are recompiled strictly. The first two have no sorryAx; the last one separately confirms that general `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero`, and `SmoothDomain.ae_exists_superlevel` still inherit sorryAx.
* Each of the three WIP files compiles successfully in regular mode; diagnostics remain 3/3/5 direct proof hole warnings, with no other diagnostics. **Total direct proof holes remain 11**; the certificate remains **24**, and perimeter infrastructure remains **missing**.
* Default `lake build` has passed (3393 jobs), log is `build/audit/quadratic-lake-build.log`; the final snapshot verification receipt for root directory `python3 research/verify.py` is `build/verification/latest.json`.
Independent clients and logs in ignored build directories, with evidence hashes recorded at `research/explorations/2026-09-14-quadratic-remainder-audit.json`, do not claim formal certificates.
* The general Sard and all WIP source code remain unchanged in this round. General Sard, weighted coarea, its measurability, reverse Cheeger comparison, and constant equality remain unproven. Local verification receipt does not equal remote CI.

## Next independent gap: two-dimensional quantitative coverage leads to zero measure

Suggest the next step is to establish the pure covering lemma (not yet proven; name to be determined at the time of search):
For `A : Set (Fin 2 → ℝ)`, any `f : (Fin 2 → ℝ) → ℝ`, assume A is bounded, and furthermore

```lean
∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ 2
```

Then `(volume : Measure ℝ) (f '' A) = 0`.
No measurability of A or its image is required, nor is continuity or differentiability of f outside A required. The dimension two is not optional.
`build/audit/QuadraticCoverNextStatement.lean` only checks the type of this statement, with no proof assertions or placeholder axioms.

One can place A inside a box, dividing it into O(r⁻²) small squares; for each square intersecting A, select a representative point from A, and use the above estimate to cover its image within an interval of length O(εr²), then take ε→0 to control the outer measure.
The quantitative finite cover, interval image cover, and outer measure estimate still need to be proven; a countable cover API alone is insufficient.
The current result allows sending a subset of second-order flat points in a compact set K through this interface, without first assuming measurability of the subset.

Even after completing this covering lemma, it only handles two-dimensional second-order flat sheaves; non-flat sheaves still require finite-order implicit function charts, local dimension reduction, and countable gluing. Higher dimensions require higher-order flat remainder terms and covering, along with handling the regularity loss during higher-order stratified descent. This does not equate to general Sard having already established it.
