# 2D Non-flat Sheaves and the Plane Sard

2026-09-14, taking over the next statement from the type-checked section in [two-dimensional quantitative coverage](2026-09-14-planar-quadratic-cover.md) (the non-flat stratum of `build/audit/PlanarNonflatNextStatement.lean`). Initial verification receipt
`build/verification/latest.json` (`20260914T150543.429034Z`) is marked as passed, and the work area is recalculated to confirm byte-by-byte consistency.
HEAD remains `2965b32`, preserving all prior uncommitted and untracked results, without submission or push; historical decisions are not rewritten.

## Scope of completion

`Analysis/QuadraticCover.lean` Add a dimension covering lemma; new
`formalization/FunctionalInequalities/Analysis/PlanarSard.lean`, public results two:

```lean
theorem volume_image_eq_zero_of_quadratic_bound {A : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hA : Bornology.IsBounded A)
    (hC : ∀ x ∈ A, ∀ y ∈ A, |f y - f x| ≤ C * |y - x| ^ 2) :
    (volume : Measure ℝ) (f '' A) = 0

theorem volume_image_nonflat_eq_zero {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x ≠ 0}) = 0

theorem sard_plane {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0
```

Full names respectively `FunctionalInequalities.Analysis.volume_image_eq_zero_of_quadratic_bound`,[,]
`…volume_image_nonflat_eq_zero`, `…sard_plane`.Three depend only on
`propext / Classical.choice / Quot.sound`, no direct proof hole, no placeholder, no new axioms.

`sard_plane` is the **Sard's theorem for C² functions on the plane**: the set of critical values has measure zero, and the critical set does not assume measurability, does not assume boundedness, nor does it assume compactness. It is **not** `Analysis.sard`—the latter is a general statement for arbitrary finite-dimensional settings, still containing a direct proof hole in WIP.

## Actual Proof: No Need for Implicit Function Theorem

The one-dimensional covering lemma is a simplification of the two-dimensional version: with constant fixed, no need for ε-δ refinement, since the number of lattice points `O(r⁻¹)` already exceeds the interval length `O(r²)`, the total quantity `O(r) → 0`.

The key to non-trivial sheaves is to collapse them into one dimension, following this route (at `x₀` we only require `D²u x₀ ≠ 0`, no critical point required):

1. `T := fderiv ℝ (fderiv ℝ u) x₀ ≠ 0` (obtained from `iteratedFDeriv ℝ 2 u x₀ ≠ 0` via norm equality),
   Take `v₀, w` such that `(T v₀) w ≠ 0`, let `α := T.flip w`, then `α ≠ 0`.
2. **Linear algebra**: a non-zero functional `α` is non-zero on some basis vector `Pi.single i 1`; let `j := 1 - i`.
   If `|α v| ≤ (|α eᵢ|/4)‖v‖`, then `‖v‖ ≤ L |v j|`. Using `‖v‖ ≤ |v i| + |v j|` and
   solve directly from `α v = v i · α eᵢ + v j · α e_j`, with explicit constants.
3. **Mean value inequality with a linear principal part** `Convex.norm_image_sub_le_of_norm_fderiv_le'` used in
   `fderiv ℝ u` upper: inside the ball `‖D²u z − T‖ ≤ η` when, for any `x, y`,
   `‖Du y − Du x − T(y−x)‖ ≤ η‖y−x‖`. When both points are critical, it is `‖T(y−x)‖ ≤ η‖y−x‖`,
   Pair `w` to `|α(y−x)| ≤ η‖w‖‖y−x‖ ≤ ε‖y−x‖`. Thus, Step 2 gives
   `‖y − x‖ ≤ L |y j − x j|`: The critical set inside the ball is Lipschitz graph with respect to the `j`-th coordinate.
   This step replaces the implicit function theorem; the existing warehouse `Analysis/ImplicitGraph.lean` requires `C^∞` and the inner product structure,
   We don't need the `C¹` for the `Du`, so we didn't reuse it, nor did we build a new implicit function framework.
4. Quadratic estimate at critical points (twice convex comparison inequality, isomorphic to flat remainder but retaining true constant `M = ‖T‖+1`) gives
   `|u y − u x| ≤ M‖y−x‖²`. Combined with step 3: `|u y − u x| ≤ M L² |y j − x j|²`.
5. The Lipschitz graph has the property of *injectivity*: if two points have the same `j` coordinate, their distance is zero, hence they are equal. Thus
   t ↦ u (representative point) is well-defined on A := (· j) '' (critical set ∩ ball) and satisfies a quadratic one-dimensional bound,
   The one-dimensional covering lemma directly gives the image of zero measure inside the ball.
6. `TopologicalSpace.isOpen_iUnion_countable` (second-countable implies Lindelöf) takes a countable subcover of balls at each point,
   `measure_biUnion_null_iff` Synthesizing the full plane conclusion. Tightness is not required, so the public statement does not include `K`.

`sard_plane` is merely splitting the critical set according to `D²u x = 0` and `≠ 0`, applying the previous round's `volume_image_flat_univ_eq_zero` and this round's `volume_image_nonflat_eq_zero` to each half respectively.

## Verification and Axiomatic Boundaries

* Two modules `lake env lean -DwarningAsError=true` strictly pass, `lake build` target module passes.
* `build/audit/PlanarSardAudit.lean` strictly passes: 13 clients and 3 main theorems produce 16 axiom reports in total, all containing only standard three axioms. Among them,
  `recorded_nonflat_obligation` verbatim reproduces the compact set version of the non-flat obligation from the previous round;
  `nonflat_on_subset` explains that compactness is actually unnecessary, and holds for any (possibly non-measurable) subset;
  `constant_critical_univ` + `constant_sard` provide a nontrivial example where the critical set is the **entire plane** (source-side measure infinite) while the image remains zero measure;
  `square_critical` proves that the critical set of `x ↦ (x 0)²` is exactly the line `{x 0 = 0}`,
  `square_critical_line` shows that for any point on this line, the non-flat branch is nontrivial.
* `QuadraticCoverAudit`, `QuadraticRemainderAudit`, `SardLowDimAudit`, `AreaFormulaAudit`, `SuperlevelSardScope` all pass strictly again. `SuperlevelSardScope` again confirms general
  `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero`, `SmoothDomain.ae_exists_superlevel`
  **still inherit `sorryAx`**.
* Three WIP files are individually compiled in practice, diagnosis remains **3/3/5** direct proof holes, no other diagnostics. Total direct proof hole count remains **11**;
  certificate remains **24**; perimeter infrastructure remains **missing**.
* Default `lake build` passes (3393 jobs]). The final snapshot verification receipt for root directory `python3 research/verify.py` is
  `build/verification/latest.json`. Evidence hash is recorded at
  `research/explorations/2026-09-14-planar-sard-audit.json`, not claimed as formal certificate.
* This round **has no** expansion of any certificate or `leanok` scope.

## Explicitly incomplete work

`sard_plane` Covers only **two-dimensional, C², real-valued**. The rest is still incomplete:

* **General Sard** (`Analysis.sard`, finite-dimensional `C^n` in arbitrary dimension): still a direct hole in `WIP/AnalyticPrerequisites`,
  Two consumers still inherit `sorryAx`. The planar case cannot imply this.
* The next independent gap has been type-checked at `build/audit/HigherSardNextStatement.lean` (no proof, no placeholder axioms):
  (1) `n` Dimensional covering lemma——bounded `A ⊆ ℝⁿ`, uniformly `o(‖y−x‖ⁿ)` amplitude control implies the image has measure zero;
  (2) A uniform order-`n` remainder at fully flat points in a compact set (all derivatives from order 1 through `n` vanish).
  Only together do they yield the `n`-dimensional top layer; the intermediate layers still require finite-order implicit function charts and successive dimension reduction.
  And regularity is lost during dimension reduction, which is precisely the difficulty of Whitney–Morse–Sard.
* **Weighted coarea** and its level set measurability: two untouched direct proof holes.
* **Reverse Cheeger comparison** `smoothConstant_le_minkowskiConstant` equal to a constant: still unproven,
  Still transitively dependent on `sorryAx`; only `h_M ≤ h_S` one direction has been proven.

The entire chain is not closed.
