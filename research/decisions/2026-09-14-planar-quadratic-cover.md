# Quantitative planar covering and null images of the second-order flat layer

2026-09-14, proving the next lemma specified in the [uniform quadratic remainder record](2026-09-14-uniform-quadratic-remainder.md).
Initial verification receipt `build/verification/latest.json` (`20260913T190354.174769Z`) is passed, recalculation confirmed.
All 390 files and workspace are byte-for-byte identical, HEAD remains `2965b32`. Retain all prior uncommitted and untracked results,
no commit, no push, historical decisions remain unchanged.

## Scope of completion

Add `formalization/FunctionalInequalities/Analysis/QuadraticCover.lean`, three public results:

```lean
theorem volume_image_eq_zero_of_quadratic_oscillation
    {A : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℝ} (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ 2) :
    (volume : Measure ℝ) (f '' A) = 0

theorem volume_image_flat_eq_zero {u : (Fin 2 → ℝ) → ℝ} {K : Set (Fin 2 → ℝ)}
    (hu : ContDiff ℝ 2 u) (hK : IsCompact K) :
    (volume : Measure ℝ)
      (u '' {x ∈ K | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}) = 0
```

Then by countable exhaustion lift the compact set version to the entire plane:

```lean
theorem volume_image_flat_univ_eq_zero {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}) = 0
```

Fully named `FunctionalInequalities.Analysis.volume_image_eq_zero_of_quadratic_oscillation`,
`FunctionalInequalities.Analysis.volume_image_flat_eq_zero` and
`FunctionalInequalities.Analysis.volume_image_flat_univ_eq_zero`.
The three depend only on `propext / Classical.choice / Quot.sound`, with no direct proof holes, hidden placeholders, or new axioms.

* The assumptions of the covering lemma are identical to those proposed in the previous round: two-dimensional, `A` bounded, uniformly quadratic amplitude control.
  No additional assumptions of measurability, continuity, differentiability, or compactness are made; `f` is completely arbitrary outside `A`.
  `A = ∅` is automatically covered by the bounded constant of `R > 0` and the empty cover, without requiring branching.
* The flatness theorem is a **subset version**: the flatness condition is applied pointwise on `{x ∈ K | Du x = 0 ∧ D²u x = 0}`,
  without assuming the entire `K` is flat, nor that the subset is measurable.
* The full plane version uses `⋃ n : ℕ, closedBall 0 n` exhaustion, `Set.image_iUnion` and `measure_iUnion_null`,
  all assumptions of compactness, boundedness, and measurability vanish. This is the required shape for subsequent assembly, introducing no new tools.
* The new module only imports Mathlib's `Measure.Lebesgue.Basic`, `Normed.Group.Bounded` and this repository's
  `Analysis/TaylorRemainder`. No existing declarations are migrated, no existing public signatures are modified,
  no dependencies on Sard, KLS, or WIP are introduced, and no new cover or outer measure framework is established.

## Actual proof

Search Mathlib confirms: `Finset` finite additivity `measure_biUnion_finset_le` and
`Real.volume_Icc` are sufficient, no need for `OuterMeasure` custom constructions or Vitali-type lemmas;
the countable cover API is insufficient alone, as the grid count and `ε` balance must be quantitative.

Fix `ε > 0`, by assumption take `δ > 0`, let `r = min δ 1` (while ensuring `r ≤ δ` and `r ≤ 1`).

1. `Bornology.IsBounded.exists_pos_norm_le` Assign `A ⊆ {x | ‖x‖ ≤ R}` to `R > 0`.
   The Pi-norm of `Fin 2 → ℝ` is the component-wise supremum, so `norm_le_pi_norm` directly gives `|x i| ≤ R`.
2. Lattice index `q x = (⌊x 0 / r⌋, ⌊x 1 / r⌋) : ℤ × ℤ`.
   `Int.floor_le_floor`, `Int.floor_le_ceil`, and `Int.floor_neg` turn `|x i| ≤ R` into
   `q x ∈ S := Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M`, where `M = ⌈R / r⌉`.
   This is a finite index set, `Int.card_Icc` and `Finset.card_product` give `#S = (2M+1)²`.
3. Use `choose` to select a representative `g c` for each grid cell: whenever the cell contains a point of `A`, we have `g c ∈ A ∧ q (g c) = c`;
   Otherwise `g c` is an arbitrary value. Thus the covered interval `I c = Icc (f (g c) - ε r²) (f (g c) + ε r²)`
   Always a true interval, no need for `dite` branches, the measure is constantly `ENNReal.ofReal (2 ε r²)`.
4. Two points in the same grid cell: `Int.abs_sub_lt_one_of_floor_eq_floor` given `|a/r - b/r| < 1`,
   After division, we obtain `|a - b| < r`; `pi_norm_lt_iff` and `Fin.forall_fin_two` handle the two components
   Synthesize `‖y - g (q y)‖ < r ≤ δ`. Thus assume applicable, and `‖y - g (q y)‖² ≤ r²`,
   Get `f y ∈ I (q y)`. This is `f '' A ⊆ ⋃ c ∈ S, I c`, **without** any measurability.
5. `measure_mono`, `measure_biUnion_finset_le`, `Finset.sum_le_card_nsmul` given
   `volume (f '' A) ≤ #S • ofReal (2 ε r²) = ofReal ((2M+1)² · 2 ε r²)`.
   `Int.ceil_lt_add_one` Given `(2M+1) r ≤ 2R + 3r ≤ 2R + 3`, the upper bound is
   `ofReal (2 (2R+3)² ε)`, **independent of `r` and `δ`**.
6. `ENNReal.le_of_forall_pos_le_add` For each `η > 0` take `ε = η / (2 (2R+3)²)`, obtain zero.

The two-dimensional case is used in the product of steps 2 and 5: the lattice count is `O(r⁻²)`, each image interval length `O(ε r²)`,
the product then becomes independent of `r`. The three-dimensional case is similarly argued to give `O(ε r⁻¹)`, diverging, so this lemma cannot be directly extended to higher dimensions.

The flatness theorem merely connects `IsCompact.isBounded` to `Analysis.exists_uniform_quadratic_remainder` at this interface: the flat subset of a compact set is bounded, and the remainder theorem provides the required uniform quadratic amplitude control for this subset (the remainder theorem allows `y` outside of `K`, here only the weaker case of `y ∈ A` is used).

## Verification and Axiomatic Boundaries

* New module `lake env lean -DwarningAsError=true` passes strictly (`build/audit/quadratic-cover-module-strict.log`),
  `lake build FunctionalInequalities.Analysis.QuadraticCover` passes (2551 jobs).
* `build/audit/QuadraticCoverAudit.lean` passes strictly: 16 clients and 3 main theorems produce 19 axiom reports,
  all containing only standard three axioms. Covers empty set; singleton sets paired with completely arbitrary (possibly everywhere discontinuous) `f`; any bounded set paired with constant `f`, no measurable instances or assumptions present within client; flat layers of constant functions on compact sets; flat layer over the entire plane (without compactness, boundedness, or measurability assumptions); flat layers and closed ball instances of very non-constant cubic functions `x ↦ (x 0)³`.
  `cubic_ball_layer_proper` also provides non-flat points `![1,0]` and flat points `0` within closed balls,
  confirming that subset versions are neither empty nor the entire set, and cannot be replaced by "entire `K` is flat".
* `QuadraticRemainderAudit`, `SardLowDimAudit`, `AreaFormulaAudit`, `SuperlevelSardScope`
  are recompiled strictly. `SuperlevelSardScope` again confirms general `Analysis.sard`,
  `Analysis.ae_forall_fderiv_ne_zero`, `SmoothDomain.ae_exists_superlevel` inherit `sorryAx`.
* Three WIP files are individually compiled in ordinary mode, diagnostics remain **3/3/5** direct proof hole warnings, no other diagnostics.
  **Total direct proof holes remain 11**; certificate remains **24**, perimeter infrastructure remains **missing**.
* Default `lake build` passes (3393 jobs), log `build/audit/quadratic-cover-lake-build.log`;
  final snapshot verification receipt for root directory `python3 research/verify.py` is `build/verification/latest.json`.
  Independent client and log are located in the ignored `build/` directory, with evidence hashes recorded in
  `research/explorations/2026-09-14-quadratic-cover-audit.json`, not claimed as formal certificates.
* This round has **no** expansion of any certificate or `leanok` scope. General Sard, weighted coarea, their measurability, reverse Cheeger comparison, and constant equality remain unproven. Local verification does not equal remote CI.

## Explicitly incomplete work

This round only completes the **two-dimensional second-order flat layer**. The following has still not been completed:

* **2D non-flat stratum**: The image of `{x ∈ K | Du x = 0 ∧ D²u x ≠ 0}` has zero measure.
  `build/audit/PlanarNonflatNextStatement.lean` only checks this proposition type, with no proof assertion, no placeholder axioms.
  This stratum requires applying the implicit function theorem to some first-order partial derivative to obtain `C¹` curve, then reducing to one dimension via Sard;
  the current repository lacks the local chart and dimension-reduction gluing.
* **General Sard** (`Analysis.sard`): Still a direct proof hole in `WIP/AnalyticPrerequisites`.
  Even if both 2D sheaves are completed, additional requirements include σ-compact exhaustion, arbitrary finite-dimensional, higher-order flat remainder and higher-order coverings, and handling regularity loss during higher-order stratified descent. The current result is **not** general Sard, nor does it alter its status.
* **Weighted coarea** and measurability of its level sets: Two untouched direct proof holes.
* **Reverse Cheeger comparison** `smoothConstant_le_minkowskiConstant` equal to constant: still unproven, still depends on `sorryAx`; only one direction, `h_M ≤ h_S`, has been proven.

The entire chain is not closed, and no closure is implied by the result of this round.
