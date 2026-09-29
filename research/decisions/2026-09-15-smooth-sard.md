# C^∞ Sard theorem proof completed

2026-09-15, taking over from the same day's [route survey](2026-09-15-smooth-sard-route.md) and
[three puzzle pieces](2026-09-15-smooth-sard-ingredients.md), completing the remaining L1, L3′, L6, L7.
Initial verification receipt `build/verification/latest.json` (`20260914T165021.064313Z`) is passed,
recomputing to confirm byte-by-byte consistency in the work area. HEAD remains `2965b32`, not commit, not pushed.

## Scope of completion

`Analysis/SmoothSard.lean` Now we prove the **Sard's theorem for C^∞ real-valued functions**:

```lean
theorem sard_smooth_pi : ∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0

theorem sard_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0

theorem ae_forall_fderiv_ne_zero_of_contDiff_top {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x, u x = t → fderiv ℝ u x ≠ 0
```

In any finite-dimensional real normed space of any dimension, the critical set is not assumed to be measurable. Together with the current addition of
`exists_contDiff_eventuallyEq`, it only depends on `propext / Classical.choice / Quot.sound`,
with no direct proof hole, no placeholder, and no new axioms.

## Second Correction to the Path: Using Extension Instead of Open Set Version of the Top Layer

The L3 investigation record is "relaxing the top-level zero measure to an open set `ContDiffOn`". This round uses a cheaper alternative instead:

```lean
theorem exists_contDiff_eventuallyEq (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hz : z ∈ O) :
    ∃ g, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 z] f
```

(bump multiply, support lies within the open set, smoothness is a local property: equal to `χ • f` on `O`,
On `tsupport χ` it equals `0`, and two open sets cover the entire space.

With it, in the induction step we replace the local `γ` with a **global** `C^∞` map `γ'`,
so the induction hypothesis can maintain a **global** form, and the top level directly uses the previously proven
`Analysis.volume_image_flat_pow_univ_eq_zero`, **completely without** the open set version of the remainder or the top level.
L3 therefore does not do this and is no longer needed.

## Actual proof

Induction on dimension. Dimension `0`: the flatness condition is hollow, the critical set is contained in the top layer, directly eliminated by the already proven top layer conclusion.

Dimension `m+1`: Split the critical set into top and `j ∈ Finset.Ico 1 (m+1)` intermediate layers using `critical_subset_layers`.
The top layer uses `volume_image_flat_pow_univ_eq_zero` (where `ContDiff.of_le` reduces `∞` to `m+1`).
For each intermediate layer `j`, at each point `x₀`:

1. `exists_flat_direction` constructed scalar `C^∞` function from `iteratedFDeriv (j+1) u x₀ ≠ 0`
   `w x := iteratedFDeriv j u x m`, it is zero over the entire layer and `fderiv w x₀ ≠ 0`.
2. `exists_local_graph` gives a continuous parameterized map `p`, a parameter open set `O`, and a `γ` on `O` with respect to `C^∞`,
   The zeros near `x₀` satisfy `γ (p x) = x`.
3. `exists_contDiff_eventuallyEq` Replace `γ` with the global `C^∞` `γ'`, identical near `p x₀`.
4. `u ∘ γ'` global `C^∞`, lying on `Fin m → ℝ`, can be handled by **inductive hypothesis**.
   A point in the stratum is `u`'s critical point, the chain rule gives `p x` is a critical point of `u ∘ γ'`,
   Moreover, `u x = (u ∘ γ') (p x)`. Thus, the image of this layer in a neighborhood of the point lies in a set of measure zero.
5. `TopologicalSpace.isOpen_iUnion_countable` (Lindelöf) takes a countable subcover,
   Use `measure_biUnion_null_iff` to assemble the strata.

The finite-dimensional version is passed from the coordinate version via `ContinuousLinearEquiv.ofFinrankEq` and the chain rule;
a.e. the version copies the `ae_iff` argument from `ae_forall_fderiv_ne_zero` in WIP.

## What hole did it fill—and which one did it not fill?

The `build/audit/SmoothSardAudit.lean` `superlevel_without_sard` **verbatim reproofs** the statement in `SmoothDomain.ae_exists_superlevel` (`filter_upwards` new a.e. theorem, together with hole-free's previously established `SmoothDomain.ofSuperlevel` and `frontier_superlevel_subset`),
whose axioms report **lack `sorryAx`**; yet within the same log, `SmoothDomain.ae_exists_superlevel` itself
still carries `sorryAx`. Reading the two reports side by side constitutes evidence: this consumer's gap has been mathematically sealed.

**But this round made no changes to any WIP files**, so:

* `SmoothDomain.ae_exists_superlevel` still inherits `sorryAx`;
* The direct proof hole remains **11** (3/3/5), certification remains **24**,
  perimeter infrastructure remains **missing**;
* The sharp `Analysis.sard` (`C^(finrank)`) statement and direct proof hole identity remain **completely unchanged**,
  `Analysis.ae_forall_fderiv_ne_zero` still inherits `sorryAx`.
  The `n = 4, j = 2` obstacle identified in the route record **is not touched**—this round proves the smooth case, not the sharp version.

Routing WIP to the new theorem (thus genuinely reducing `sorryAx` and hole count) is a **standalone decision for the next round**,
involving whether `ae_exists_superlevel` is also migrated out of WIP, which is not decided in this round.

## Verification

* New module `lake env lean -DwarningAsError=true` passes strictly; `lake build` target module passes (2706 jobs).
* `build/audit/SmoothSardAudit.lean` Strictly passed: 12 standard axiom reports + 1 intentionally retained
  `sorryAx` report (WIP of `ae_exists_superlevel`, for comparison). Covers zero-dimensional, three-dimensional,
  Interface for any finite-dimensional non-measurable instance, constant functions (critical set is the entire space, source measure infinite while image has zero measure).
* `SmoothSardIngredientsAudit`, `QuadraticRemainderAudit`, `QuadraticCoverAudit`,
  `PlanarSardAudit`, `HigherSardAudit`, `SardLowDimAudit`, `AreaFormulaAudit`,
  `SuperlevelSardScope` Re-verify entirely strictly, **without modification**.
* Three WIP files are compiled individually, and the diagnosis remains **3/3/5** direct proof holes.
* Default `lake build` passes (3393 jobs). Verification receipt for the final snapshot of root directory `python3 research/verify.py` is
  `build/verification/latest.json`. Evidence hash recorded at
  `research/explorations/2026-09-15-smooth-sard.json`.
This round does not expand any certifications or `leanok` scope.

## Still not completed

* **WIP Reconnection**: Make `ae_exists_superlevel` truly without `sorryAx` (decided in the next round).
* **Sharp `C^n` Sard**: `Analysis.sard` remains a direct proof hole.
* **Weighted coarea** `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  and measurability of its level sets: two untouched direct proof holes, this is the main obstruction to the reverse Cheeger comparison.
* **Reverse comparison** `smoothConstant_le_minkowskiConstant` equal to a constant: still unproven.

The entire chain is not closed.
