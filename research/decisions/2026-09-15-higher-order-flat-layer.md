# n-th order uniform remainder and n-dimensional top layer

2026-09-15, following the two next obligations typechecked in [planar Sard](2026-09-14-planar-sard.md)
(`build/audit/HigherSardNextStatement.lean`). Start verification receipt
`build/verification/latest.json` (`20260914T154144.742286Z`) is passed, recompute verification of the workspace byte-by-byte consistency.
HEAD remains `2965b32`, retains all previous uncommit and untraced achievements, does not commit, does not push, historical decisions are not rewritten.

## Scope of completion

Prove verbatim the two obligations from the previous record, and synthesize `n` at the topmost level.

`Analysis/TaylorRemainder.lean` Generalization to arbitrary order:

```lean
theorem exists_uniform_pow_remainder {u : V → ℝ} {K : Set V} {n : ℕ}
    (hu : ContDiff ℝ (n : ℕ) u) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, (∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0) →
        ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ n
```

`Analysis/QuadraticCover.lean` Generalization to arbitrary dimension:

```lean
theorem volume_image_eq_zero_of_oscillation_pow {n : ℕ} {A : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ n) :
    (volume : Measure ℝ) (f '' A) = 0

theorem volume_image_flat_pow_eq_zero {n : ℕ} {u : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hu : ContDiff ℝ (n : ℕ) u) (hK : IsCompact K) :
    (volume : Measure ℝ)
      (u '' {x ∈ K | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}) = 0

theorem volume_image_flat_pow_univ_eq_zero {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ (n : ℕ) u) :
    (volume : Measure ℝ)
      (u '' {x | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}) = 0
```

The four new results depend only on `propext / Classical.choice / Quot.sound`, with no direct holes, placeholders, or new axioms.

**No new duplicate proofs**: The original `exists_uniform_quadratic_remainder` and `volume_image_eq_zero_of_quadratic_oscillation` are now derived as corollaries of the general result, with both statements unchanged word for word (line-by-line diff verified), and all existing client code passes without modification. The order of the remainder term is raised from 2 to any `n`, and the second-order proof is entirely replaced by induction, with no net increase in module line count.

## Actual proof

**Remainder (induction by order)**. Zeroth order is uniform continuity on a compact set (external neighbor version of `IsCompact.uniformContinuousAt_of_continuousAt`). Inductive step: `fderiv ℝ f` is `C^m`, its `x`-th derivative at `1..m` is zero if and only if `f` has zero `x`-th derivative at `2..m+1` (`norm_iteratedFDeriv_fderiv`), and since the first derivative of `f` is zero, it gives `fderiv ℝ f x = 0`; thus, inside the ball, `‖fderiv ℝ f z‖ ≤ ε‖z-x‖^m`, the convex inequality in a single convex set raises the power to `m+1`.
The constant is **non-degenerate**, always the same `ε`.

Induction is carried out on vector-valued functions (`fderiv f` taking values in `V →L[ℝ] F`), so the internal auxiliary lemma places `W` and `F` in the same universe; the public real-valued theorem first reduces `n = m+1` one order down to `fderiv ℝ u : V → (V →L[ℝ] ℝ)` before applying the auxiliary lemma, thus there is **no** universe restriction, holding for any real normed space, without requiring finite-dimensionality, completeness, inner product, or measure.

**Covering (generalization to dimension)**. The lattice index changes from `ℤ × ℤ` to `Fin n → ℤ`, the index set is denoted by `Fintype.piFinset`, and the cardinality `(2M+1)^n` is given by `Fintype.card_piFinset` and `Finset.prod_const`.
The total quantity `(2M+1)^n · 2εr^n = 2ε((2M+1)r)^n ≤ 2ε(2R+3)^n` is independent of `r`.
The dimension and exponent must be equal: the number of lattices `O(r⁻ⁿ)` cancels exactly with the length of the image interval `O(εrⁿ)`.
The two-dimensional version is now an instance of `n = 2`; `Fin.forall_fin_two` is replaced by `congrFun`, and the proof becomes shorter.
`n = 0` (with empty product cardinality 1) and `n = 1` are both covered by the same proof, with no branching.

## Verification and Axiomatic Boundaries

* Three modules `lake env lean -DwarningAsError=true` pass strictly.
* `build/audit/HigherSardAudit.lean` passes strictly: 13 clients and 5 main theorems produce 17 axiom reports in total, all containing only standard three axioms. Among them, `recorded_pow_cover` and `recorded_pow_remainder` verbatim reproduce the two obligations from the previous round; `pow_remainder_general` uses remainder terms on any normed space of arbitrary dimension; `dim_zero` (flatness condition void, set being the whole space), `dim_one`, and `dim_three` cover both low and non-low dimensions; `flat_two_unchanged` confirms the two-level planar interface remains unchanged; `constant_fully_flat` + `constant_sard_pow` provide instances of any-dimensional constant functions being flat everywhere, and flat sets being the **entire `ℝⁿ`** while the image remains zero-measure and nontrivial.
* `QuadraticRemainderAudit`, `QuadraticCoverAudit`, `PlanarSardAudit`, `SardLowDimAudit`, `AreaFormulaAudit`, and `SuperlevelSardScope` all pass strictly again, **with no modifications made**. `SuperlevelSardScope` reconfirms general `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero`, and `SmoothDomain.ae_exists_superlevel` **still inherit `sorryAx`**.
* Each of the three WIP files is compiled in practice, with diagnostics still showing **3/3/5** direct proof holes, no other diagnostics. Total direct proof hole count remains **11**; certificate count remains **24**; perimeter infrastructure remains **missing**.
* Default `lake build` passes (3393 jobs). The final snapshot verification receipt for the root directory `python3 research/verify.py` is `build/verification/latest.json`. Evidence hash is recorded at `research/explorations/2026-09-15-higher-order-flat-layer.json`, without claiming formal certification.
* This round **does not** expand any certificate or `leanok` scope.

## Explicitly incomplete work

This round only completes the `n`-dimensional **top layer** (fully flat layer). The following have all not yet been completed:

* **Intermediate layers**: `1 ≤ j < n` when
  The image of \{x ∈ K | 1..j-th derivatives are all zero ∧ (j+1)-th derivative ≠ 0\} has zero measure.
  Type-checked at `build/audit/IntermediateLayerNextStatement.lean` (no proof, no placeholder axioms).
  The planar case `n = 2, j = 1` has been proven, using the fact that the critical set is locally the graph of a Lipschitz function in some coordinate.
  A elementary path "collapsing down to one dimension". In general `n` the same estimate only yields a Lipschitz graph in `(n-1)` dimensions,
  Still need to do `(n-1)`-dimensional Sard on this diagram and handle the drop in regularity after restriction—
  This is exactly the difficulty of Whitney–Morse–Sard, and this round has not touched it.
* **`n` Dimension Sard** (stacking all layers): As in Section 2 of the same document, unproven.
* **General Sard** (`Analysis.sard`, any finite-dimensional normed space): is still
  The direct proof hole of `WIP/AnalyticPrerequisites`, two consumers still inherit `sorryAx`.
  Even after the `n`-dimensional `Fin n → ℝ` version is completed, it still requires the linear isomorphism action to transit between finite-dimensional spaces and `Fin n → ℝ`.
* **Weighted coarea** and its level set measurability: two untouched direct proof holes.
* **Reverse Cheeger comparison** `smoothConstant_le_minkowskiConstant` equal to a constant: still unproven,
  Still transitively dependent on `sorryAx`; only `h_M ≤ h_S` one direction has been proven.

The entire chain is not closed.
